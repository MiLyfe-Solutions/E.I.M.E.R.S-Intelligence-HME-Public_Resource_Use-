import V185TrunkScan23Chunk0245

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1454635 : List Nat := [1, 1, 1, 1, 2, 1, 3, 2, 3, 8]
def baseStart_1454635 : Nat := 118140960795 + 1454635 * 2 ^ 59
def prefixEnd_1454635 : Nat := 4983230072969 + 3 ^ 40 * 1454635 * 2
def baseEnd_1454635 : Nat := 248975643951007155857587

theorem tailTrace_1454635 : CollatzResearch.WordTrace tailWord_1454635 prefixEnd_1454635 248975643951007155857587 := by
  unfold tailWord_1454635
  simp only [CollatzResearch.WordTrace]
  refine ⟨53054897085113301724437359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35369931390075534482958239 53054897085113301724437359)
  ·
    refine ⟨79582345627669952586656039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53054897085113301724437359 79582345627669952586656039)
    ·
      refine ⟨119373518441504928879984059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79582345627669952586656039 119373518441504928879984059)
      ·
        refine ⟨179060277662257393319976089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119373518441504928879984059 179060277662257393319976089)
        ·
          refine ⟨134295208246693044989982067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179060277662257393319976089 134295208246693044989982067)
          ·
            refine ⟨201442812370039567484973101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134295208246693044989982067 201442812370039567484973101)
            ·
              refine ⟨75541054638764837806864913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 201442812370039567484973101 75541054638764837806864913)
              ·
                refine ⟨56655790979073628355148685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 75541054638764837806864913 56655790979073628355148685)
                ·
                  refine ⟨21245921617152610633180757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56655790979073628355148685 21245921617152610633180757)
                  ·
                    refine ⟨248975643951007155857587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21245921617152610633180757 248975643951007155857587)
                    ·
                      rfl

theorem cell23_1454635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 2, 3, 8].length) (baseStart_1454635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454635 prefixEnd_1454635 := by exact prefixLift 1454635
  have htrace : WordTrace (prefixWord ++ tailWord_1454635) baseStart_1454635 baseEnd_1454635 := by
    simpa [prefixWord, tailWord_1454635, baseEnd_1454635] using wordTrace_append hprefix tailTrace_1454635
  have hstable : (prefixWord ++ tailWord_1454635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454635).length < 2 ^ (prefixWord ++ tailWord_1454635).sum := by decide
  have hdescent : baseEnd_1454635 < baseStart_1454635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454642 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4]
def baseStart_1454642 : Nat := 118140960795 + 1454642 * 2 ^ 59
def prefixEnd_1454642 : Nat := 4983230072969 + 3 ^ 40 * 1454642 * 2
def baseEnd_1454642 : Nat := 746930526217602940185229

theorem tailTrace_1454642 : CollatzResearch.WordTrace tailWord_1454642 prefixEnd_1454642 746930526217602940185229 := by
  unfold tailWord_1454642
  simp only [CollatzResearch.WordTrace]
  refine ⟨13263788099021985479985545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35370101597391961279961453 13263788099021985479985545)
  ·
    refine ⟨9947841074266489109989159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13263788099021985479985545 9947841074266489109989159)
    ·
      refine ⟨14921761611399733664983739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9947841074266489109989159 14921761611399733664983739)
      ·
        refine ⟨22382642417099600497475609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14921761611399733664983739 22382642417099600497475609)
        ·
          refine ⟨16786981812824700373106707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22382642417099600497475609 16786981812824700373106707)
          ·
            refine ⟨25180472719237050559660061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16786981812824700373106707 25180472719237050559660061)
            ·
              refine ⟨9442677269713893959872523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25180472719237050559660061 9442677269713893959872523)
              ·
                refine ⟨14164015904570840939808785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9442677269713893959872523 14164015904570840939808785)
                ·
                  refine ⟨10623011928428130704856589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14164015904570840939808785 10623011928428130704856589)
                  ·
                    refine ⟨3983629473160549014321221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10623011928428130704856589 3983629473160549014321221)
                    ·
                      refine ⟨746930526217602940185229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3983629473160549014321221 746930526217602940185229)
                      ·
                        rfl

theorem cell23_1454642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_1454642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454642 prefixEnd_1454642 := by exact prefixLift 1454642
  have htrace : WordTrace (prefixWord ++ tailWord_1454642) baseStart_1454642 baseEnd_1454642 := by
    simpa [prefixWord, tailWord_1454642, baseEnd_1454642] using wordTrace_append hprefix tailTrace_1454642
  have hstable : (prefixWord ++ tailWord_1454642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454642).length < 2 ^ (prefixWord ++ tailWord_1454642).sum := by decide
  have hdescent : baseEnd_1454642 < baseStart_1454642 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454652 : List Nat := [2, 2, 2, 2, 3, 1, 1, 1, 1, 8]
def baseStart_1454652 : Nat := 118140960795 + 1454652 * 2 ^ 59
def prefixEnd_1454652 : Nat := 4983230072969 + 3 ^ 40 * 1454652 * 2
def baseEnd_1454652 : Nat := 248978553674715967020061

theorem tailTrace_1454652 : CollatzResearch.WordTrace tailWord_1454652 prefixEnd_1454652 248978553674715967020061 := by
  unfold tailWord_1454652
  simp only [CollatzResearch.WordTrace]
  refine ⟨26527758563025856813903105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35370344750701142418537473 26527758563025856813903105)
  ·
    refine ⟨19895818922269392610427329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26527758563025856813903105 19895818922269392610427329)
    ·
      refine ⟨14921864191702044457820497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19895818922269392610427329 14921864191702044457820497)
      ·
        refine ⟨11191398143776533343365373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14921864191702044457820497 11191398143776533343365373)
        ·
          refine ⟨4196774303916200003762015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11191398143776533343365373 4196774303916200003762015)
          ·
            refine ⟨6295161455874300005643023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4196774303916200003762015 6295161455874300005643023)
            ·
              refine ⟨9442742183811450008464535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6295161455874300005643023 9442742183811450008464535)
              ·
                refine ⟨14164113275717175012696803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9442742183811450008464535 14164113275717175012696803)
                ·
                  refine ⟨21246169913575762519045205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14164113275717175012696803 21246169913575762519045205)
                  ·
                    refine ⟨248978553674715967020061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21246169913575762519045205 248978553674715967020061)
                    ·
                      rfl

theorem cell23_1454652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 1, 1, 8].length) (baseStart_1454652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454652 prefixEnd_1454652 := by exact prefixLift 1454652
  have htrace : WordTrace (prefixWord ++ tailWord_1454652) baseStart_1454652 baseEnd_1454652 := by
    simpa [prefixWord, tailWord_1454652, baseEnd_1454652] using wordTrace_append hprefix tailTrace_1454652
  have hstable : (prefixWord ++ tailWord_1454652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454652).length < 2 ^ (prefixWord ++ tailWord_1454652).sum := by decide
  have hdescent : baseEnd_1454652 < baseStart_1454652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454676 : List Nat := [2, 4, 1, 1, 1, 3, 2, 2, 1, 4, 2]
def baseStart_1454676 : Nat := 118140960795 + 1454676 * 2 ^ 59
def prefixEnd_1454676 : Nat := 4983230072969 + 3 ^ 40 * 1454676 * 2
def baseEnd_1454676 : Nat := 746947984559855807160073

theorem tailTrace_1454676 : CollatzResearch.WordTrace tailWord_1454676 prefixEnd_1454676 746947984559855807160073 := by
  unfold tailWord_1454676
  simp only [CollatzResearch.WordTrace]
  refine ⟨26528196238982382863339941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35370928318643177151119921 26528196238982382863339941)
  ·
    refine ⟨4974036794809196786876239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26528196238982382863339941 4974036794809196786876239)
    ·
      refine ⟨7461055192213795180314359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4974036794809196786876239 7461055192213795180314359)
      ·
        refine ⟨11191582788320692770471539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7461055192213795180314359 11191582788320692770471539)
        ·
          refine ⟨16787374182481039155707309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11191582788320692770471539 16787374182481039155707309)
          ·
            refine ⟨6295265318430389683390241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16787374182481039155707309 6295265318430389683390241)
            ·
              refine ⟨4721448988822792262542681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6295265318430389683390241 4721448988822792262542681)
              ·
                refine ⟨3541086741617094196907011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4721448988822792262542681 3541086741617094196907011)
                ·
                  refine ⟨5311630112425641295360517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3541086741617094196907011 5311630112425641295360517)
                  ·
                    refine ⟨995930646079807742880097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5311630112425641295360517 995930646079807742880097)
                    ·
                      refine ⟨746947984559855807160073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 995930646079807742880097 746947984559855807160073)
                      ·
                        rfl

theorem cell23_1454676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 1, 4, 2].length) (baseStart_1454676 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454676 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454676 prefixEnd_1454676 := by exact prefixLift 1454676
  have htrace : WordTrace (prefixWord ++ tailWord_1454676) baseStart_1454676 baseEnd_1454676 := by
    simpa [prefixWord, tailWord_1454676, baseEnd_1454676] using wordTrace_append hprefix tailTrace_1454676
  have hstable : (prefixWord ++ tailWord_1454676).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454676).length < 2 ^ (prefixWord ++ tailWord_1454676).sum := by decide
  have hdescent : baseEnd_1454676 < baseStart_1454676 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454693 : List Nat := [1, 3, 1, 3, 4, 1, 1, 1, 4, 2, 2]
def baseStart_1454693 : Nat := 118140960795 + 1454693 * 2 ^ 59
def prefixEnd_1454693 : Nat := 4983230072969 + 3 ^ 40 * 1454693 * 2
def baseEnd_1454693 : Nat := 746956713730982240647495

theorem tailTrace_1454693 : CollatzResearch.WordTrace tailWord_1454693 prefixEnd_1454693 746956713730982240647495 := by
  unfold tailWord_1454693
  simp only [CollatzResearch.WordTrace]
  refine ⟨53057012518903177630048733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35371341679268785086699155 53057012518903177630048733)
  ·
    refine ⟨19896379694588691611268275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53057012518903177630048733 19896379694588691611268275)
    ·
      refine ⟨29844569541883037416902413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19896379694588691611268275 29844569541883037416902413)
      ·
        refine ⟨11191713578206139031338405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29844569541883037416902413 11191713578206139031338405)
        ·
          refine ⟨2098446295913651068375951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11191713578206139031338405 2098446295913651068375951)
          ·
            refine ⟨3147669443870476602563927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2098446295913651068375951 3147669443870476602563927)
            ·
              refine ⟨4721504165805714903845891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3147669443870476602563927 4721504165805714903845891)
              ·
                refine ⟨7082256248708572355768837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4721504165805714903845891 7082256248708572355768837)
                ·
                  refine ⟨1327923046632857316706657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7082256248708572355768837 1327923046632857316706657)
                  ·
                    refine ⟨995942284974642987529993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1327923046632857316706657 995942284974642987529993)
                    ·
                      refine ⟨746956713730982240647495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 995942284974642987529993 746956713730982240647495)
                      ·
                        rfl

theorem cell23_1454693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_1454693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454693 prefixEnd_1454693 := by exact prefixLift 1454693
  have htrace : WordTrace (prefixWord ++ tailWord_1454693) baseStart_1454693 baseEnd_1454693 := by
    simpa [prefixWord, tailWord_1454693, baseEnd_1454693] using wordTrace_append hprefix tailTrace_1454693
  have hstable : (prefixWord ++ tailWord_1454693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454693).length < 2 ^ (prefixWord ++ tailWord_1454693).sum := by decide
  have hdescent : baseEnd_1454693 < baseStart_1454693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454710 : List Nat := [5, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2]
def baseStart_1454710 : Nat := 118140960795 + 1454710 * 2 ^ 59
def prefixEnd_1454710 : Nat := 4983230072969 + 3 ^ 40 * 1454710 * 2
def baseEnd_1454710 : Nat := 746965442902108674134917

theorem tailTrace_1454710 : CollatzResearch.WordTrace tailWord_1454710 prefixEnd_1454710 746965442902108674134917 := by
  unfold tailWord_1454710
  simp only [CollatzResearch.WordTrace]
  refine ⟨3316102034990099345838599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35371755039894393022278389 3316102034990099345838599)
  ·
    refine ⟨4974153052485149018757899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3316102034990099345838599 4974153052485149018757899)
    ·
      refine ⟨7461229578727723528136849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4974153052485149018757899 7461229578727723528136849)
      ·
        refine ⟨5595922184045792646102637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7461229578727723528136849 5595922184045792646102637)
        ·
          refine ⟨2098470819017172242288489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5595922184045792646102637 2098470819017172242288489)
          ·
            refine ⟨1573853114262879181716367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2098470819017172242288489 1573853114262879181716367)
            ·
              refine ⟨2360779671394318772574551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1573853114262879181716367 2360779671394318772574551)
              ·
                refine ⟨3541169507091478158861827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2360779671394318772574551 3541169507091478158861827)
                ·
                  refine ⟨5311754260637217238292741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3541169507091478158861827 5311754260637217238292741)
                  ·
                    refine ⟨995953923869478232179889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5311754260637217238292741 995953923869478232179889)
                    ·
                      refine ⟨746965442902108674134917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 995953923869478232179889 746965442902108674134917)
                      ·
                        rfl

theorem cell23_1454710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_1454710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454710 prefixEnd_1454710 := by exact prefixLift 1454710
  have htrace : WordTrace (prefixWord ++ tailWord_1454710) baseStart_1454710 baseEnd_1454710 := by
    simpa [prefixWord, tailWord_1454710, baseEnd_1454710] using wordTrace_append hprefix tailTrace_1454710
  have hstable : (prefixWord ++ tailWord_1454710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454710).length < 2 ^ (prefixWord ++ tailWord_1454710).sum := by decide
  have hdescent : baseEnd_1454710 < baseStart_1454710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454712 : List Nat := [2, 1, 2, 1, 1, 1, 2, 4, 4, 5]
def baseStart_1454712 : Nat := 118140960795 + 1454712 * 2 ^ 59
def prefixEnd_1454712 : Nat := 4983230072969 + 3 ^ 40 * 1454712 * 2
def baseEnd_1454712 : Nat := 248988823287805888769969

theorem tailTrace_1454712 : CollatzResearch.WordTrace tailWord_1454712 prefixEnd_1454712 248988823287805888769969 := by
  unfold tailWord_1454712
  simp only [CollatzResearch.WordTrace]
  refine ⟨26528852752917171937495195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35371803670556229249993593 26528852752917171937495195)
  ·
    refine ⟨39793279129375757906242793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26528852752917171937495195 39793279129375757906242793)
    ·
      refine ⟨29844959347031818429682095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39793279129375757906242793 29844959347031818429682095)
      ·
        refine ⟨44767439020547727644523143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29844959347031818429682095 44767439020547727644523143)
        ·
          refine ⟨67151158530821591466784715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44767439020547727644523143 67151158530821591466784715)
          ·
            refine ⟨100726737796232387200177073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67151158530821591466784715 100726737796232387200177073)
            ·
              refine ⟨75545053347174290400132805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100726737796232387200177073 75545053347174290400132805)
              ·
                refine ⟨14164697502595179450024901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75545053347174290400132805 14164697502595179450024901)
                ·
                  refine ⟨2655880781736596146879669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14164697502595179450024901 2655880781736596146879669)
                  ·
                    refine ⟨248988823287805888769969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2655880781736596146879669 248988823287805888769969)
                    ·
                      rfl

theorem cell23_1454712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 4, 4, 5].length) (baseStart_1454712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454712 prefixEnd_1454712 := by exact prefixLift 1454712
  have htrace : WordTrace (prefixWord ++ tailWord_1454712) baseStart_1454712 baseEnd_1454712 := by
    simpa [prefixWord, tailWord_1454712, baseEnd_1454712] using wordTrace_append hprefix tailTrace_1454712
  have hstable : (prefixWord ++ tailWord_1454712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454712).length < 2 ^ (prefixWord ++ tailWord_1454712).sum := by decide
  have hdescent : baseEnd_1454712 < baseStart_1454712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454749 : List Nat := [1, 4, 2, 1, 1, 1, 3, 1, 4, 1, 4]
def baseStart_1454749 : Nat := 118140960795 + 1454749 * 2 ^ 59
def prefixEnd_1454749 : Nat := 4983230072969 + 3 ^ 40 * 1454749 * 2
def baseEnd_1454749 : Nat := 746985468647634021547237

theorem tailTrace_1454749 : CollatzResearch.WordTrace tailWord_1454749 prefixEnd_1454749 746985468647634021547237 := by
  unfold tailWord_1454749
  simp only [CollatzResearch.WordTrace]
  refine ⟨53059055006700299194087301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35372703337800199462724867 53059055006700299194087301)
  ·
    refine ⟨9948572813756306098891369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53059055006700299194087301 9948572813756306098891369)
    ·
      refine ⟨7461429610317229574168527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9948572813756306098891369 7461429610317229574168527)
      ·
        refine ⟨11192144415475844361252791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7461429610317229574168527 11192144415475844361252791)
        ·
          refine ⟨16788216623213766541879187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11192144415475844361252791 16788216623213766541879187)
          ·
            refine ⟨25182324934820649812818781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16788216623213766541879187 25182324934820649812818781)
            ·
              refine ⟨9443371850557743679807043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25182324934820649812818781 9443371850557743679807043)
              ·
                refine ⟨14165057775836615519710565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9443371850557743679807043 14165057775836615519710565)
                ·
                  refine ⟨2655948332969365409945731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14165057775836615519710565 2655948332969365409945731)
                  ·
                    refine ⟨3983922499454048114918597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2655948332969365409945731 3983922499454048114918597)
                    ·
                      refine ⟨746985468647634021547237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3983922499454048114918597 746985468647634021547237)
                      ·
                        rfl

theorem cell23_1454749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 1, 4, 1, 4].length) (baseStart_1454749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454749 prefixEnd_1454749 := by exact prefixLift 1454749
  have htrace : WordTrace (prefixWord ++ tailWord_1454749) baseStart_1454749 baseEnd_1454749 := by
    simpa [prefixWord, tailWord_1454749, baseEnd_1454749] using wordTrace_append hprefix tailTrace_1454749
  have hstable : (prefixWord ++ tailWord_1454749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454749).length < 2 ^ (prefixWord ++ tailWord_1454749).sum := by decide
  have hdescent : baseEnd_1454749 < baseStart_1454749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454816 : List Nat := [2, 1, 1, 3, 1, 2, 1, 5, 3, 1, 3]
def baseStart_1454816 : Nat := 118140960795 + 1454816 * 2 ^ 59
def prefixEnd_1454816 : Nat := 4983230072969 + 3 ^ 40 * 1454816 * 2
def baseEnd_1454816 : Nat := 747019871851485259409429

theorem tailTrace_1454816 : CollatzResearch.WordTrace tailWord_1454816 prefixEnd_1454816 747019871851485259409429 := by
  unfold tailWord_1454816
  simp only [CollatzResearch.WordTrace]
  refine ⟨26530749348728784818388151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35374332464971713091184201 26530749348728784818388151)
  ·
    refine ⟨39796124023093177227582227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26530749348728784818388151 39796124023093177227582227)
    ·
      refine ⟨59694186034639765841373341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39796124023093177227582227 59694186034639765841373341)
      ·
        refine ⟨22385319762989912190515003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59694186034639765841373341 22385319762989912190515003)
        ·
          refine ⟨33577979644484868285772505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22385319762989912190515003 33577979644484868285772505)
          ·
            refine ⟨25183484733363651214329379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33577979644484868285772505 25183484733363651214329379)
            ·
              refine ⟨37775227100045476821494069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25183484733363651214329379 37775227100045476821494069)
              ·
                refine ⟨3541427540629263452015069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37775227100045476821494069 3541427540629263452015069)
                ·
                  refine ⟨1328035327735973794505651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3541427540629263452015069 1328035327735973794505651)
                  ·
                    refine ⟨1992052991603960691758477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1328035327735973794505651 1992052991603960691758477)
                    ·
                      refine ⟨747019871851485259409429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1992052991603960691758477 747019871851485259409429)
                      ·
                        rfl

theorem cell23_1454816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 1, 5, 3, 1, 3].length) (baseStart_1454816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454816 prefixEnd_1454816 := by exact prefixLift 1454816
  have htrace : WordTrace (prefixWord ++ tailWord_1454816) baseStart_1454816 baseEnd_1454816 := by
    simpa [prefixWord, tailWord_1454816, baseEnd_1454816] using wordTrace_append hprefix tailTrace_1454816
  have hstable : (prefixWord ++ tailWord_1454816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454816).length < 2 ^ (prefixWord ++ tailWord_1454816).sum := by decide
  have hdescent : baseEnd_1454816 < baseStart_1454816 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454826 : List Nat := [3, 1, 3, 1, 1, 1, 1, 4, 1, 5, 2]
def baseStart_1454826 : Nat := 118140960795 + 1454826 * 2 ^ 59
def prefixEnd_1454826 : Nat := 4983230072969 + 3 ^ 40 * 1454826 * 2
def baseEnd_1454826 : Nat := 747025006658030220284383

theorem tailTrace_1454826 : CollatzResearch.WordTrace tailWord_1454826 prefixEnd_1454826 747025006658030220284383 := by
  unfold tailWord_1454826
  simp only [CollatzResearch.WordTrace]
  refine ⟨13265465856855335336160083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35374575618280894229760221 13265465856855335336160083)
  ·
    refine ⟨19898198785283003004240125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13265465856855335336160083 19898198785283003004240125)
    ·
      refine ⟨7461824544481126126590047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19898198785283003004240125 7461824544481126126590047)
      ·
        refine ⟨11192736816721689189885071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7461824544481126126590047 11192736816721689189885071)
        ·
          refine ⟨16789105225082533784827607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11192736816721689189885071 16789105225082533784827607)
          ·
            refine ⟨25183657837623800677241411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16789105225082533784827607 25183657837623800677241411)
            ·
              refine ⟨37775486756435701015862117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25183657837623800677241411 37775486756435701015862117)
              ·
                refine ⟨7082903766831693940474147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37775486756435701015862117 7082903766831693940474147)
                ·
                  refine ⟨10624355650247540910711221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7082903766831693940474147 10624355650247540910711221)
                  ·
                    refine ⟨996033342210706960379177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10624355650247540910711221 996033342210706960379177)
                    ·
                      refine ⟨747025006658030220284383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 996033342210706960379177 747025006658030220284383)
                      ·
                        rfl

theorem cell23_1454826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 4, 1, 5, 2].length) (baseStart_1454826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454826 prefixEnd_1454826 := by exact prefixLift 1454826
  have htrace : WordTrace (prefixWord ++ tailWord_1454826) baseStart_1454826 baseEnd_1454826 := by
    simpa [prefixWord, tailWord_1454826, baseEnd_1454826] using wordTrace_append hprefix tailTrace_1454826
  have hstable : (prefixWord ++ tailWord_1454826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454826).length < 2 ^ (prefixWord ++ tailWord_1454826).sum := by decide
  have hdescent : baseEnd_1454826 < baseStart_1454826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454829 : List Nat := [1, 5, 1, 2, 1, 1, 1, 1, 2, 1, 7]
def baseStart_1454829 : Nat := 118140960795 + 1454829 * 2 ^ 59
def prefixEnd_1454829 : Nat := 4983230072969 + 3 ^ 40 * 1454829 * 2
def baseEnd_1454829 : Nat := 747026547099993708546869

theorem tailTrace_1454829 : CollatzResearch.WordTrace tailWord_1454829 prefixEnd_1454829 747026547099993708546869 := by
  unfold tailWord_1454829
  simp only [CollatzResearch.WordTrace]
  refine ⟨53061972846410472856999541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35374648564273648571333027 53061972846410472856999541)
  ·
    refine ⟨4974559954350981830343707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53061972846410472856999541 4974559954350981830343707)
    ·
      refine ⟨7461839931526472745515561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4974559954350981830343707 7461839931526472745515561)
      ·
        refine ⟨5596379948644854559136671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7461839931526472745515561 5596379948644854559136671)
        ·
          refine ⟨8394569922967281838705007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5596379948644854559136671 8394569922967281838705007)
          ·
            refine ⟨12591854884450922758057511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8394569922967281838705007 12591854884450922758057511)
            ·
              refine ⟨18887782326676384137086267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12591854884450922758057511 18887782326676384137086267)
              ·
                refine ⟨28331673490014576205629401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18887782326676384137086267 28331673490014576205629401)
                ·
                  refine ⟨21248755117510932154222051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28331673490014576205629401 21248755117510932154222051)
                  ·
                    refine ⟨31873132676266398231333077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21248755117510932154222051 31873132676266398231333077)
                    ·
                      refine ⟨747026547099993708546869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31873132676266398231333077 747026547099993708546869)
                      ·
                        rfl

theorem cell23_1454829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 1, 1, 2, 1, 7].length) (baseStart_1454829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454829 prefixEnd_1454829 := by exact prefixLift 1454829
  have htrace : WordTrace (prefixWord ++ tailWord_1454829) baseStart_1454829 baseEnd_1454829 := by
    simpa [prefixWord, tailWord_1454829, baseEnd_1454829] using wordTrace_append hprefix tailTrace_1454829
  have hstable : (prefixWord ++ tailWord_1454829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454829).length < 2 ^ (prefixWord ++ tailWord_1454829).sum := by decide
  have hdescent : baseEnd_1454829 < baseStart_1454829 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454859 : List Nat := [1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 5]
def baseStart_1454859 : Nat := 118140960795 + 1454859 * 2 ^ 59
def prefixEnd_1454859 : Nat := 4983230072969 + 3 ^ 40 * 1454859 * 2
def baseEnd_1454859 : Nat := 747041951519628591171731

theorem tailTrace_1454859 : CollatzResearch.WordTrace tailWord_1454859 prefixEnd_1454859 747041951519628591171731 := by
  unfold tailWord_1454859
  simp only [CollatzResearch.WordTrace]
  refine ⟨53063067036301787980591631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35375378024201191987061087 53063067036301787980591631)
  ·
    refine ⟨79594600554452681970887447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53063067036301787980591631 79594600554452681970887447)
    ·
      refine ⟨119391900831679022956331171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79594600554452681970887447 119391900831679022956331171)
      ·
        refine ⟨179087851247518534434496757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119391900831679022956331171 179087851247518534434496757)
        ·
          refine ⟨16789486054454862603234071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 179087851247518534434496757 16789486054454862603234071)
          ·
            refine ⟨25184229081682293904851107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16789486054454862603234071 25184229081682293904851107)
            ·
              refine ⟨37776343622523440857276661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25184229081682293904851107 37776343622523440857276661)
              ·
                refine ⟨3541532214611572580369687, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37776343622523440857276661 3541532214611572580369687)
                ·
                  refine ⟨5312298321917358870554531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3541532214611572580369687 5312298321917358870554531)
                  ·
                    refine ⟨7968447482876038305831797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5312298321917358870554531 7968447482876038305831797)
                    ·
                      refine ⟨747041951519628591171731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7968447482876038305831797 747041951519628591171731)
                      ·
                        rfl

theorem cell23_1454859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 1, 1, 5].length) (baseStart_1454859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454859 prefixEnd_1454859 := by exact prefixLift 1454859
  have htrace : WordTrace (prefixWord ++ tailWord_1454859) baseStart_1454859 baseEnd_1454859 := by
    simpa [prefixWord, tailWord_1454859, baseEnd_1454859] using wordTrace_append hprefix tailTrace_1454859
  have hstable : (prefixWord ++ tailWord_1454859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454859).length < 2 ^ (prefixWord ++ tailWord_1454859).sum := by decide
  have hdescent : baseEnd_1454859 < baseStart_1454859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454869 : List Nat := [1, 3, 2, 1, 2, 2, 2, 2, 1, 1, 6]
def baseStart_1454869 : Nat := 118140960795 + 1454869 * 2 ^ 59
def prefixEnd_1454869 : Nat := 4983230072969 + 3 ^ 40 * 1454869 * 2
def baseEnd_1454869 : Nat := 747047086326173552046685

theorem tailTrace_1454869 : CollatzResearch.WordTrace tailWord_1454869 prefixEnd_1454869 747047086326173552046685 := by
  unfold tailWord_1454869
  simp only [CollatzResearch.WordTrace]
  refine ⟨53063431766265559688455661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35375621177510373125637107 53063431766265559688455661)
  ·
    refine ⟨19898786912349584883170873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53063431766265559688455661 19898786912349584883170873)
    ·
      refine ⟨14924090184262188662378155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19898786912349584883170873 14924090184262188662378155)
      ·
        refine ⟨22386135276393282993567233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14924090184262188662378155 22386135276393282993567233)
        ·
          refine ⟨16789601457294962245175425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22386135276393282993567233 16789601457294962245175425)
          ·
            refine ⟨12592201092971221683881569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16789601457294962245175425 12592201092971221683881569)
            ·
              refine ⟨9444150819728416262911177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12592201092971221683881569 9444150819728416262911177)
              ·
                refine ⟨7083113114796312197183383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9444150819728416262911177 7083113114796312197183383)
                ·
                  refine ⟨10624669672194468295775075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7083113114796312197183383 10624669672194468295775075)
                  ·
                    refine ⟨15937004508291702443662613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10624669672194468295775075 15937004508291702443662613)
                    ·
                      refine ⟨747047086326173552046685, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15937004508291702443662613 747047086326173552046685)
                      ·
                        rfl

theorem cell23_1454869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 1, 1, 6].length) (baseStart_1454869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454869 prefixEnd_1454869 := by exact prefixLift 1454869
  have htrace : WordTrace (prefixWord ++ tailWord_1454869) baseStart_1454869 baseEnd_1454869 := by
    simpa [prefixWord, tailWord_1454869, baseEnd_1454869] using wordTrace_append hprefix tailTrace_1454869
  have hstable : (prefixWord ++ tailWord_1454869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454869).length < 2 ^ (prefixWord ++ tailWord_1454869).sum := by decide
  have hdescent : baseEnd_1454869 < baseStart_1454869 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454876 : List Nat := [2, 2, 3, 1, 1, 4, 1, 2, 1, 1, 5]
def baseStart_1454876 : Nat := 118140960795 + 1454876 * 2 ^ 59
def prefixEnd_1454876 : Nat := 4983230072969 + 3 ^ 40 * 1454876 * 2
def baseEnd_1454876 : Nat := 747050680690755024659153

theorem tailTrace_1454876 : CollatzResearch.WordTrace tailWord_1454876 prefixEnd_1454876 747050680690755024659153 := by
  unfold tailWord_1454876
  simp only [CollatzResearch.WordTrace]
  refine ⟨26531843538620099941980241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35375791384826799922640321 26531843538620099941980241)
  ·
    refine ⟨19898882653965074956485181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26531843538620099941980241 19898882653965074956485181)
    ·
      refine ⟨7462080995236903108681943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19898882653965074956485181 7462080995236903108681943)
      ·
        refine ⟨11193121492855354663022915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7462080995236903108681943 11193121492855354663022915)
        ·
          refine ⟨16789682239283031994534373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11193121492855354663022915 16789682239283031994534373)
          ·
            refine ⟨3148065419865568498975195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16789682239283031994534373 3148065419865568498975195)
            ·
              refine ⟨4722098129798352748462793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3148065419865568498975195 4722098129798352748462793)
              ·
                refine ⟨3541573597348764561347095, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4722098129798352748462793 3541573597348764561347095)
                ·
                  refine ⟨5312360396023146842020643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3541573597348764561347095 5312360396023146842020643)
                  ·
                    refine ⟨7968540594034720263030965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5312360396023146842020643 7968540594034720263030965)
                    ·
                      refine ⟨747050680690755024659153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7968540594034720263030965 747050680690755024659153)
                      ·
                        rfl

theorem cell23_1454876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 1, 1, 5].length) (baseStart_1454876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454876 prefixEnd_1454876 := by exact prefixLift 1454876
  have htrace : WordTrace (prefixWord ++ tailWord_1454876) baseStart_1454876 baseEnd_1454876 := by
    simpa [prefixWord, tailWord_1454876, baseEnd_1454876] using wordTrace_append hprefix tailTrace_1454876
  have hstable : (prefixWord ++ tailWord_1454876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454876).length < 2 ^ (prefixWord ++ tailWord_1454876).sum := by decide
  have hdescent : baseEnd_1454876 < baseStart_1454876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454913 : List Nat := [1, 2, 5, 3, 1, 2, 9]
def baseStart_1454913 : Nat := 118140960795 + 1454913 * 2 ^ 59
def prefixEnd_1454913 : Nat := 4983230072969 + 3 ^ 40 * 1454913 * 2
def baseEnd_1454913 : Nat := 9223082462653967653043

theorem tailTrace_1454913 : CollatzResearch.WordTrace tailWord_1454913 prefixEnd_1454913 9223082462653967653043 := by
  unfold tailWord_1454913
  simp only [CollatzResearch.WordTrace]
  refine ⟨53065036578106155203057393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35376691052070770135371595 53065036578106155203057393)
  ·
    refine ⟨39798777433579616402293045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53065036578106155203057393 39798777433579616402293045)
    ·
      refine ⟨3731135384398089037714973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39798777433579616402293045 3731135384398089037714973)
      ·
        refine ⟨1399175769149283389143115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3731135384398089037714973 1399175769149283389143115)
        ·
          refine ⟨2098763653723925083714673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1399175769149283389143115 2098763653723925083714673)
          ·
            refine ⟨1574072740292943812786005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2098763653723925083714673 1574072740292943812786005)
            ·
              refine ⟨9223082462653967653043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1574072740292943812786005 9223082462653967653043)
              ·
                rfl

theorem cell23_1454913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 2, 9].length) (baseStart_1454913 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454913 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454913 prefixEnd_1454913 := by exact prefixLift 1454913
  have htrace : WordTrace (prefixWord ++ tailWord_1454913) baseStart_1454913 baseEnd_1454913 := by
    simpa [prefixWord, tailWord_1454913, baseEnd_1454913] using wordTrace_append hprefix tailTrace_1454913
  have hstable : (prefixWord ++ tailWord_1454913).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454913).length < 2 ^ (prefixWord ++ tailWord_1454913).sum := by decide
  have hdescent : baseEnd_1454913 < baseStart_1454913 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454919 : List Nat := [1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 5]
def baseStart_1454919 : Nat := 118140960795 + 1454919 * 2 ^ 59
def prefixEnd_1454919 : Nat := 4983230072969 + 3 ^ 40 * 1454919 * 2
def baseEnd_1454919 : Nat := 747072760358898356421455

theorem tailTrace_1454919 : CollatzResearch.WordTrace tailWord_1454919 prefixEnd_1454919 747072760358898356421455 := by
  unfold tailWord_1454919
  simp only [CollatzResearch.WordTrace]
  refine ⟨53065255416084418227775811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35376836944056278818517207 53065255416084418227775811)
  ·
    refine ⟨79597883124126627341663717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53065255416084418227775811 79597883124126627341663717)
    ·
      refine ⟨14924603085773742626561947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79597883124126627341663717 14924603085773742626561947)
      ·
        refine ⟨22386904628660613939842921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14924603085773742626561947 22386904628660613939842921)
        ·
          refine ⟨16790178471495460454882191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22386904628660613939842921 16790178471495460454882191)
          ·
            refine ⟨25185267707243190682323287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16790178471495460454882191 25185267707243190682323287)
            ·
              refine ⟨37777901560864786023484931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25185267707243190682323287 37777901560864786023484931)
              ·
                refine ⟨56666852341297179035227397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37777901560864786023484931 56666852341297179035227397)
                ·
                  refine ⟨10625034813993221069105137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56666852341297179035227397 10625034813993221069105137)
                  ·
                    refine ⟨7968776110494915801828853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10625034813993221069105137 7968776110494915801828853)
                    ·
                      refine ⟨747072760358898356421455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7968776110494915801828853 747072760358898356421455)
                      ·
                        rfl

theorem cell23_1454919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 1, 4, 2, 5].length) (baseStart_1454919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454919 prefixEnd_1454919 := by exact prefixLift 1454919
  have htrace : WordTrace (prefixWord ++ tailWord_1454919) baseStart_1454919 baseEnd_1454919 := by
    simpa [prefixWord, tailWord_1454919, baseEnd_1454919] using wordTrace_append hprefix tailTrace_1454919
  have hstable : (prefixWord ++ tailWord_1454919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454919).length < 2 ^ (prefixWord ++ tailWord_1454919).sum := by decide
  have hdescent : baseEnd_1454919 < baseStart_1454919 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454924 : List Nat := [2, 2, 1, 3, 3, 2, 3, 2, 1, 2, 2]
def baseStart_1454924 : Nat := 118140960795 + 1454924 * 2 ^ 59
def prefixEnd_1454924 : Nat := 4983230072969 + 3 ^ 40 * 1454924 * 2
def baseEnd_1454924 : Nat := 747075327762170836858933

theorem tailTrace_1454924 : CollatzResearch.WordTrace tailWord_1454924 prefixEnd_1454924 747075327762170836858933 := by
  unfold tailWord_1454924
  simp only [CollatzResearch.WordTrace]
  refine ⟨26532718890533152040853913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35376958520710869387805217 26532718890533152040853913)
  ·
    refine ⟨19899539167899864030640435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26532718890533152040853913 19899539167899864030640435)
    ·
      refine ⟨29849308751849796045960653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19899539167899864030640435 29849308751849796045960653)
      ·
        refine ⟨11193490781943673517235245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29849308751849796045960653 11193490781943673517235245)
        ·
          refine ⟨4197559043228877568963217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11193490781943673517235245 4197559043228877568963217)
          ·
            refine ⟨3148169282421658176722413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4197559043228877568963217 3148169282421658176722413)
            ·
              refine ⟨1180563480908121816270905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3148169282421658176722413 1180563480908121816270905)
              ·
                refine ⟨885422610681091362203179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1180563480908121816270905 885422610681091362203179)
                ·
                  refine ⟨1328133916021637043304769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 885422610681091362203179 1328133916021637043304769)
                  ·
                    refine ⟨996100437016227782478577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1328133916021637043304769 996100437016227782478577)
                    ·
                      refine ⟨747075327762170836858933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 996100437016227782478577 747075327762170836858933)
                      ·
                        rfl

theorem cell23_1454924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 2, 1, 2, 2].length) (baseStart_1454924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454924 prefixEnd_1454924 := by exact prefixLift 1454924
  have htrace : WordTrace (prefixWord ++ tailWord_1454924) baseStart_1454924 baseEnd_1454924 := by
    simpa [prefixWord, tailWord_1454924, baseEnd_1454924] using wordTrace_append hprefix tailTrace_1454924
  have hstable : (prefixWord ++ tailWord_1454924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454924).length < 2 ^ (prefixWord ++ tailWord_1454924).sum := by decide
  have hdescent : baseEnd_1454924 < baseStart_1454924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454933 : List Nat := [1, 3, 2, 2, 2, 1, 2, 2, 3, 3, 2]
def baseStart_1454933 : Nat := 118140960795 + 1454933 * 2 ^ 59
def prefixEnd_1454933 : Nat := 4983230072969 + 3 ^ 40 * 1454933 * 2
def baseEnd_1454933 : Nat := 747079949088061301646391

theorem tailTrace_1454933 : CollatzResearch.WordTrace tailWord_1454933 prefixEnd_1454933 747079949088061301646391 := by
  unfold tailWord_1454933
  simp only [CollatzResearch.WordTrace]
  refine ⟨53065766038033698618785453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35377177358689132412523635 53065766038033698618785453)
  ·
    refine ⟨19899662264262636982044545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53065766038033698618785453 19899662264262636982044545)
    ·
      refine ⟨14924746698196977736533409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19899662264262636982044545 14924746698196977736533409)
      ·
        refine ⟨11193560023647733302400057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14924746698196977736533409 11193560023647733302400057)
        ·
          refine ⟨8395170017735799976800043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11193560023647733302400057 8395170017735799976800043)
          ·
            refine ⟨12592755026603699965200065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8395170017735799976800043 12592755026603699965200065)
            ·
              refine ⟨9444566269952774973900049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12592755026603699965200065 9444566269952774973900049)
              ·
                refine ⟨7083424702464581230425037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9444566269952774973900049 7083424702464581230425037)
                ·
                  refine ⟨2656284263424217961409389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7083424702464581230425037 2656284263424217961409389)
                  ·
                    refine ⟨996106598784081735528521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2656284263424217961409389 996106598784081735528521)
                    ·
                      refine ⟨747079949088061301646391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 996106598784081735528521 747079949088061301646391)
                      ·
                        rfl

theorem cell23_1454933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 2, 3, 3, 2].length) (baseStart_1454933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454933 prefixEnd_1454933 := by exact prefixLift 1454933
  have htrace : WordTrace (prefixWord ++ tailWord_1454933) baseStart_1454933 baseEnd_1454933 := by
    simpa [prefixWord, tailWord_1454933, baseEnd_1454933] using wordTrace_append hprefix tailTrace_1454933
  have hstable : (prefixWord ++ tailWord_1454933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454933).length < 2 ^ (prefixWord ++ tailWord_1454933).sum := by decide
  have hdescent : baseEnd_1454933 < baseStart_1454933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454963 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 6, 2, 2]
def baseStart_1454963 : Nat := 118140960795 + 1454963 * 2 ^ 59
def prefixEnd_1454963 : Nat := 4983230072969 + 3 ^ 40 * 1454963 * 2
def baseEnd_1454963 : Nat := 747095353507696184271253

theorem tailTrace_1454963 : CollatzResearch.WordTrace tailWord_1454963 prefixEnd_1454963 747095353507696184271253 := by
  unfold tailWord_1454963
  simp only [CollatzResearch.WordTrace]
  refine ⟨53066860227925013742377543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35377906818616675828251695 53066860227925013742377543)
  ·
    refine ⟨79600290341887520613566315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53066860227925013742377543 79600290341887520613566315)
    ·
      refine ⟨119400435512831280920349473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79600290341887520613566315 119400435512831280920349473)
      ·
        refine ⟨89550326634623460690262105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119400435512831280920349473 89550326634623460690262105)
        ·
          refine ⟨67162744975967595517696579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89550326634623460690262105 67162744975967595517696579)
          ·
            refine ⟨100744117463951393276544869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67162744975967595517696579 100744117463951393276544869)
            ·
              refine ⟨18889522024490886239352163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100744117463951393276544869 18889522024490886239352163)
              ·
                refine ⟨28334283036736329359028245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18889522024490886239352163 28334283036736329359028245)
                ·
                  refine ⟨1328169517347015438704449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 28334283036736329359028245 1328169517347015438704449)
                  ·
                    refine ⟨996127138010261579028337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1328169517347015438704449 996127138010261579028337)
                    ·
                      refine ⟨747095353507696184271253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 996127138010261579028337 747095353507696184271253)
                      ·
                        rfl

theorem cell23_1454963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 6, 2, 2].length) (baseStart_1454963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454963 prefixEnd_1454963 := by exact prefixLift 1454963
  have htrace : WordTrace (prefixWord ++ tailWord_1454963) baseStart_1454963 baseEnd_1454963 := by
    simpa [prefixWord, tailWord_1454963, baseEnd_1454963] using wordTrace_append hprefix tailTrace_1454963
  have hstable : (prefixWord ++ tailWord_1454963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454963).length < 2 ^ (prefixWord ++ tailWord_1454963).sum := by decide
  have hdescent : baseEnd_1454963 < baseStart_1454963 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1454974 : List Nat := [4, 2, 3, 1, 2, 1, 2, 2, 2, 1, 3]
def baseStart_1454974 : Nat := 118140960795 + 1454974 * 2 ^ 59
def prefixEnd_1454974 : Nat := 4983230072969 + 3 ^ 40 * 1454974 * 2
def baseEnd_1454974 : Nat := 747101001794895641233703

theorem tailTrace_1454974 : CollatzResearch.WordTrace tailWord_1454974 prefixEnd_1454974 747101001794895641233703 := by
  unfold tailWord_1454974
  simp only [CollatzResearch.WordTrace]
  refine ⟨6633407678860645327628497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35378174287256775080685317 6633407678860645327628497)
  ·
    refine ⟨4975055759145483995721373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6633407678860645327628497 4975055759145483995721373)
    ·
      refine ⟨1865645909679556498395515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4975055759145483995721373 1865645909679556498395515)
      ·
        refine ⟨2798468864519334747593273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1865645909679556498395515 2798468864519334747593273)
        ·
          refine ⟨2098851648389501060694955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2798468864519334747593273 2098851648389501060694955)
          ·
            refine ⟨3148277472584251591042433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2098851648389501060694955 3148277472584251591042433)
            ·
              refine ⟨2361208104438188693281825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3148277472584251591042433 2361208104438188693281825)
              ·
                refine ⟨1770906078328641519961369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2361208104438188693281825 1770906078328641519961369)
                ·
                  refine ⟨1328179558746481139971027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1770906078328641519961369 1328179558746481139971027)
                  ·
                    refine ⟨1992269338119721709956541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1328179558746481139971027 1992269338119721709956541)
                    ·
                      refine ⟨747101001794895641233703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1992269338119721709956541 747101001794895641233703)
                      ·
                        rfl

theorem cell23_1454974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 1, 2, 2, 2, 1, 3].length) (baseStart_1454974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1454974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1454974 prefixEnd_1454974 := by exact prefixLift 1454974
  have htrace : WordTrace (prefixWord ++ tailWord_1454974) baseStart_1454974 baseEnd_1454974 := by
    simpa [prefixWord, tailWord_1454974, baseEnd_1454974] using wordTrace_append hprefix tailTrace_1454974
  have hstable : (prefixWord ++ tailWord_1454974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1454974).length < 2 ^ (prefixWord ++ tailWord_1454974).sum := by decide
  have hdescent : baseEnd_1454974 < baseStart_1454974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1454974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455073 : List Nat := [1, 2, 3, 1, 2, 1, 1, 5, 2, 2, 3]
def baseStart_1455073 : Nat := 118140960795 + 1455073 * 2 ^ 59
def prefixEnd_1455073 : Nat := 4983230072969 + 3 ^ 40 * 1455073 * 2
def baseEnd_1455073 : Nat := 747151836379690753895747

theorem tailTrace_1455073 : CollatzResearch.WordTrace tailWord_1455073 prefixEnd_1455073 747151836379690753895747 := by
  unfold tailWord_1455073
  simp only [CollatzResearch.WordTrace]
  refine ⟨53070872257526502528881873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35380581505017668352587915 53070872257526502528881873)
  ·
    refine ⟨39803154193144876896661405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53070872257526502528881873 39803154193144876896661405)
    ·
      refine ⟨14926182822429328836248027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39803154193144876896661405 14926182822429328836248027)
      ·
        refine ⟨22389274233643993254372041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14926182822429328836248027 22389274233643993254372041)
        ·
          refine ⟨16791955675232994940779031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22389274233643993254372041 16791955675232994940779031)
          ·
            refine ⟨25187933512849492411168547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16791955675232994940779031 25187933512849492411168547)
            ·
              refine ⟨37781900269274238616752821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25187933512849492411168547 37781900269274238616752821)
              ·
                refine ⟨3542053150244459870320577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37781900269274238616752821 3542053150244459870320577)
                ·
                  refine ⟨2656539862683344902740433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3542053150244459870320577 2656539862683344902740433)
                  ·
                    refine ⟨1992404897012508677055325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2656539862683344902740433 1992404897012508677055325)
                    ·
                      refine ⟨747151836379690753895747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1992404897012508677055325 747151836379690753895747)
                      ·
                        rfl

theorem cell23_1455073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 1, 5, 2, 2, 3].length) (baseStart_1455073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1455073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1455073 prefixEnd_1455073 := by exact prefixLift 1455073
  have htrace : WordTrace (prefixWord ++ tailWord_1455073) baseStart_1455073 baseEnd_1455073 := by
    simpa [prefixWord, tailWord_1455073, baseEnd_1455073] using wordTrace_append hprefix tailTrace_1455073
  have hstable : (prefixWord ++ tailWord_1455073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455073).length < 2 ^ (prefixWord ++ tailWord_1455073).sum := by decide
  have hdescent : baseEnd_1455073 < baseStart_1455073 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455097 : List Nat := [1, 2, 1, 3, 1, 3, 5, 2, 1, 4]
def baseStart_1455097 : Nat := 118140960795 + 1455097 * 2 ^ 59
def prefixEnd_1455097 : Nat := 4983230072969 + 3 ^ 40 * 1455097 * 2
def baseEnd_1455097 : Nat := 249054719971799553331879

theorem tailTrace_1455097 : CollatzResearch.WordTrace tailWord_1455097 prefixEnd_1455097 249054719971799553331879 := by
  unfold tailWord_1455097
  simp only [CollatzResearch.WordTrace]
  refine ⟨53071747609439554627755545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35381165072959703085170363 53071747609439554627755545)
  ·
    refine ⟨39803810707079665970816659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53071747609439554627755545 39803810707079665970816659)
    ·
      refine ⟨59705716060619498956224989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39803810707079665970816659 59705716060619498956224989)
      ·
        refine ⟨22389643522732312108584371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59705716060619498956224989 22389643522732312108584371)
        ·
          refine ⟨33584465284098468162876557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22389643522732312108584371 33584465284098468162876557)
          ·
            refine ⟨12594174481536925561078709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33584465284098468162876557 12594174481536925561078709)
            ·
              refine ⟨1180703857644086771351129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12594174481536925561078709 1180703857644086771351129)
              ·
                refine ⟨885527893233065078513347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1180703857644086771351129 885527893233065078513347)
                ·
                  refine ⟨1328291839849597617770021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 885527893233065078513347 1328291839849597617770021)
                  ·
                    refine ⟨249054719971799553331879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1328291839849597617770021 249054719971799553331879)
                    ·
                      rfl

theorem cell23_1455097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 5, 2, 1, 4].length) (baseStart_1455097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1455097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1455097 prefixEnd_1455097 := by exact prefixLift 1455097
  have htrace : WordTrace (prefixWord ++ tailWord_1455097) baseStart_1455097 baseEnd_1455097 := by
    simpa [prefixWord, tailWord_1455097, baseEnd_1455097] using wordTrace_append hprefix tailTrace_1455097
  have hstable : (prefixWord ++ tailWord_1455097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455097).length < 2 ^ (prefixWord ++ tailWord_1455097).sum := by decide
  have hdescent : baseEnd_1455097 < baseStart_1455097 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455113 : List Nat := [1, 2, 1, 1, 3, 1, 1, 3, 3, 5, 2]
def baseStart_1455113 : Nat := 118140960795 + 1455113 * 2 ^ 59
def prefixEnd_1455113 : Nat := 4983230072969 + 3 ^ 40 * 1455113 * 2
def baseEnd_1455113 : Nat := 747172375605870597395563

theorem tailTrace_1455113 : CollatzResearch.WordTrace tailWord_1455113 prefixEnd_1455113 747172375605870597395563 := by
  unfold tailWord_1455113
  simp only [CollatzResearch.WordTrace]
  refine ⟨53072331177381589360337993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35381554118254392906891995 53072331177381589360337993)
  ·
    refine ⟨39804248383036192020253495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53072331177381589360337993 39804248383036192020253495)
    ·
      refine ⟨59706372574554288030380243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39804248383036192020253495 59706372574554288030380243)
      ·
        refine ⟨89559558861831432045570365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59706372574554288030380243 89559558861831432045570365)
        ·
          refine ⟨33584834573186787017088887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89559558861831432045570365 33584834573186787017088887)
          ·
            refine ⟨50377251859780180525633331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33584834573186787017088887 50377251859780180525633331)
            ·
              refine ⟨75565877789670270788449997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50377251859780180525633331 75565877789670270788449997)
              ·
                refine ⟨28337204171126351545668749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75565877789670270788449997 28337204171126351545668749)
                ·
                  refine ⟨10626451564172381829625781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28337204171126351545668749 10626451564172381829625781)
                  ·
                    refine ⟨996229834141160796527417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10626451564172381829625781 996229834141160796527417)
                    ·
                      refine ⟨747172375605870597395563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 996229834141160796527417 747172375605870597395563)
                      ·
                        rfl

theorem cell23_1455113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 3, 3, 5, 2].length) (baseStart_1455113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1455113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1455113 prefixEnd_1455113 := by exact prefixLift 1455113
  have htrace : WordTrace (prefixWord ++ tailWord_1455113) baseStart_1455113 baseEnd_1455113 := by
    simpa [prefixWord, tailWord_1455113, baseEnd_1455113] using wordTrace_append hprefix tailTrace_1455113
  have hstable : (prefixWord ++ tailWord_1455113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455113).length < 2 ^ (prefixWord ++ tailWord_1455113).sum := by decide
  have hdescent : baseEnd_1455113 < baseStart_1455113 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455173 : List Nat := [1, 3, 1, 1, 1, 3, 3, 3, 1, 2, 4]
def baseStart_1455173 : Nat := 118140960795 + 1455173 * 2 ^ 59
def prefixEnd_1455173 : Nat := 4983230072969 + 3 ^ 40 * 1455173 * 2
def baseEnd_1455173 : Nat := 747203184445140362645287

theorem tailTrace_1455173 : CollatzResearch.WordTrace tailWord_1455173 prefixEnd_1455173 747203184445140362645287 := by
  unfold tailWord_1455173
  simp only [CollatzResearch.WordTrace]
  refine ⟨53074519557164219607522173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35383013038109479738348115 53074519557164219607522173)
  ·
    refine ⟨19902944833936582352820815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53074519557164219607522173 19902944833936582352820815)
    ·
      refine ⟨29854417250904873529231223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19902944833936582352820815 29854417250904873529231223)
      ·
        refine ⟨44781625876357310293846835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29854417250904873529231223 44781625876357310293846835)
        ·
          refine ⟨67172438814535965440770253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44781625876357310293846835 67172438814535965440770253)
          ·
            refine ⟨25189664555450987040288845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67172438814535965440770253 25189664555450987040288845)
            ·
              refine ⟨9446124208294120140108317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25189664555450987040288845 9446124208294120140108317)
              ·
                refine ⟨3542296578110295052540619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9446124208294120140108317 3542296578110295052540619)
                ·
                  refine ⟨5313444867165442578810929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3542296578110295052540619 5313444867165442578810929)
                  ·
                    refine ⟨3985083650374081934108197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5313444867165442578810929 3985083650374081934108197)
                    ·
                      refine ⟨747203184445140362645287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3985083650374081934108197 747203184445140362645287)
                      ·
                        rfl

theorem cell23_1455173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 3, 3, 1, 2, 4].length) (baseStart_1455173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1455173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1455173 prefixEnd_1455173 := by exact prefixLift 1455173
  have htrace : WordTrace (prefixWord ++ tailWord_1455173) baseStart_1455173 baseEnd_1455173 := by
    simpa [prefixWord, tailWord_1455173, baseEnd_1455173] using wordTrace_append hprefix tailTrace_1455173
  have hstable : (prefixWord ++ tailWord_1455173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455173).length < 2 ^ (prefixWord ++ tailWord_1455173).sum := by decide
  have hdescent : baseEnd_1455173 < baseStart_1455173 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455180 : List Nat := [2, 2, 1, 3, 1, 1, 1, 6, 1, 2, 3]
def baseStart_1455180 : Nat := 118140960795 + 1455180 * 2 ^ 59
def prefixEnd_1455180 : Nat := 4983230072969 + 3 ^ 40 * 1455180 * 2
def baseEnd_1455180 : Nat := 747206778809721835257755

theorem tailTrace_1455180 : CollatzResearch.WordTrace tailWord_1455180 prefixEnd_1455180 747206778809721835257755 := by
  unfold tailWord_1455180
  simp only [CollatzResearch.WordTrace]
  refine ⟨26537387434069429901513497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35383183245425906535351329 26537387434069429901513497)
  ·
    refine ⟨19903040575552072426135123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26537387434069429901513497 19903040575552072426135123)
    ·
      refine ⟨29854560863328108639202685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19903040575552072426135123 29854560863328108639202685)
      ·
        refine ⟨11195460323748040739701007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29854560863328108639202685 11195460323748040739701007)
        ·
          refine ⟨16793190485622061109551511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11195460323748040739701007 16793190485622061109551511)
          ·
            refine ⟨25189785728433091664327267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16793190485622061109551511 25189785728433091664327267)
            ·
              refine ⟨37784678592649637496490901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25189785728433091664327267 37784678592649637496490901)
              ·
                refine ⟨1771156809030451757648011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 37784678592649637496490901 1771156809030451757648011)
                ·
                  refine ⟨2656735213545677636472017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1771156809030451757648011 2656735213545677636472017)
                  ·
                    refine ⟨1992551410159258227354013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2656735213545677636472017 1992551410159258227354013)
                    ·
                      refine ⟨747206778809721835257755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1992551410159258227354013 747206778809721835257755)
                      ·
                        rfl

theorem cell23_1455180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 6, 1, 2, 3].length) (baseStart_1455180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1455180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1455180 prefixEnd_1455180 := by exact prefixLift 1455180
  have htrace : WordTrace (prefixWord ++ tailWord_1455180) baseStart_1455180 baseEnd_1455180 := by
    simpa [prefixWord, tailWord_1455180, baseEnd_1455180] using wordTrace_append hprefix tailTrace_1455180
  have hstable : (prefixWord ++ tailWord_1455180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455180).length < 2 ^ (prefixWord ++ tailWord_1455180).sum := by decide
  have hdescent : baseEnd_1455180 < baseStart_1455180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455193 : List Nat := [1, 2, 1, 2, 2, 1, 2, 3, 3, 3, 3]
def baseStart_1455193 : Nat := 118140960795 + 1455193 * 2 ^ 59
def prefixEnd_1455193 : Nat := 4983230072969 + 3 ^ 40 * 1455193 * 2
def baseEnd_1455193 : Nat := 747213454058230284395195

theorem tailTrace_1455193 : CollatzResearch.WordTrace tailWord_1455193 prefixEnd_1455193 747213454058230284395195 := by
  unfold tailWord_1455193
  simp only [CollatzResearch.WordTrace]
  refine ⟨53075249017091763023250233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35383499344727842015500155 53075249017091763023250233)
  ·
    refine ⟨39806436762818822267437675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53075249017091763023250233 39806436762818822267437675)
    ·
      refine ⟨59709655144228233401156513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39806436762818822267437675 59709655144228233401156513)
      ·
        refine ⟨44782241358171175050867385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59709655144228233401156513 44782241358171175050867385)
        ·
          refine ⟨33586681018628381288150539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44782241358171175050867385 33586681018628381288150539)
          ·
            refine ⟨50380021527942571932225809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33586681018628381288150539 50380021527942571932225809)
            ·
              refine ⟨37785016145956928949169357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50380021527942571932225809 37785016145956928949169357)
              ·
                refine ⟨14169381054733848355938509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37785016145956928949169357 14169381054733848355938509)
                ·
                  refine ⟨5313517895525193133476941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14169381054733848355938509 5313517895525193133476941)
                  ·
                    refine ⟨1992569210821947425053853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5313517895525193133476941 1992569210821947425053853)
                    ·
                      refine ⟨747213454058230284395195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1992569210821947425053853 747213454058230284395195)
                      ·
                        rfl

theorem cell23_1455193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 3, 3, 3, 3].length) (baseStart_1455193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1455193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1455193 prefixEnd_1455193 := by exact prefixLift 1455193
  have htrace : WordTrace (prefixWord ++ tailWord_1455193) baseStart_1455193 baseEnd_1455193 := by
    simpa [prefixWord, tailWord_1455193, baseEnd_1455193] using wordTrace_append hprefix tailTrace_1455193
  have hstable : (prefixWord ++ tailWord_1455193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455193).length < 2 ^ (prefixWord ++ tailWord_1455193).sum := by decide
  have hdescent : baseEnd_1455193 < baseStart_1455193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455221 : List Nat := [1, 3, 4, 3, 1, 1, 3, 1, 2, 4]
def baseStart_1455221 : Nat := 118140960795 + 1455221 * 2 ^ 59
def prefixEnd_1455221 : Nat := 4983230072969 + 3 ^ 40 * 1455221 * 2
def baseEnd_1455221 : Nat := 249075943838852058281689

theorem tailTrace_1455221 : CollatzResearch.WordTrace tailWord_1455221 prefixEnd_1455221 249075943838852058281689 := by
  unfold tailWord_1455221
  simp only [CollatzResearch.WordTrace]
  refine ⟨53076270260990323805269517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35384180173993549203513011 53076270260990323805269517)
  ·
    refine ⟨19903601347871371426976069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53076270260990323805269517 19903601347871371426976069)
    ·
      refine ⟨3731925252725882142558013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19903601347871371426976069 3731925252725882142558013)
      ·
        refine ⟨1399471969772205803459255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3731925252725882142558013 1399471969772205803459255)
        ·
          refine ⟨2099207954658308705188883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1399471969772205803459255 2099207954658308705188883)
          ·
            refine ⟨3148811931987463057783325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2099207954658308705188883 3148811931987463057783325)
            ·
              refine ⟨1180804474495298646668747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3148811931987463057783325 1180804474495298646668747)
              ·
                refine ⟨1771206711742947970003121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1180804474495298646668747 1771206711742947970003121)
                ·
                  refine ⟨1328405033807210977502341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1771206711742947970003121 1328405033807210977502341)
                  ·
                    refine ⟨249075943838852058281689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1328405033807210977502341 249075943838852058281689)
                    ·
                      rfl

theorem cell23_1455221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_1455221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1455221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1455221 prefixEnd_1455221 := by exact prefixLift 1455221
  have htrace : WordTrace (prefixWord ++ tailWord_1455221) baseStart_1455221 baseEnd_1455221 := by
    simpa [prefixWord, tailWord_1455221, baseEnd_1455221] using wordTrace_append hprefix tailTrace_1455221
  have hstable : (prefixWord ++ tailWord_1455221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455221).length < 2 ^ (prefixWord ++ tailWord_1455221).sum := by decide
  have hdescent : baseEnd_1455221 < baseStart_1455221 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455303 : List Nat := [1, 1, 4, 1, 1, 1, 1, 5, 1, 7]
def baseStart_1455303 : Nat := 118140960795 + 1455303 * 2 ^ 59
def prefixEnd_1455303 : Nat := 4983230072969 + 3 ^ 40 * 1455303 * 2
def baseEnd_1455303 : Nat := 249089978976741618006563

theorem tailTrace_1455303 : CollatzResearch.WordTrace tailWord_1455303 prefixEnd_1455303 249089978976741618006563 := by
  unfold tailWord_1455303
  simp only [CollatzResearch.WordTrace]
  refine ⟨53079261046693251809754563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35386174031128834539836375 53079261046693251809754563)
  ·
    refine ⟨79618891570039877714631845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53079261046693251809754563 79618891570039877714631845)
    ·
      refine ⟨14928542169382477071493471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79618891570039877714631845 14928542169382477071493471)
      ·
        refine ⟨22392813254073715607240207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14928542169382477071493471 22392813254073715607240207)
        ·
          refine ⟨33589219881110573410860311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22392813254073715607240207 33589219881110573410860311)
          ·
            refine ⟨50383829821665860116290467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33589219881110573410860311 50383829821665860116290467)
            ·
              refine ⟨75575744732498790174435701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50383829821665860116290467 75575744732498790174435701)
              ·
                refine ⟨7085226068671761578853347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75575744732498790174435701 7085226068671761578853347)
                ·
                  refine ⟨10627839103007642368280021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7085226068671761578853347 10627839103007642368280021)
                  ·
                    refine ⟨249089978976741618006563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10627839103007642368280021 249089978976741618006563)
                    ·
                      rfl

theorem cell23_1455303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 5, 1, 7].length) (baseStart_1455303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1455303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1455303 prefixEnd_1455303 := by exact prefixLift 1455303
  have htrace : WordTrace (prefixWord ++ tailWord_1455303) baseStart_1455303 baseEnd_1455303 := by
    simpa [prefixWord, tailWord_1455303, baseEnd_1455303] using wordTrace_append hprefix tailTrace_1455303
  have hstable : (prefixWord ++ tailWord_1455303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455303).length < 2 ^ (prefixWord ++ tailWord_1455303).sum := by decide
  have hdescent : baseEnd_1455303 < baseStart_1455303 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455384 : List Nat := [2, 1, 2, 3, 1, 3, 2, 4, 1, 4]
def baseStart_1455384 : Nat := 118140960795 + 1455384 * 2 ^ 59
def prefixEnd_1455384 : Nat := 4983230072969 + 3 ^ 40 * 1455384 * 2
def baseEnd_1455384 : Nat := 249103842954413012368939

theorem tailTrace_1455384 : CollatzResearch.WordTrace tailWord_1455384 prefixEnd_1455384 249103842954413012368939 := by
  unfold tailWord_1455384
  simp only [CollatzResearch.WordTrace]
  refine ⟨26541107679699901321726603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35388143572933201762302137 26541107679699901321726603)
  ·
    refine ⟨39811661519549851982589905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26541107679699901321726603 39811661519549851982589905)
    ·
      refine ⟨29858746139662388986942429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39811661519549851982589905 29858746139662388986942429)
      ·
        refine ⟨11197029802373395870103411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29858746139662388986942429 11197029802373395870103411)
        ·
          refine ⟨16795544703560093805155117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11197029802373395870103411 16795544703560093805155117)
          ·
            refine ⟨6298329263835035176933169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16795544703560093805155117 6298329263835035176933169)
            ·
              refine ⟨4723746947876276382699877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6298329263835035176933169 4723746947876276382699877)
              ·
                refine ⟨885702552726801821756227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4723746947876276382699877 885702552726801821756227)
                ·
                  refine ⟨1328553829090202732634341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 885702552726801821756227 1328553829090202732634341)
                  ·
                    refine ⟨249103842954413012368939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1328553829090202732634341 249103842954413012368939)
                    ·
                      rfl

theorem cell23_1455384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 2, 4, 1, 4].length) (baseStart_1455384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1455384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1455384 prefixEnd_1455384 := by exact prefixLift 1455384
  have htrace : WordTrace (prefixWord ++ tailWord_1455384) baseStart_1455384 baseEnd_1455384 := by
    simpa [prefixWord, tailWord_1455384, baseEnd_1455384] using wordTrace_append hprefix tailTrace_1455384
  have hstable : (prefixWord ++ tailWord_1455384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455384).length < 2 ^ (prefixWord ++ tailWord_1455384).sum := by decide
  have hdescent : baseEnd_1455384 < baseStart_1455384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455464 : List Nat := [2, 1, 4, 2, 3, 1, 1, 1, 3, 1, 4]
def baseStart_1455464 : Nat := 118140960795 + 1455464 * 2 ^ 59
def prefixEnd_1455464 : Nat := 4983230072969 + 3 ^ 40 * 1455464 * 2
def baseEnd_1455464 : Nat := 747352607315598724106449

theorem tailTrace_1455464 : CollatzResearch.WordTrace tailWord_1455464 prefixEnd_1455464 747352607315598724106449 := by
  unfold tailWord_1455464
  simp only [CollatzResearch.WordTrace]
  refine ⟨26542566599554988153182723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35390088799406650870910297 26542566599554988153182723)
  ·
    refine ⟨39813849899332482229774085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26542566599554988153182723 39813849899332482229774085)
    ·
      refine ⟨7465096856124840418082641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39813849899332482229774085 7465096856124840418082641)
      ·
        refine ⟨5598822642093630313561981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7465096856124840418082641 5598822642093630313561981)
        ·
          refine ⟨2099558490785111367585743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5598822642093630313561981 2099558490785111367585743)
          ·
            refine ⟨3149337736177667051378615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2099558490785111367585743 3149337736177667051378615)
            ·
              refine ⟨4724006604266500577067923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3149337736177667051378615 4724006604266500577067923)
              ·
                refine ⟨7086009906399750865601885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4724006604266500577067923 7086009906399750865601885)
                ·
                  refine ⟨2657253714899906574600707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7086009906399750865601885 2657253714899906574600707)
                  ·
                    refine ⟨3985880572349859861901061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2657253714899906574600707 3985880572349859861901061)
                    ·
                      refine ⟨747352607315598724106449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3985880572349859861901061 747352607315598724106449)
                      ·
                        rfl

theorem cell23_1455464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_1455464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1455464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1455464 prefixEnd_1455464 := by exact prefixLift 1455464
  have htrace : WordTrace (prefixWord ++ tailWord_1455464) baseStart_1455464 baseEnd_1455464 := by
    simpa [prefixWord, tailWord_1455464, baseEnd_1455464] using wordTrace_append hprefix tailTrace_1455464
  have hstable : (prefixWord ++ tailWord_1455464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455464).length < 2 ^ (prefixWord ++ tailWord_1455464).sum := by decide
  have hdescent : baseEnd_1455464 < baseStart_1455464 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455500 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 1, 9]
def baseStart_1455500 : Nat := 118140960795 + 1455500 * 2 ^ 59
def prefixEnd_1455500 : Nat := 4983230072969 + 3 ^ 40 * 1455500 * 2
def baseEnd_1455500 : Nat := 249123697539720194418761

theorem tailTrace_1455500 : CollatzResearch.WordTrace tailWord_1455500 prefixEnd_1455500 249123697539720194418761 := by
  unfold tailWord_1455500
  simp only [CollatzResearch.WordTrace]
  refine ⟨26543223113489777227337977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35390964151319702969783969 26543223113489777227337977)
  ·
    refine ⟨19907417335117332920503483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26543223113489777227337977 19907417335117332920503483)
    ·
      refine ⟨29861126002675999380755225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19907417335117332920503483 29861126002675999380755225)
      ·
        refine ⟨22395844502006999535566419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29861126002675999380755225 22395844502006999535566419)
        ·
          refine ⟨33593766753010499303349629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22395844502006999535566419 33593766753010499303349629)
          ·
            refine ⟨12597662532378937238756111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33593766753010499303349629 12597662532378937238756111)
            ·
              refine ⟨18896493798568405858134167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12597662532378937238756111 18896493798568405858134167)
              ·
                refine ⟨28344740697852608787201251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18896493798568405858134167 28344740697852608787201251)
                ·
                  refine ⟨42517111046778913180801877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28344740697852608787201251 42517111046778913180801877)
                  ·
                    refine ⟨249123697539720194418761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 42517111046778913180801877 249123697539720194418761)
                    ·
                      rfl

theorem cell23_1455500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 1, 9].length) (baseStart_1455500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1455500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1455500 prefixEnd_1455500 := by exact prefixLift 1455500
  have htrace : WordTrace (prefixWord ++ tailWord_1455500) baseStart_1455500 baseEnd_1455500 := by
    simpa [prefixWord, tailWord_1455500, baseEnd_1455500] using wordTrace_append hprefix tailTrace_1455500
  have hstable : (prefixWord ++ tailWord_1455500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455500).length < 2 ^ (prefixWord ++ tailWord_1455500).sum := by decide
  have hdescent : baseEnd_1455500 < baseStart_1455500 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455514 : List Nat := [3, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3]
def baseStart_1455514 : Nat := 118140960795 + 1455514 * 2 ^ 59
def prefixEnd_1455514 : Nat := 4983230072969 + 3 ^ 40 * 1455514 * 2
def baseEnd_1455514 : Nat := 747378281348323528481219

theorem tailTrace_1455514 : CollatzResearch.WordTrace tailWord_1455514 prefixEnd_1455514 747378281348323528481219 := by
  unfold tailWord_1455514
  simp only [CollatzResearch.WordTrace]
  refine ⟨13271739212232208711421399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35391304565952556563790397 13271739212232208711421399)
  ·
    refine ⟨19907608818348313067132099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13271739212232208711421399 19907608818348313067132099)
    ·
      refine ⟨29861413227522469600698149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19907608818348313067132099 29861413227522469600698149)
      ·
        refine ⟨5599014980160463050130903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29861413227522469600698149 5599014980160463050130903)
        ·
          refine ⟨8398522470240694575196355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5599014980160463050130903 8398522470240694575196355)
          ·
            refine ⟨12597783705361041862794533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8398522470240694575196355 12597783705361041862794533)
            ·
              refine ⟨2362084444755195349273975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12597783705361041862794533 2362084444755195349273975)
              ·
                refine ⟨3543126667132793023910963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2362084444755195349273975 3543126667132793023910963)
                ·
                  refine ⟨5314690000699189535866445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3543126667132793023910963 5314690000699189535866445)
                  ·
                    refine ⟨1993008750262196075949917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5314690000699189535866445 1993008750262196075949917)
                    ·
                      refine ⟨747378281348323528481219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1993008750262196075949917 747378281348323528481219)
                      ·
                        rfl

theorem cell23_1455514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 4, 1, 1, 3, 3].length) (baseStart_1455514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1455514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1455514 prefixEnd_1455514 := by exact prefixLift 1455514
  have htrace : WordTrace (prefixWord ++ tailWord_1455514) baseStart_1455514 baseEnd_1455514 := by
    simpa [prefixWord, tailWord_1455514, baseEnd_1455514] using wordTrace_append hprefix tailTrace_1455514
  have hstable : (prefixWord ++ tailWord_1455514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455514).length < 2 ^ (prefixWord ++ tailWord_1455514).sum := by decide
  have hdescent : baseEnd_1455514 < baseStart_1455514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455527 : List Nat := [1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 5]
def baseStart_1455527 : Nat := 118140960795 + 1455527 * 2 ^ 59
def prefixEnd_1455527 : Nat := 4983230072969 + 3 ^ 40 * 1455527 * 2
def baseEnd_1455527 : Nat := 747384956596831977618659

theorem tailTrace_1455527 : CollatzResearch.WordTrace tailWord_1455527 prefixEnd_1455527 747384956596831977618659 := by
  unfold tailWord_1455527
  simp only [CollatzResearch.WordTrace]
  refine ⟨53087430997881738065908835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35391620665254492043939223 53087430997881738065908835)
  ·
    refine ⟨79631146496822607098863253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53087430997881738065908835 79631146496822607098863253)
    ·
      refine ⟨3732709992038559707759215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 79631146496822607098863253 3732709992038559707759215)
      ·
        refine ⟨5599064988057839561638823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3732709992038559707759215 5599064988057839561638823)
        ·
          refine ⟨8398597482086759342458235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5599064988057839561638823 8398597482086759342458235)
          ·
            refine ⟨12597896223130139013687353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8398597482086759342458235 12597896223130139013687353)
            ·
              refine ⟨9448422167347604260265515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12597896223130139013687353 9448422167347604260265515)
              ·
                refine ⟨14172633251021406390398273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9448422167347604260265515 14172633251021406390398273)
                ·
                  refine ⟨10629474938266054792798705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14172633251021406390398273 10629474938266054792798705)
                  ·
                    refine ⟨7972106203699541094599029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10629474938266054792798705 7972106203699541094599029)
                    ·
                      refine ⟨747384956596831977618659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7972106203699541094599029 747384956596831977618659)
                      ·
                        rfl

theorem cell23_1455527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_1455527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1455527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1455527 prefixEnd_1455527 := by exact prefixLift 1455527
  have htrace : WordTrace (prefixWord ++ tailWord_1455527) baseStart_1455527 baseEnd_1455527 := by
    simpa [prefixWord, tailWord_1455527, baseEnd_1455527] using wordTrace_append hprefix tailTrace_1455527
  have hstable : (prefixWord ++ tailWord_1455527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455527).length < 2 ^ (prefixWord ++ tailWord_1455527).sum := by decide
  have hdescent : baseEnd_1455527 < baseStart_1455527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455567 : List Nat := [1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 4]
def baseStart_1455567 : Nat := 118140960795 + 1455567 * 2 ^ 59
def prefixEnd_1455567 : Nat := 4983230072969 + 3 ^ 40 * 1455567 * 2
def baseEnd_1455567 : Nat := 747405495823011821118475

theorem tailTrace_1455567 : CollatzResearch.WordTrace tailWord_1455567 prefixEnd_1455567 747405495823011821118475 := by
  unfold tailWord_1455567
  simp only [CollatzResearch.WordTrace]
  refine ⟨53088889917736824897364955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35392593278491216598243303 53088889917736824897364955)
  ·
    refine ⟨79633334876605237346047433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53088889917736824897364955 79633334876605237346047433)
    ·
      refine ⟨59725001157453928009535575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79633334876605237346047433 59725001157453928009535575)
      ·
        refine ⟨89587501736180892014303363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59725001157453928009535575 89587501736180892014303363)
        ·
          refine ⟨134381252604271338021455045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89587501736180892014303363 134381252604271338021455045)
          ·
            refine ⟨25196484863300875879022821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134381252604271338021455045 25196484863300875879022821)
            ·
              refine ⟨4724340911868914227316779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25196484863300875879022821 4724340911868914227316779)
              ·
                refine ⟨7086511367803371340975169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4724340911868914227316779 7086511367803371340975169)
                ·
                  refine ⟨5314883525852528505731377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7086511367803371340975169 5314883525852528505731377)
                  ·
                    refine ⟨3986162644389396379298533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5314883525852528505731377 3986162644389396379298533)
                    ·
                      refine ⟨747405495823011821118475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3986162644389396379298533 747405495823011821118475)
                      ·
                        rfl

theorem cell23_1455567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 4, 1, 2, 2, 4].length) (baseStart_1455567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1455567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1455567 prefixEnd_1455567 := by exact prefixLift 1455567
  have htrace : WordTrace (prefixWord ++ tailWord_1455567) baseStart_1455567 baseEnd_1455567 := by
    simpa [prefixWord, tailWord_1455567, baseEnd_1455567] using wordTrace_append hprefix tailTrace_1455567
  have hstable : (prefixWord ++ tailWord_1455567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455567).length < 2 ^ (prefixWord ++ tailWord_1455567).sum := by decide
  have hdescent : baseEnd_1455567 < baseStart_1455567 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455577 : List Nat := [1, 2, 1, 2, 4, 2, 2, 2, 7]
def baseStart_1455577 : Nat := 118140960795 + 1455577 * 2 ^ 59
def prefixEnd_1455577 : Nat := 4983230072969 + 3 ^ 40 * 1455577 * 2
def baseEnd_1455577 : Nat := 83045625625506309110381

theorem tailTrace_1455577 : CollatzResearch.WordTrace tailWord_1455577 prefixEnd_1455577 83045625625506309110381 := by
  unfold tailWord_1455577
  simp only [CollatzResearch.WordTrace]
  refine ⟨53089254647700596605228985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35392836431800397736819323 53089254647700596605228985)
  ·
    refine ⟨39816940985775447453921739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53089254647700596605228985 39816940985775447453921739)
    ·
      refine ⟨59725411478663171180882609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39816940985775447453921739 59725411478663171180882609)
      ·
        refine ⟨44794058608997378385661957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59725411478663171180882609 44794058608997378385661957)
        ·
          refine ⟨8398885989187008447311617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44794058608997378385661957 8398885989187008447311617)
          ·
            refine ⟨6299164491890256335483713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8398885989187008447311617 6299164491890256335483713)
            ·
              refine ⟨4724373368917692251612785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6299164491890256335483713 4724373368917692251612785)
              ·
                refine ⟨3543280026688269188709589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4724373368917692251612785 3543280026688269188709589)
                ·
                  refine ⟨83045625625506309110381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3543280026688269188709589 83045625625506309110381)
                  ·
                    rfl

theorem cell23_1455577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 2, 2, 2, 7].length) (baseStart_1455577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1455577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1455577 prefixEnd_1455577 := by exact prefixLift 1455577
  have htrace : WordTrace (prefixWord ++ tailWord_1455577) baseStart_1455577 baseEnd_1455577 := by
    simpa [prefixWord, tailWord_1455577, baseEnd_1455577] using wordTrace_append hprefix tailTrace_1455577
  have hstable : (prefixWord ++ tailWord_1455577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455577).length < 2 ^ (prefixWord ++ tailWord_1455577).sum := by decide
  have hdescent : baseEnd_1455577 < baseStart_1455577 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455698 : List Nat := [3, 2, 2, 1, 2, 4, 1, 1, 2, 2, 3]
def baseStart_1455698 : Nat := 118140960795 + 1455698 * 2 ^ 59
def prefixEnd_1455698 : Nat := 4983230072969 + 3 ^ 40 * 1455698 * 2
def baseEnd_1455698 : Nat := 747472761788750808580373

theorem tailTrace_1455698 : CollatzResearch.WordTrace tailWord_1455698 prefixEnd_1455698 747472761788750808580373 := by
  unfold tailWord_1455698
  simp only [CollatzResearch.WordTrace]
  refine ⟨13273416970065558567595937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35395778586841489513589165 13273416970065558567595937)
  ·
    refine ⟨9955062727549168925696953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13273416970065558567595937 9955062727549168925696953)
    ·
      refine ⟨7466297045661876694272715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9955062727549168925696953 7466297045661876694272715)
      ·
        refine ⟨11199445568492815041409073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7466297045661876694272715 11199445568492815041409073)
        ·
          refine ⟨8399584176369611281056805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11199445568492815041409073 8399584176369611281056805)
          ·
            refine ⟨1574922033069302115198151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8399584176369611281056805 1574922033069302115198151)
            ·
              refine ⟨2362383049603953172797227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1574922033069302115198151 2362383049603953172797227)
              ·
                refine ⟨3543574574405929759195841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2362383049603953172797227 3543574574405929759195841)
                ·
                  refine ⟨2657680930804447319396881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3543574574405929759195841 2657680930804447319396881)
                  ·
                    refine ⟨1993260698103335489547661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2657680930804447319396881 1993260698103335489547661)
                    ·
                      refine ⟨747472761788750808580373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1993260698103335489547661 747472761788750808580373)
                      ·
                        rfl

theorem cell23_1455698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_1455698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1455698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1455698 prefixEnd_1455698 := by exact prefixLift 1455698
  have htrace : WordTrace (prefixWord ++ tailWord_1455698) baseStart_1455698 baseEnd_1455698 := by
    simpa [prefixWord, tailWord_1455698, baseEnd_1455698] using wordTrace_append hprefix tailTrace_1455698
  have hstable : (prefixWord ++ tailWord_1455698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455698).length < 2 ^ (prefixWord ++ tailWord_1455698).sum := by decide
  have hdescent : baseEnd_1455698 < baseStart_1455698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455721 : List Nat := [1, 2, 1, 1, 1, 4, 2, 4, 2, 3, 2]
def baseStart_1455721 : Nat := 118140960795 + 1455721 * 2 ^ 59
def prefixEnd_1455721 : Nat := 4983230072969 + 3 ^ 40 * 1455721 * 2
def baseEnd_1455721 : Nat := 747484571843804218592767

theorem tailTrace_1455721 : CollatzResearch.WordTrace tailWord_1455721 prefixEnd_1455721 747484571843804218592767 := by
  unfold tailWord_1455721
  simp only [CollatzResearch.WordTrace]
  refine ⟨53094506759178909198471017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35396337839452606132314011 53094506759178909198471017)
  ·
    refine ⟨39820880069384181898853263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53094506759178909198471017 39820880069384181898853263)
    ·
      refine ⟨59731320104076272848279895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39820880069384181898853263 59731320104076272848279895)
      ·
        refine ⟨89596980156114409272419843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59731320104076272848279895 89596980156114409272419843)
        ·
          refine ⟨134395470234171613908629765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89596980156114409272419843 134395470234171613908629765)
          ·
            refine ⟨25199150668907177607868081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134395470234171613908629765 25199150668907177607868081)
            ·
              refine ⟨18899363001680383205901061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25199150668907177607868081 18899363001680383205901061)
              ·
                refine ⟨3543630562815071851106449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18899363001680383205901061 3543630562815071851106449)
                ·
                  refine ⟨2657722922111303888329837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3543630562815071851106449 2657722922111303888329837)
                  ·
                    refine ⟨996646095791738958123689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2657722922111303888329837 996646095791738958123689)
                    ·
                      refine ⟨747484571843804218592767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 996646095791738958123689 747484571843804218592767)
                      ·
                        rfl

theorem cell23_1455721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 2, 4, 2, 3, 2].length) (baseStart_1455721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1455721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1455721 prefixEnd_1455721 := by exact prefixLift 1455721
  have htrace : WordTrace (prefixWord ++ tailWord_1455721) baseStart_1455721 baseEnd_1455721 := by
    simpa [prefixWord, tailWord_1455721, baseEnd_1455721] using wordTrace_append hprefix tailTrace_1455721
  have hstable : (prefixWord ++ tailWord_1455721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455721).length < 2 ^ (prefixWord ++ tailWord_1455721).sum := by decide
  have hdescent : baseEnd_1455721 < baseStart_1455721 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455728 : List Nat := [2, 1, 1, 1, 6, 2, 2, 1, 3, 1, 3]
def baseStart_1455728 : Nat := 118140960795 + 1455728 * 2 ^ 59
def prefixEnd_1455728 : Nat := 4983230072969 + 3 ^ 40 * 1455728 * 2
def baseEnd_1455728 : Nat := 747488166208385691205235

theorem tailTrace_1455728 : CollatzResearch.WordTrace tailWord_1455728 prefixEnd_1455728 747488166208385691205235 := by
  unfold tailWord_1455728
  simp only [CollatzResearch.WordTrace]
  refine ⟨26547381035076774696987919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35396508046769032929317225 26547381035076774696987919)
  ·
    refine ⟨39821071552615162045481879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26547381035076774696987919 39821071552615162045481879)
    ·
      refine ⟨59731607328922743068222819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39821071552615162045481879 59731607328922743068222819)
      ·
        refine ⟨89597410993384114602334229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59731607328922743068222819 89597410993384114602334229)
        ·
          refine ⟨4199878640314880371984417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 89597410993384114602334229 4199878640314880371984417)
          ·
            refine ⟨3149908980236160278988313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4199878640314880371984417 3149908980236160278988313)
            ·
              refine ⟨2362431735177120209241235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3149908980236160278988313 2362431735177120209241235)
              ·
                refine ⟨3543647602765680313861853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2362431735177120209241235 3543647602765680313861853)
                ·
                  refine ⟨1328867851037130117698195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3543647602765680313861853 1328867851037130117698195)
                  ·
                    refine ⟨1993301776555695176547293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1328867851037130117698195 1993301776555695176547293)
                    ·
                      refine ⟨747488166208385691205235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1993301776555695176547293 747488166208385691205235)
                      ·
                        rfl

theorem cell23_1455728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 2, 1, 3, 1, 3].length) (baseStart_1455728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1455728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1455728 prefixEnd_1455728 := by exact prefixLift 1455728
  have htrace : WordTrace (prefixWord ++ tailWord_1455728) baseStart_1455728 baseEnd_1455728 := by
    simpa [prefixWord, tailWord_1455728, baseEnd_1455728] using wordTrace_append hprefix tailTrace_1455728
  have hstable : (prefixWord ++ tailWord_1455728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455728).length < 2 ^ (prefixWord ++ tailWord_1455728).sum := by decide
  have hdescent : baseEnd_1455728 < baseStart_1455728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455748 : List Nat := [2, 3, 2, 1, 4, 1, 2, 2, 1, 5]
def baseStart_1455748 : Nat := 118140960795 + 1455748 * 2 ^ 59
def prefixEnd_1455748 : Nat := 4983230072969 + 3 ^ 40 * 1455748 * 2
def baseEnd_1455748 : Nat := 249166145273825204318381

theorem tailTrace_1455748 : CollatzResearch.WordTrace tailWord_1455748 prefixEnd_1455748 249166145273825204318381 := by
  unfold tailWord_1455748
  simp only [CollatzResearch.WordTrace]
  refine ⟨26547745765040546404851949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35396994353387395206469265 26547745765040546404851949)
  ·
    refine ⟨9955404661890204901819481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26547745765040546404851949 9955404661890204901819481)
    ·
      refine ⟨7466553496417653676364611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9955404661890204901819481 7466553496417653676364611)
      ·
        refine ⟨11199830244626480514546917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7466553496417653676364611 11199830244626480514546917)
        ·
          refine ⟨2099968170867465096477547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11199830244626480514546917 2099968170867465096477547)
          ·
            refine ⟨3149952256301197644716321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2099968170867465096477547 3149952256301197644716321)
            ·
              refine ⟨2362464192225898233537241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3149952256301197644716321 2362464192225898233537241)
              ·
                refine ⟨1771848144169423675152931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2362464192225898233537241 1771848144169423675152931)
                ·
                  refine ⟨2657772216254135512729397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1771848144169423675152931 2657772216254135512729397)
                  ·
                    refine ⟨249166145273825204318381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2657772216254135512729397 249166145273825204318381)
                    ·
                      rfl

theorem cell23_1455748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_1455748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1455748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1455748 prefixEnd_1455748 := by exact prefixLift 1455748
  have htrace : WordTrace (prefixWord ++ tailWord_1455748) baseStart_1455748 baseEnd_1455748 := by
    simpa [prefixWord, tailWord_1455748, baseEnd_1455748] using wordTrace_append hprefix tailTrace_1455748
  have hstable : (prefixWord ++ tailWord_1455748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455748).length < 2 ^ (prefixWord ++ tailWord_1455748).sum := by decide
  have hdescent : baseEnd_1455748 < baseStart_1455748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455751 : List Nat := [1, 1, 4, 2, 1, 3, 1, 4, 1, 1, 4]
def baseStart_1455751 : Nat := 118140960795 + 1455751 * 2 ^ 59
def prefixEnd_1455751 : Nat := 4983230072969 + 3 ^ 40 * 1455751 * 2
def baseEnd_1455751 : Nat := 747499976263439101217629

theorem tailTrace_1455751 : CollatzResearch.WordTrace tailWord_1455751 prefixEnd_1455751 747499976263439101217629 := by
  unfold tailWord_1455751
  simp only [CollatzResearch.WordTrace]
  refine ⟨53095600949070224322063107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35397067299380149548042071 53095600949070224322063107)
  ·
    refine ⟨79643401423605336483094661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53095600949070224322063107 79643401423605336483094661)
    ·
      refine ⟨14933137766926000590580249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79643401423605336483094661 14933137766926000590580249)
      ·
        refine ⟨11199853325194500442935187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14933137766926000590580249 11199853325194500442935187)
        ·
          refine ⟨16799779987791750664402781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11199853325194500442935187 16799779987791750664402781)
          ·
            refine ⟨6299917495421906499151043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16799779987791750664402781 6299917495421906499151043)
            ·
              refine ⟨9449876243132859748726565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6299917495421906499151043 9449876243132859748726565)
              ·
                refine ⟨1771851795587411202886231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9449876243132859748726565 1771851795587411202886231)
                ·
                  refine ⟨2657777693381116804329347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1771851795587411202886231 2657777693381116804329347)
                  ·
                    refine ⟨3986666540071675206494021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2657777693381116804329347 3986666540071675206494021)
                    ·
                      refine ⟨747499976263439101217629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3986666540071675206494021 747499976263439101217629)
                      ·
                        rfl

theorem cell23_1455751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_1455751 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1455751 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1455751 prefixEnd_1455751 := by exact prefixLift 1455751
  have htrace : WordTrace (prefixWord ++ tailWord_1455751) baseStart_1455751 baseEnd_1455751 := by
    simpa [prefixWord, tailWord_1455751, baseEnd_1455751] using wordTrace_append hprefix tailTrace_1455751
  have hstable : (prefixWord ++ tailWord_1455751).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455751).length < 2 ^ (prefixWord ++ tailWord_1455751).sum := by decide
  have hdescent : baseEnd_1455751 < baseStart_1455751 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455798 : List Nat := [5, 1, 3, 1, 1, 1, 2, 1, 1, 1, 6]
def baseStart_1455798 : Nat := 118140960795 + 1455798 * 2 ^ 59
def prefixEnd_1455798 : Nat := 4983230072969 + 3 ^ 40 * 1455798 * 2
def baseEnd_1455798 : Nat := 747524109854200417329913

theorem tailTrace_1455798 : CollatzResearch.WordTrace tailWord_1455798 prefixEnd_1455798 747524109854200417329913 := by
  unfold tailWord_1455798
  simp only [CollatzResearch.WordTrace]
  refine ⟨3318582198743746959314003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35398210119933300899349365 3318582198743746959314003)
  ·
    refine ⟨4977873298115620438971005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3318582198743746959314003 4977873298115620438971005)
    ·
      refine ⟨1866702486793357664614127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4977873298115620438971005 1866702486793357664614127)
      ·
        refine ⟨2800053730190036496921191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1866702486793357664614127 2800053730190036496921191)
        ·
          refine ⟨4200080595285054745381787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2800053730190036496921191 4200080595285054745381787)
          ·
            refine ⟨6300120892927582118072681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4200080595285054745381787 6300120892927582118072681)
            ·
              refine ⟨4725090669695686588554511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6300120892927582118072681 4725090669695686588554511)
              ·
                refine ⟨7087636004543529882831767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4725090669695686588554511 7087636004543529882831767)
                ·
                  refine ⟨10631454006815294824247651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7087636004543529882831767 10631454006815294824247651)
                  ·
                    refine ⟨15947181010222942236371477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10631454006815294824247651 15947181010222942236371477)
                    ·
                      refine ⟨747524109854200417329913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15947181010222942236371477 747524109854200417329913)
                      ·
                        rfl

theorem cell23_1455798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_1455798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1455798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1455798 prefixEnd_1455798 := by exact prefixLift 1455798
  have htrace : WordTrace (prefixWord ++ tailWord_1455798) baseStart_1455798 baseEnd_1455798 := by
    simpa [prefixWord, tailWord_1455798, baseEnd_1455798] using wordTrace_append hprefix tailTrace_1455798
  have hstable : (prefixWord ++ tailWord_1455798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455798).length < 2 ^ (prefixWord ++ tailWord_1455798).sum := by decide
  have hdescent : baseEnd_1455798 < baseStart_1455798 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455818 : List Nat := [3, 1, 2, 1, 5, 1, 1, 2, 1, 3, 3]
def baseStart_1455818 : Nat := 118140960795 + 1455818 * 2 ^ 59
def prefixEnd_1455818 : Nat := 4983230072969 + 3 ^ 40 * 1455818 * 2
def baseEnd_1455818 : Nat := 747534379467290339079821

theorem tailTrace_1455818 : CollatzResearch.WordTrace tailWord_1455818 prefixEnd_1455818 747534379467290339079821 := by
  unfold tailWord_1455818
  simp only [CollatzResearch.WordTrace]
  refine ⟨13274511159956873691188027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35398696426551663176501405 13274511159956873691188027)
  ·
    refine ⟨19911766739935310536782041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13274511159956873691188027 19911766739935310536782041)
    ·
      refine ⟨14933825054951482902586531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19911766739935310536782041 14933825054951482902586531)
      ·
        refine ⟨22400737582427224353879797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14933825054951482902586531 22400737582427224353879797)
        ·
          refine ⟨2100069148352552283176231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22400737582427224353879797 2100069148352552283176231)
          ·
            refine ⟨3150103722528828424764347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2100069148352552283176231 3150103722528828424764347)
            ·
              refine ⟨4725155583793242637146521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3150103722528828424764347 4725155583793242637146521)
              ·
                refine ⟨3543866687844931977859891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4725155583793242637146521 3543866687844931977859891)
                ·
                  refine ⟨5315800031767397966789837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3543866687844931977859891 5315800031767397966789837)
                  ·
                    refine ⟨1993425011912774237546189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5315800031767397966789837 1993425011912774237546189)
                    ·
                      refine ⟨747534379467290339079821, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1993425011912774237546189 747534379467290339079821)
                      ·
                        rfl

theorem cell23_1455818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_1455818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1455818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1455818 prefixEnd_1455818 := by exact prefixLift 1455818
  have htrace : WordTrace (prefixWord ++ tailWord_1455818) baseStart_1455818 baseEnd_1455818 := by
    simpa [prefixWord, tailWord_1455818, baseEnd_1455818] using wordTrace_append hprefix tailTrace_1455818
  have hstable : (prefixWord ++ tailWord_1455818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455818).length < 2 ^ (prefixWord ++ tailWord_1455818).sum := by decide
  have hdescent : baseEnd_1455818 < baseStart_1455818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455879 : List Nat := [1, 1, 4, 4, 2, 2, 2, 1, 1, 3, 2]
def baseStart_1455879 : Nat := 118140960795 + 1455879 * 2 ^ 59
def prefixEnd_1455879 : Nat := 4983230072969 + 3 ^ 40 * 1455879 * 2
def baseEnd_1455879 : Nat := 747565701787214600417041

theorem tailTrace_1455879 : CollatzResearch.WordTrace tailWord_1455879 prefixEnd_1455879 747565701787214600417041 := by
  unfold tailWord_1455879
  simp only [CollatzResearch.WordTrace]
  refine ⟨53100269492606502182722691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35400179661737668121815127 53100269492606502182722691)
  ·
    refine ⟨79650404238909753274084037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53100269492606502182722691 79650404238909753274084037)
    ·
      refine ⟨14934450794795578738890757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79650404238909753274084037 14934450794795578738890757)
      ·
        refine ⟨2800209524024171013542017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14934450794795578738890757 2800209524024171013542017)
        ·
          refine ⟨2100157143018128260156513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2800209524024171013542017 2100157143018128260156513)
          ·
            refine ⟨1575117857263596195117385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2100157143018128260156513 1575117857263596195117385)
            ·
              refine ⟨1181338392947697146338039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1575117857263596195117385 1181338392947697146338039)
              ·
                refine ⟨1772007589421545719507059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1181338392947697146338039 1772007589421545719507059)
                ·
                  refine ⟨2658011384132318579260589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1772007589421545719507059 2658011384132318579260589)
                  ·
                    refine ⟨996754269049619467222721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2658011384132318579260589 996754269049619467222721)
                    ·
                      refine ⟨747565701787214600417041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 996754269049619467222721 747565701787214600417041)
                      ·
                        rfl

theorem cell23_1455879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_1455879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1455879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1455879 prefixEnd_1455879 := by exact prefixLift 1455879
  have htrace : WordTrace (prefixWord ++ tailWord_1455879) baseStart_1455879 baseEnd_1455879 := by
    simpa [prefixWord, tailWord_1455879, baseEnd_1455879] using wordTrace_append hprefix tailTrace_1455879
  have hstable : (prefixWord ++ tailWord_1455879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455879).length < 2 ^ (prefixWord ++ tailWord_1455879).sum := by decide
  have hdescent : baseEnd_1455879 < baseStart_1455879 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455898 : List Nat := [3, 1, 1, 3, 2, 2, 2, 4, 5]
def baseStart_1455898 : Nat := 118140960795 + 1455898 * 2 ^ 59
def prefixEnd_1455898 : Nat := 4983230072969 + 3 ^ 40 * 1455898 * 2
def baseEnd_1455898 : Nat := 83063939768850002897717

theorem tailTrace_1455898 : CollatzResearch.WordTrace tailWord_1455898 prefixEnd_1455898 83063939768850002897717 := by
  unfold tailWord_1455898
  simp only [CollatzResearch.WordTrace]
  refine ⟨13275240619884417106916087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35400641653025112285109565 13275240619884417106916087)
  ·
    refine ⟨19912860929826625660374131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13275240619884417106916087 19912860929826625660374131)
    ·
      refine ⟨29869291394739938490561197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19912860929826625660374131 29869291394739938490561197)
      ·
        refine ⟨11200984273027476933960449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29869291394739938490561197 11200984273027476933960449)
        ·
          refine ⟨8400738204770607700470337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11200984273027476933960449 8400738204770607700470337)
          ·
            refine ⟨6300553653577955775352753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8400738204770607700470337 6300553653577955775352753)
            ·
              refine ⟨4725415240183466831514565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6300553653577955775352753 4725415240183466831514565)
              ·
                refine ⟨886015357534400030908981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4725415240183466831514565 886015357534400030908981)
                ·
                  refine ⟨83063939768850002897717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 886015357534400030908981 83063939768850002897717)
                  ·
                    rfl

theorem cell23_1455898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 2, 4, 5].length) (baseStart_1455898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1455898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1455898 prefixEnd_1455898 := by exact prefixLift 1455898
  have htrace : WordTrace (prefixWord ++ tailWord_1455898) baseStart_1455898 baseEnd_1455898 := by
    simpa [prefixWord, tailWord_1455898, baseEnd_1455898] using wordTrace_append hprefix tailTrace_1455898
  have hstable : (prefixWord ++ tailWord_1455898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455898).length < 2 ^ (prefixWord ++ tailWord_1455898).sum := by decide
  have hdescent : baseEnd_1455898 < baseStart_1455898 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1455908 : List Nat := [2, 3, 1, 3, 2, 1, 2, 1, 2, 3, 3]
def baseStart_1455908 : Nat := 118140960795 + 1455908 * 2 ^ 59
def prefixEnd_1455908 : Nat := 4983230072969 + 3 ^ 40 * 1455908 * 2
def baseEnd_1455908 : Nat := 747580592726194986954407

theorem tailTrace_1455908 : CollatzResearch.WordTrace tailWord_1455908 prefixEnd_1455908 747580592726194986954407 := by
  unfold tailWord_1455908
  simp only [CollatzResearch.WordTrace]
  refine ⟨26550663604750720067764189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35400884806334293423685585 26550663604750720067764189)
  ·
    refine ⟨9956498851781520025411571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26550663604750720067764189 9956498851781520025411571)
    ·
      refine ⟨14934748277672280038117357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9956498851781520025411571 14934748277672280038117357)
      ·
        refine ⟨5600530604127105014294009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14934748277672280038117357 5600530604127105014294009)
        ·
          refine ⟨4200397953095328760720507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5600530604127105014294009 4200397953095328760720507)
          ·
            refine ⟨6300596929642993141080761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4200397953095328760720507 6300596929642993141080761)
            ·
              refine ⟨4725447697232244855810571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6300596929642993141080761 4725447697232244855810571)
              ·
                refine ⟨7088171545848367283715857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4725447697232244855810571 7088171545848367283715857)
                ·
                  refine ⟨5316128659386275462786893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7088171545848367283715857 5316128659386275462786893)
                  ·
                    refine ⟨1993548247269853298545085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5316128659386275462786893 1993548247269853298545085)
                    ·
                      refine ⟨747580592726194986954407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1993548247269853298545085 747580592726194986954407)
                      ·
                        rfl

theorem cell23_1455908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_1455908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1455908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1455908 prefixEnd_1455908 := by exact prefixLift 1455908
  have htrace : WordTrace (prefixWord ++ tailWord_1455908) baseStart_1455908 baseEnd_1455908 := by
    simpa [prefixWord, tailWord_1455908, baseEnd_1455908] using wordTrace_append hprefix tailTrace_1455908
  have hstable : (prefixWord ++ tailWord_1455908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1455908).length < 2 ^ (prefixWord ++ tailWord_1455908).sum := by decide
  have hdescent : baseEnd_1455908 < baseStart_1455908 := by decide
  rcases family_descends (prefixWord ++ tailWord_1455908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456041 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 5, 1, 5]
def baseStart_1456041 : Nat := 118140960795 + 1456041 * 2 ^ 59
def prefixEnd_1456041 : Nat := 4983230072969 + 3 ^ 40 * 1456041 * 2
def baseEnd_1456041 : Nat := 747648885653242966591295

theorem tailTrace_1456041 : CollatzResearch.WordTrace tailWord_1456041 prefixEnd_1456041 747648885653242966591295 := by
  unfold tailWord_1456041
  simp only [CollatzResearch.WordTrace]
  refine ⟨53106178118019603850119977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35404118745346402566746651 53106178118019603850119977)
  ·
    refine ⟨39829633588514702887589983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53106178118019603850119977 39829633588514702887589983)
    ·
      refine ⟨59744450382772054331384975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39829633588514702887589983 59744450382772054331384975)
      ·
        refine ⟨89616675574158081497077463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59744450382772054331384975 89616675574158081497077463)
        ·
          refine ⟨134425013361237122245616195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89616675574158081497077463 134425013361237122245616195)
          ·
            refine ⟨201637520041855683368424293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134425013361237122245616195 201637520041855683368424293)
            ·
              refine ⟨37807035007847940631579555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 201637520041855683368424293 37807035007847940631579555)
              ·
                refine ⟨56710552511771910947369333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37807035007847940631579555 56710552511771910947369333)
                ·
                  refine ⟨5316614297978616651315875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 56710552511771910947369333 5316614297978616651315875)
                  ·
                    refine ⟨7974921446967924976973813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5316614297978616651315875 7974921446967924976973813)
                    ·
                      refine ⟨747648885653242966591295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7974921446967924976973813 747648885653242966591295)
                      ·
                        rfl

theorem cell23_1456041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 5, 1, 5].length) (baseStart_1456041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456041 prefixEnd_1456041 := by exact prefixLift 1456041
  have htrace : WordTrace (prefixWord ++ tailWord_1456041) baseStart_1456041 baseEnd_1456041 := by
    simpa [prefixWord, tailWord_1456041, baseEnd_1456041] using wordTrace_append hprefix tailTrace_1456041
  have hstable : (prefixWord ++ tailWord_1456041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456041).length < 2 ^ (prefixWord ++ tailWord_1456041).sum := by decide
  have hdescent : baseEnd_1456041 < baseStart_1456041 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456049 : List Nat := [1, 2, 2, 4, 2, 2, 2, 3, 1, 1, 3]
def baseStart_1456049 : Nat := 118140960795 + 1456049 * 2 ^ 59
def prefixEnd_1456049 : Nat := 4983230072969 + 3 ^ 40 * 1456049 * 2
def baseEnd_1456049 : Nat := 747652993498478935291259

theorem tailTrace_1456049 : CollatzResearch.WordTrace tailWord_1456049 prefixEnd_1456049 747652993498478935291259 := by
  unfold tailWord_1456049
  simp only [CollatzResearch.WordTrace]
  refine ⟨53106469901990621216411201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35404313267993747477607467 53106469901990621216411201)
  ·
    refine ⟨39829852426492965912308401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53106469901990621216411201 39829852426492965912308401)
    ·
      refine ⟨29872389319869724434231301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39829852426492965912308401 29872389319869724434231301)
      ·
        refine ⟨5601072997475573331418369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29872389319869724434231301 5601072997475573331418369)
        ·
          refine ⟨4200804748106679998563777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5601072997475573331418369 4200804748106679998563777)
          ·
            refine ⟨3150603561080009998922833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4200804748106679998563777 3150603561080009998922833)
            ·
              refine ⟨2362952670810007499192125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3150603561080009998922833 2362952670810007499192125)
              ·
                refine ⟨886107251553752812197047, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2362952670810007499192125 886107251553752812197047)
                ·
                  refine ⟨1329160877330629218295571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 886107251553752812197047 1329160877330629218295571)
                  ·
                    refine ⟨1993741315995943827443357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1329160877330629218295571 1993741315995943827443357)
                    ·
                      refine ⟨747652993498478935291259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1993741315995943827443357 747652993498478935291259)
                      ·
                        rfl

theorem cell23_1456049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_1456049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456049 prefixEnd_1456049 := by exact prefixLift 1456049
  have htrace : WordTrace (prefixWord ++ tailWord_1456049) baseStart_1456049 baseEnd_1456049 := by
    simpa [prefixWord, tailWord_1456049, baseEnd_1456049] using wordTrace_append hprefix tailTrace_1456049
  have hstable : (prefixWord ++ tailWord_1456049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456049).length < 2 ^ (prefixWord ++ tailWord_1456049).sum := by decide
  have hdescent : baseEnd_1456049 < baseStart_1456049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456055 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 7, 2, 2]
def baseStart_1456055 : Nat := 118140960795 + 1456055 * 2 ^ 59
def prefixEnd_1456055 : Nat := 4983230072969 + 3 ^ 40 * 1456055 * 2
def baseEnd_1456055 : Nat := 747656074382405911816231

theorem tailTrace_1456055 : CollatzResearch.WordTrace tailWord_1456055 prefixEnd_1456055 747656074382405911816231 := by
  unfold tailWord_1456055
  simp only [CollatzResearch.WordTrace]
  refine ⟨53106688739968884241129619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35404459159979256160753079 53106688739968884241129619)
  ·
    refine ⟨79660033109953326361694429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53106688739968884241129619 79660033109953326361694429)
    ·
      refine ⟨29872512416232497385635411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79660033109953326361694429 29872512416232497385635411)
      ·
        refine ⟨44808768624348746078453117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29872512416232497385635411 44808768624348746078453117)
        ·
          refine ⟨16803288234130779779419919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44808768624348746078453117 16803288234130779779419919)
          ·
            refine ⟨25204932351196169669129879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16803288234130779779419919 25204932351196169669129879)
            ·
              refine ⟨37807398526794254503694819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25204932351196169669129879 37807398526794254503694819)
              ·
                refine ⟨56711097790191381755542229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37807398526794254503694819 56711097790191381755542229)
                ·
                  refine ⟨1329166354457610509895521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 56711097790191381755542229 1329166354457610509895521)
                  ·
                    refine ⟨996874765843207882421641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1329166354457610509895521 996874765843207882421641)
                    ·
                      refine ⟨747656074382405911816231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 996874765843207882421641 747656074382405911816231)
                      ·
                        rfl

theorem cell23_1456055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 7, 2, 2].length) (baseStart_1456055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456055 prefixEnd_1456055 := by exact prefixLift 1456055
  have htrace : WordTrace (prefixWord ++ tailWord_1456055) baseStart_1456055 baseEnd_1456055 := by
    simpa [prefixWord, tailWord_1456055, baseEnd_1456055] using wordTrace_append hprefix tailTrace_1456055
  have hstable : (prefixWord ++ tailWord_1456055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456055).length < 2 ^ (prefixWord ++ tailWord_1456055).sum := by decide
  have hdescent : baseEnd_1456055 < baseStart_1456055 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456058 : List Nat := [3, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3]
def baseStart_1456058 : Nat := 118140960795 + 1456058 * 2 ^ 59
def prefixEnd_1456058 : Nat := 4983230072969 + 3 ^ 40 * 1456058 * 2
def baseEnd_1456058 : Nat := 747657614824369400078717

theorem tailTrace_1456058 : CollatzResearch.WordTrace tailWord_1456058 prefixEnd_1456058 747657614824369400078717 := by
  unfold tailWord_1456058
  simp only [CollatzResearch.WordTrace]
  refine ⟨13276699539739503938372207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35404532105972010502325885 13276699539739503938372207)
  ·
    refine ⟨19915049309609255907558311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13276699539739503938372207 19915049309609255907558311)
    ·
      refine ⟨29872573964413883861337467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19915049309609255907558311 29872573964413883861337467)
      ·
        refine ⟨44808860946620825792006201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29872573964413883861337467 44808860946620825792006201)
        ·
          refine ⟨33606645709965619344004651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44808860946620825792006201 33606645709965619344004651)
          ·
            refine ⟨50409968564948429016006977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33606645709965619344004651 50409968564948429016006977)
            ·
              refine ⟨37807476423711321762005233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50409968564948429016006977 37807476423711321762005233)
              ·
                refine ⟨28355607317783491321503925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37807476423711321762005233 28355607317783491321503925)
                ·
                  refine ⟨2658338186042202311390993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28355607317783491321503925 2658338186042202311390993)
                  ·
                    refine ⟨1993753639531651733543245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2658338186042202311390993 1993753639531651733543245)
                    ·
                      refine ⟨747657614824369400078717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1993753639531651733543245 747657614824369400078717)
                      ·
                        rfl

theorem cell23_1456058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 2, 2, 5, 2, 3].length) (baseStart_1456058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456058 prefixEnd_1456058 := by exact prefixLift 1456058
  have htrace : WordTrace (prefixWord ++ tailWord_1456058) baseStart_1456058 baseEnd_1456058 := by
    simpa [prefixWord, tailWord_1456058, baseEnd_1456058] using wordTrace_append hprefix tailTrace_1456058
  have hstable : (prefixWord ++ tailWord_1456058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456058).length < 2 ^ (prefixWord ++ tailWord_1456058).sum := by decide
  have hdescent : baseEnd_1456058 < baseStart_1456058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456071 : List Nat := [1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 7]
def baseStart_1456071 : Nat := 118140960795 + 1456071 * 2 ^ 59
def prefixEnd_1456071 : Nat := 4983230072969 + 3 ^ 40 * 1456071 * 2
def baseEnd_1456071 : Nat := 747664290072877849216157

theorem tailTrace_1456071 : CollatzResearch.WordTrace tailWord_1456071 prefixEnd_1456071 747664290072877849216157 := by
  unfold tailWord_1456071
  simp only [CollatzResearch.WordTrace]
  refine ⟨53107272307910918973712067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35404848205273945982474711 53107272307910918973712067)
  ·
    refine ⟨79660908461866378460568101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53107272307910918973712067 79660908461866378460568101)
    ·
      refine ⟨14936420336599945961356519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79660908461866378460568101 14936420336599945961356519)
      ·
        refine ⟨22404630504899918942034779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14936420336599945961356519 22404630504899918942034779)
        ·
          refine ⟨33606945757349878413052169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22404630504899918942034779 33606945757349878413052169)
          ·
            refine ⟨25205209318012408809789127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33606945757349878413052169 25205209318012408809789127)
            ·
              refine ⟨37807813977018613214683691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25205209318012408809789127 37807813977018613214683691)
              ·
                refine ⟨56711720965527919822025537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37807813977018613214683691 56711720965527919822025537)
                ·
                  refine ⟨42533790724145939866519153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 56711720965527919822025537 42533790724145939866519153)
                  ·
                    refine ⟨31900343043109454899889365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42533790724145939866519153 31900343043109454899889365)
                    ·
                      refine ⟨747664290072877849216157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31900343043109454899889365 747664290072877849216157)
                      ·
                        rfl

theorem cell23_1456071_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 1, 1, 2, 2, 7].length) (baseStart_1456071 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456071 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456071 prefixEnd_1456071 := by exact prefixLift 1456071
  have htrace : WordTrace (prefixWord ++ tailWord_1456071) baseStart_1456071 baseEnd_1456071 := by
    simpa [prefixWord, tailWord_1456071, baseEnd_1456071] using wordTrace_append hprefix tailTrace_1456071
  have hstable : (prefixWord ++ tailWord_1456071).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456071).length < 2 ^ (prefixWord ++ tailWord_1456071).sum := by decide
  have hdescent : baseEnd_1456071 < baseStart_1456071 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456071) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456072 : List Nat := [2, 1, 3, 1, 4, 1, 1, 3, 3, 2, 2]
def baseStart_1456072 : Nat := 118140960795 + 1456072 * 2 ^ 59
def prefixEnd_1456072 : Nat := 4983230072969 + 3 ^ 40 * 1456072 * 2
def baseEnd_1456072 : Nat := 747664803553532345303653

theorem tailTrace_1456072 : CollatzResearch.WordTrace tailWord_1456072 prefixEnd_1456072 747664803553532345303653 := by
  unfold tailWord_1456072
  simp only [CollatzResearch.WordTrace]
  refine ⟨26553654390453648072249235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35404872520604864096332313 26553654390453648072249235)
  ·
    refine ⟨39830481585680472108373853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26553654390453648072249235 39830481585680472108373853)
    ·
      refine ⟨14936430594630177040640195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39830481585680472108373853 14936430594630177040640195)
      ·
        refine ⟨22404645891945265560960293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14936430594630177040640195 22404645891945265560960293)
        ·
          refine ⟨4200871104739737292680055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22404645891945265560960293 4200871104739737292680055)
          ·
            refine ⟨6301306657109605939020083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4200871104739737292680055 6301306657109605939020083)
            ·
              refine ⟨9451959985664408908530125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6301306657109605939020083 9451959985664408908530125)
              ·
                refine ⟨3544484994624153340698797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9451959985664408908530125 3544484994624153340698797)
                ·
                  refine ⟨1329181872984057502762049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3544484994624153340698797 1329181872984057502762049)
                  ·
                    refine ⟨996886404738043127071537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1329181872984057502762049 996886404738043127071537)
                    ·
                      refine ⟨747664803553532345303653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 996886404738043127071537 747664803553532345303653)
                      ·
                        rfl

theorem cell23_1456072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 3, 3, 2, 2].length) (baseStart_1456072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456072 prefixEnd_1456072 := by exact prefixLift 1456072
  have htrace : WordTrace (prefixWord ++ tailWord_1456072) baseStart_1456072 baseEnd_1456072 := by
    simpa [prefixWord, tailWord_1456072, baseEnd_1456072] using wordTrace_append hprefix tailTrace_1456072
  have hstable : (prefixWord ++ tailWord_1456072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456072).length < 2 ^ (prefixWord ++ tailWord_1456072).sum := by decide
  have hdescent : baseEnd_1456072 < baseStart_1456072 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456081 : List Nat := [1, 2, 2, 1, 2, 1, 2, 1, 1, 4, 6]
def baseStart_1456081 : Nat := 118140960795 + 1456081 * 2 ^ 59
def prefixEnd_1456081 : Nat := 4983230072969 + 3 ^ 40 * 1456081 * 2
def baseEnd_1456081 : Nat := 747669424879422810091111

theorem tailTrace_1456081 : CollatzResearch.WordTrace tailWord_1456081 prefixEnd_1456081 747669424879422810091111 := by
  unfold tailWord_1456081
  simp only [CollatzResearch.WordTrace]
  refine ⟨53107637037874690681576097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35405091358583127121050731 53107637037874690681576097)
  ·
    refine ⟨39830727778406018011182073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53107637037874690681576097 39830727778406018011182073)
    ·
      refine ⟨29873045833804513508386555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39830727778406018011182073 29873045833804513508386555)
      ·
        refine ⟨44809568750706770262579833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29873045833804513508386555 44809568750706770262579833)
        ·
          refine ⟨33607176563030077696934875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44809568750706770262579833 33607176563030077696934875)
          ·
            refine ⟨50410764844545116545402313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33607176563030077696934875 50410764844545116545402313)
            ·
              refine ⟨37808073633408837409051735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50410764844545116545402313 37808073633408837409051735)
              ·
                refine ⟨56712110450113256113577603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37808073633408837409051735 56712110450113256113577603)
                ·
                  refine ⟨85068165675169884170366405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 56712110450113256113577603 85068165675169884170366405)
                  ·
                    refine ⟨15950281064094353281943701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85068165675169884170366405 15950281064094353281943701)
                    ·
                      refine ⟨747669424879422810091111, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15950281064094353281943701 747669424879422810091111)
                      ·
                        rfl

theorem cell23_1456081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_1456081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456081 prefixEnd_1456081 := by exact prefixLift 1456081
  have htrace : WordTrace (prefixWord ++ tailWord_1456081) baseStart_1456081 baseEnd_1456081 := by
    simpa [prefixWord, tailWord_1456081, baseEnd_1456081] using wordTrace_append hprefix tailTrace_1456081
  have hstable : (prefixWord ++ tailWord_1456081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456081).length < 2 ^ (prefixWord ++ tailWord_1456081).sum := by decide
  have hdescent : baseEnd_1456081 < baseStart_1456081 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456082 : List Nat := [3, 2, 2, 3, 2, 2, 1, 1, 1, 6]
def baseStart_1456082 : Nat := 118140960795 + 1456082 * 2 ^ 59
def prefixEnd_1456082 : Nat := 4983230072969 + 3 ^ 40 * 1456082 * 2
def baseEnd_1456082 : Nat := 249223312786692435392869

theorem tailTrace_1456082 : CollatzResearch.WordTrace tailWord_1456082 prefixEnd_1456082 249223312786692435392869 := by
  unfold tailWord_1456082
  simp only [CollatzResearch.WordTrace]
  refine ⟨13276918377717766963090625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35405115673914045234908333 13276918377717766963090625)
  ·
    refine ⟨9957688783288325222317969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13276918377717766963090625 9957688783288325222317969)
    ·
      refine ⟨7468266587466243916738477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9957688783288325222317969 7468266587466243916738477)
      ·
        refine ⟨2800599970299841468776929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7468266587466243916738477 2800599970299841468776929)
        ·
          refine ⟨2100449977724881101582697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2800599970299841468776929 2100449977724881101582697)
          ·
            refine ⟨1575337483293660826187023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2100449977724881101582697 1575337483293660826187023)
            ·
              refine ⟨2363006224940491239280535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1575337483293660826187023 2363006224940491239280535)
              ·
                refine ⟨3544509337410736858920803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2363006224940491239280535 3544509337410736858920803)
                ·
                  refine ⟨5316764006116105288381205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3544509337410736858920803 5316764006116105288381205)
                  ·
                    refine ⟨249223312786692435392869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5316764006116105288381205 249223312786692435392869)
                    ·
                      rfl

theorem cell23_1456082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_1456082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456082 prefixEnd_1456082 := by exact prefixLift 1456082
  have htrace : WordTrace (prefixWord ++ tailWord_1456082) baseStart_1456082 baseEnd_1456082 := by
    simpa [prefixWord, tailWord_1456082, baseEnd_1456082] using wordTrace_append hprefix tailTrace_1456082
  have hstable : (prefixWord ++ tailWord_1456082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456082).length < 2 ^ (prefixWord ++ tailWord_1456082).sum := by decide
  have hdescent : baseEnd_1456082 < baseStart_1456082 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456085 : List Nat := [1, 3, 2, 3, 2, 1, 3, 1, 1, 2, 4]
def baseStart_1456085 : Nat := 118140960795 + 1456085 * 2 ^ 59
def prefixEnd_1456085 : Nat := 4983230072969 + 3 ^ 40 * 1456085 * 2
def baseEnd_1456085 : Nat := 747671478802040794441093

theorem tailTrace_1456085 : CollatzResearch.WordTrace tailWord_1456085 prefixEnd_1456085 747671478802040794441093 := by
  unfold tailWord_1456085
  simp only [CollatzResearch.WordTrace]
  refine ⟨53107782929860199364721709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35405188619906799576481139 53107782929860199364721709)
  ·
    refine ⟨19915418598697574761770641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53107782929860199364721709 19915418598697574761770641)
    ·
      refine ⟨14936563949023181071327981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19915418598697574761770641 14936563949023181071327981)
      ·
        refine ⟨5601211480883692901747993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14936563949023181071327981 5601211480883692901747993)
        ·
          refine ⟨4200908610662769676310995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5601211480883692901747993 4200908610662769676310995)
          ·
            refine ⟨6301362915994154514466493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4200908610662769676310995 6301362915994154514466493)
            ·
              refine ⟨2363011093497807942924935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6301362915994154514466493 2363011093497807942924935)
              ·
                refine ⟨3544516640246711914387403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2363011093497807942924935 3544516640246711914387403)
                ·
                  refine ⟨5316774960370067871581105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3544516640246711914387403 5316774960370067871581105)
                  ·
                    refine ⟨3987581220277550903685829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5316774960370067871581105 3987581220277550903685829)
                    ·
                      refine ⟨747671478802040794441093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3987581220277550903685829 747671478802040794441093)
                      ·
                        rfl

theorem cell23_1456085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 3, 1, 1, 2, 4].length) (baseStart_1456085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456085 prefixEnd_1456085 := by exact prefixLift 1456085
  have htrace : WordTrace (prefixWord ++ tailWord_1456085) baseStart_1456085 baseEnd_1456085 := by
    simpa [prefixWord, tailWord_1456085, baseEnd_1456085] using wordTrace_append hprefix tailTrace_1456085
  have hstable : (prefixWord ++ tailWord_1456085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456085).length < 2 ^ (prefixWord ++ tailWord_1456085).sum := by decide
  have hdescent : baseEnd_1456085 < baseStart_1456085 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456095 : List Nat := [1, 1, 2, 3, 4, 3, 2, 7]
def baseStart_1456095 : Nat := 118140960795 + 1456095 * 2 ^ 59
def prefixEnd_1456095 : Nat := 4983230072969 + 3 ^ 40 * 1456095 * 2
def baseEnd_1456095 : Nat := 27691726429947620567261

theorem tailTrace_1456095 : CollatzResearch.WordTrace tailWord_1456095 prefixEnd_1456095 27691726429947620567261 := by
  unfold tailWord_1456095
  simp only [CollatzResearch.WordTrace]
  refine ⟨53108147659823971072585739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35405431773215980715057159 53108147659823971072585739)
  ·
    refine ⟨79662221489735956608878609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53108147659823971072585739 79662221489735956608878609)
    ·
      refine ⟨59746666117301967456658957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79662221489735956608878609 59746666117301967456658957)
      ·
        refine ⟨22404999793988237796247109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59746666117301967456658957 22404999793988237796247109)
        ·
          refine ⟨4200937461372794586796333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22404999793988237796247109 4200937461372794586796333)
          ·
            refine ⟨1575351548014797970048625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4200937461372794586796333 1575351548014797970048625)
            ·
              refine ⟨1181513661011098477536469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1575351548014797970048625 1181513661011098477536469)
              ·
                refine ⟨27691726429947620567261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1181513661011098477536469 27691726429947620567261)
                ·
                  rfl

theorem cell23_1456095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 3, 2, 7].length) (baseStart_1456095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456095 prefixEnd_1456095 := by exact prefixLift 1456095
  have htrace : WordTrace (prefixWord ++ tailWord_1456095) baseStart_1456095 baseEnd_1456095 := by
    simpa [prefixWord, tailWord_1456095, baseEnd_1456095] using wordTrace_append hprefix tailTrace_1456095
  have hstable : (prefixWord ++ tailWord_1456095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456095).length < 2 ^ (prefixWord ++ tailWord_1456095).sum := by decide
  have hdescent : baseEnd_1456095 < baseStart_1456095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456162 : List Nat := [3, 3, 1, 1, 1, 2, 3, 2, 1, 4, 2]
def baseStart_1456162 : Nat := 118140960795 + 1456162 * 2 ^ 59
def prefixEnd_1456162 : Nat := 4983230072969 + 3 ^ 40 * 1456162 * 2
def baseEnd_1456162 : Nat := 747711016812436993178239

theorem tailTrace_1456162 : CollatzResearch.WordTrace tailWord_1456162 prefixEnd_1456162 747711016812436993178239 := by
  unfold tailWord_1456162
  simp only [CollatzResearch.WordTrace]
  refine ⟨13277647837645310378818685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35407060900387494343516493 13277647837645310378818685)
  ·
    refine ⟨4979117939116991392057007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13277647837645310378818685 4979117939116991392057007)
    ·
      refine ⟨7468676908675487088085511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4979117939116991392057007 7468676908675487088085511)
      ·
        refine ⟨11203015363013230632128267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7468676908675487088085511 11203015363013230632128267)
        ·
          refine ⟨16804523044519845948192401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11203015363013230632128267 16804523044519845948192401)
          ·
            refine ⟨12603392283389884461144301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16804523044519845948192401 12603392283389884461144301)
            ·
              refine ⟨4726272106271206672929113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12603392283389884461144301 4726272106271206672929113)
              ·
                refine ⟨3544704079703405004696835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4726272106271206672929113 3544704079703405004696835)
                ·
                  refine ⟨5317056119555107507045253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3544704079703405004696835 5317056119555107507045253)
                  ·
                    refine ⟨996948022416582657570985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5317056119555107507045253 996948022416582657570985)
                    ·
                      refine ⟨747711016812436993178239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 996948022416582657570985 747711016812436993178239)
                      ·
                        rfl

theorem cell23_1456162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_1456162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456162 prefixEnd_1456162 := by exact prefixLift 1456162
  have htrace : WordTrace (prefixWord ++ tailWord_1456162) baseStart_1456162 baseEnd_1456162 := by
    simpa [prefixWord, tailWord_1456162, baseEnd_1456162] using wordTrace_append hprefix tailTrace_1456162
  have hstable : (prefixWord ++ tailWord_1456162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456162).length < 2 ^ (prefixWord ++ tailWord_1456162).sum := by decide
  have hdescent : baseEnd_1456162 < baseStart_1456162 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456215 : List Nat := [1, 1, 3, 2, 2, 1, 5, 1, 2, 5]
def baseStart_1456215 : Nat := 118140960795 + 1456215 * 2 ^ 59
def prefixEnd_1456215 : Nat := 4983230072969 + 3 ^ 40 * 1456215 * 2
def baseEnd_1456215 : Nat := 249246077095708428605165

theorem tailTrace_1456215 : CollatzResearch.WordTrace tailWord_1456215 prefixEnd_1456215 249246077095708428605165 := by
  unfold tailWord_1456215
  simp only [CollatzResearch.WordTrace]
  refine ⟨53112524419389231566954099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35408349612926154377969399 53112524419389231566954099)
  ·
    refine ⟨79668786629083847350431149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53112524419389231566954099 79668786629083847350431149)
    ·
      refine ⟨29875794985906442756411681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79668786629083847350431149 29875794985906442756411681)
      ·
        refine ⟨22406846239429832067308761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29875794985906442756411681 22406846239429832067308761)
        ·
          refine ⟨16805134679572374050481571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22406846239429832067308761 16805134679572374050481571)
          ·
            refine ⟨25207702019358561075722357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16805134679572374050481571 25207702019358561075722357)
            ·
              refine ⟨2363222064314865100848971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25207702019358561075722357 2363222064314865100848971)
              ·
                refine ⟨3544833096472297651273457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2363222064314865100848971 3544833096472297651273457)
                ·
                  refine ⟨2658624822354223238455093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3544833096472297651273457 2658624822354223238455093)
                  ·
                    refine ⟨249246077095708428605165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2658624822354223238455093 249246077095708428605165)
                    ·
                      rfl

theorem cell23_1456215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 5, 1, 2, 5].length) (baseStart_1456215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456215 prefixEnd_1456215 := by exact prefixLift 1456215
  have htrace : WordTrace (prefixWord ++ tailWord_1456215) baseStart_1456215 baseEnd_1456215 := by
    simpa [prefixWord, tailWord_1456215, baseEnd_1456215] using wordTrace_append hprefix tailTrace_1456215
  have hstable : (prefixWord ++ tailWord_1456215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456215).length < 2 ^ (prefixWord ++ tailWord_1456215).sum := by decide
  have hdescent : baseEnd_1456215 < baseStart_1456215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456248 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 4, 1, 6]
def baseStart_1456248 : Nat := 118140960795 + 1456248 * 2 ^ 59
def prefixEnd_1456248 : Nat := 4983230072969 + 3 ^ 40 * 1456248 * 2
def baseEnd_1456248 : Nat := 747755176148723656702843

theorem tailTrace_1456248 : CollatzResearch.WordTrace tailWord_1456248 prefixEnd_1456248 747755176148723656702843 := by
  unfold tailWord_1456248
  simp only [CollatzResearch.WordTrace]
  refine ⟨26556864014134839101452699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35409152018846452135270265 26556864014134839101452699)
  ·
    refine ⟨39835296021202258652179049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26556864014134839101452699 39835296021202258652179049)
    ·
      refine ⟨29876472015901693989134287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39835296021202258652179049 29876472015901693989134287)
      ·
        refine ⟨44814708023852540983701431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29876472015901693989134287 44814708023852540983701431)
        ·
          refine ⟨67222062035778811475552147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44814708023852540983701431 67222062035778811475552147)
          ·
            refine ⟨100833093053668217213328221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67222062035778811475552147 100833093053668217213328221)
            ·
              refine ⟨37812409895125581454998083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 100833093053668217213328221 37812409895125581454998083)
              ·
                refine ⟨56718614842688372182497125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37812409895125581454998083 56718614842688372182497125)
                ·
                  refine ⟨10634740283004069784218211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56718614842688372182497125 10634740283004069784218211)
                  ·
                    refine ⟨15952110424506104676327317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10634740283004069784218211 15952110424506104676327317)
                    ·
                      refine ⟨747755176148723656702843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15952110424506104676327317 747755176148723656702843)
                      ·
                        rfl

theorem cell23_1456248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_1456248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456248 prefixEnd_1456248 := by exact prefixLift 1456248
  have htrace : WordTrace (prefixWord ++ tailWord_1456248) baseStart_1456248 baseEnd_1456248 := by
    simpa [prefixWord, tailWord_1456248, baseEnd_1456248] using wordTrace_append hprefix tailTrace_1456248
  have hstable : (prefixWord ++ tailWord_1456248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456248).length < 2 ^ (prefixWord ++ tailWord_1456248).sum := by decide
  have hdescent : baseEnd_1456248 < baseStart_1456248 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456252 : List Nat := [2, 2, 2, 1, 1, 4, 2, 1, 2, 4, 2]
def baseStart_1456252 : Nat := 118140960795 + 1456252 * 2 ^ 59
def prefixEnd_1456252 : Nat := 4983230072969 + 3 ^ 40 * 1456252 * 2
def baseEnd_1456252 : Nat := 747757230071341641052825

theorem tailTrace_1456252 : CollatzResearch.WordTrace tailWord_1456252 prefixEnd_1456252 747757230071341641052825 := by
  unfold tailWord_1456252
  simp only [CollatzResearch.WordTrace]
  refine ⟨26556936960127593443025505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35409249280170124590700673 26556936960127593443025505)
  ·
    refine ⟨19917702720095695082269129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26556936960127593443025505 19917702720095695082269129)
    ·
      refine ⟨14938277040071771311701847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19917702720095695082269129 14938277040071771311701847)
      ·
        refine ⟨22407415560107656967552771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14938277040071771311701847 22407415560107656967552771)
        ·
          refine ⟨33611123340161485451329157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22407415560107656967552771 33611123340161485451329157)
          ·
            refine ⟨6302085626280278522124217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33611123340161485451329157 6302085626280278522124217)
            ·
              refine ⟨4726564219710208891593163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6302085626280278522124217 4726564219710208891593163)
              ·
                refine ⟨7089846329565313337389745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4726564219710208891593163 7089846329565313337389745)
                ·
                  refine ⟨5317384747173985003042309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7089846329565313337389745 5317384747173985003042309)
                  ·
                    refine ⟨997009640095122188070433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5317384747173985003042309 997009640095122188070433)
                    ·
                      refine ⟨747757230071341641052825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 997009640095122188070433 747757230071341641052825)
                      ·
                        rfl

theorem cell23_1456252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 2, 1, 2, 4, 2].length) (baseStart_1456252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456252 prefixEnd_1456252 := by exact prefixLift 1456252
  have htrace : WordTrace (prefixWord ++ tailWord_1456252) baseStart_1456252 baseEnd_1456252 := by
    simpa [prefixWord, tailWord_1456252, baseEnd_1456252] using wordTrace_append hprefix tailTrace_1456252
  have hstable : (prefixWord ++ tailWord_1456252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456252).length < 2 ^ (prefixWord ++ tailWord_1456252).sum := by decide
  have hdescent : baseEnd_1456252 < baseStart_1456252 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456268 : List Nat := [2, 2, 1, 2, 1, 1, 1, 1, 2, 1, 9]
def baseStart_1456268 : Nat := 118140960795 + 1456268 * 2 ^ 59
def prefixEnd_1456268 : Nat := 4983230072969 + 3 ^ 40 * 1456268 * 2
def baseEnd_1456268 : Nat := 747765445761813578452751

theorem tailTrace_1456268 : CollatzResearch.WordTrace tailWord_1456268 prefixEnd_1456268 747765445761813578452751 := by
  unfold tailWord_1456268
  simp only [CollatzResearch.WordTrace]
  refine ⟨26557228744098610809316729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35409638325464814412422305 26557228744098610809316729)
  ·
    refine ⟨19917921558073958106987547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26557228744098610809316729 19917921558073958106987547)
    ·
      refine ⟨29876882337110937160481321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19917921558073958106987547 29876882337110937160481321)
      ·
        refine ⟨22407661752833202870360991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29876882337110937160481321 22407661752833202870360991)
        ·
          refine ⟨33611492629249804305541487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22407661752833202870360991 33611492629249804305541487)
          ·
            refine ⟨50417238943874706458312231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33611492629249804305541487 50417238943874706458312231)
            ·
              refine ⟨75625858415812059687468347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50417238943874706458312231 75625858415812059687468347)
              ·
                refine ⟨113438787623718089531202521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75625858415812059687468347 113438787623718089531202521)
                ·
                  refine ⟨85079090717788567148401891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 113438787623718089531202521 85079090717788567148401891)
                  ·
                    refine ⟨127618636076682850722602837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85079090717788567148401891 127618636076682850722602837)
                    ·
                      refine ⟨747765445761813578452751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 127618636076682850722602837 747765445761813578452751)
                      ·
                        rfl

theorem cell23_1456268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_1456268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456268 prefixEnd_1456268 := by exact prefixLift 1456268
  have htrace : WordTrace (prefixWord ++ tailWord_1456268) baseStart_1456268 baseEnd_1456268 := by
    simpa [prefixWord, tailWord_1456268, baseEnd_1456268] using wordTrace_append hprefix tailTrace_1456268
  have hstable : (prefixWord ++ tailWord_1456268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456268).length < 2 ^ (prefixWord ++ tailWord_1456268).sum := by decide
  have hdescent : baseEnd_1456268 < baseStart_1456268 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456309 : List Nat := [1, 3, 3, 4, 1, 1, 1, 3, 6]
def baseStart_1456309 : Nat := 118140960795 + 1456309 * 2 ^ 59
def prefixEnd_1456309 : Nat := 4983230072969 + 3 ^ 40 * 1456309 * 2
def baseEnd_1456309 : Nat := 83087388718738657560007

theorem tailTrace_1456309 : CollatzResearch.WordTrace tailWord_1456309 prefixEnd_1456309 83087388718738657560007 := by
  unfold tailWord_1456309
  simp only [CollatzResearch.WordTrace]
  refine ⟨53115952881048685620875981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35410635254032457080583987 53115952881048685620875981)
  ·
    refine ⟨19918482330393257107828493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53115952881048685620875981 19918482330393257107828493)
    ·
      refine ⟨7469430873897471415435685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19918482330393257107828493 7469430873897471415435685)
      ·
        refine ⟨1400518288855775890394191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7469430873897471415435685 1400518288855775890394191)
        ·
          refine ⟨2100777433283663835591287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1400518288855775890394191 2100777433283663835591287)
          ·
            refine ⟨3151166149925495753386931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2100777433283663835591287 3151166149925495753386931)
            ·
              refine ⟨4726749224888243630080397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3151166149925495753386931 4726749224888243630080397)
              ·
                refine ⟨1772530959333091361280149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4726749224888243630080397 1772530959333091361280149)
                ·
                  refine ⟨83087388718738657560007, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1772530959333091361280149 83087388718738657560007)
                  ·
                    rfl

theorem cell23_1456309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 1, 1, 1, 3, 6].length) (baseStart_1456309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456309 prefixEnd_1456309 := by exact prefixLift 1456309
  have htrace : WordTrace (prefixWord ++ tailWord_1456309) baseStart_1456309 baseEnd_1456309 := by
    simpa [prefixWord, tailWord_1456309, baseEnd_1456309] using wordTrace_append hprefix tailTrace_1456309
  have hstable : (prefixWord ++ tailWord_1456309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456309).length < 2 ^ (prefixWord ++ tailWord_1456309).sum := by decide
  have hdescent : baseEnd_1456309 < baseStart_1456309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456312 : List Nat := [2, 1, 2, 1, 2, 1, 3, 2, 4, 3, 2]
def baseStart_1456312 : Nat := 118140960795 + 1456312 * 2 ^ 59
def prefixEnd_1456312 : Nat := 4983230072969 + 3 ^ 40 * 1456312 * 2
def baseEnd_1456312 : Nat := 747788038910611406302549

theorem tailTrace_1456312 : CollatzResearch.WordTrace tailWord_1456312 prefixEnd_1456312 747788038910611406302549 := by
  unfold tailWord_1456312
  simp only [CollatzResearch.WordTrace]
  refine ⟨26558031150018908566617595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35410708200025211422156793 26558031150018908566617595)
  ·
    refine ⟨39837046725028362849926393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26558031150018908566617595 39837046725028362849926393)
    ·
      refine ⟨29877785043771272137444795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39837046725028362849926393 29877785043771272137444795)
      ·
        refine ⟨44816677565656908206167193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29877785043771272137444795 44816677565656908206167193)
        ·
          refine ⟨33612508174242681154625395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44816677565656908206167193 33612508174242681154625395)
          ·
            refine ⟨50418762261364021731938093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33612508174242681154625395 50418762261364021731938093)
            ·
              refine ⟨18907035848011508149476785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50418762261364021731938093 18907035848011508149476785)
              ·
                refine ⟨14180276886008631112107589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18907035848011508149476785 14180276886008631112107589)
                ·
                  refine ⟨2658801916126618333520173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14180276886008631112107589 2658801916126618333520173)
                  ·
                    refine ⟨997050718547481875070065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2658801916126618333520173 997050718547481875070065)
                    ·
                      refine ⟨747788038910611406302549, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 997050718547481875070065 747788038910611406302549)
                      ·
                        rfl

theorem cell23_1456312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 2, 4, 3, 2].length) (baseStart_1456312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456312 prefixEnd_1456312 := by exact prefixLift 1456312
  have htrace : WordTrace (prefixWord ++ tailWord_1456312) baseStart_1456312 baseEnd_1456312 := by
    simpa [prefixWord, tailWord_1456312, baseEnd_1456312] using wordTrace_append hprefix tailTrace_1456312
  have hstable : (prefixWord ++ tailWord_1456312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456312).length < 2 ^ (prefixWord ++ tailWord_1456312).sum := by decide
  have hdescent : baseEnd_1456312 < baseStart_1456312 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456335 : List Nat := [1, 1, 2, 1, 1, 3, 5, 2, 1, 6]
def baseStart_1456335 : Nat := 118140960795 + 1456335 * 2 ^ 59
def prefixEnd_1456335 : Nat := 4983230072969 + 3 ^ 40 * 1456335 * 2
def baseEnd_1456335 : Nat := 249266616321888272104981

theorem tailTrace_1456335 : CollatzResearch.WordTrace tailWord_1456335 prefixEnd_1456335 249266616321888272104981 := by
  unfold tailWord_1456335
  simp only [CollatzResearch.WordTrace]
  refine ⟨53116901178954492061322459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35411267452636328040881639 53116901178954492061322459)
  ·
    refine ⟨79675351768431738091983689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53116901178954492061322459 79675351768431738091983689)
    ·
      refine ⟨59756513826323803568987767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79675351768431738091983689 59756513826323803568987767)
      ·
        refine ⟨89634770739485705353481651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59756513826323803568987767 89634770739485705353481651)
        ·
          refine ⟨134452156109228558030222477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89634770739485705353481651 134452156109228558030222477)
          ·
            refine ⟨50419558540960709261333429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134452156109228558030222477 50419558540960709261333429)
            ·
              refine ⟨4726833613215066493250009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50419558540960709261333429 4726833613215066493250009)
              ·
                refine ⟨3545125209911299869937507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4726833613215066493250009 3545125209911299869937507)
                ·
                  refine ⟨5317687814866949804906261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3545125209911299869937507 5317687814866949804906261)
                  ·
                    refine ⟨249266616321888272104981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5317687814866949804906261 249266616321888272104981)
                    ·
                      rfl

theorem cell23_1456335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 5, 2, 1, 6].length) (baseStart_1456335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456335 prefixEnd_1456335 := by exact prefixLift 1456335
  have htrace : WordTrace (prefixWord ++ tailWord_1456335) baseStart_1456335 baseEnd_1456335 := by
    simpa [prefixWord, tailWord_1456335, baseEnd_1456335] using wordTrace_append hprefix tailTrace_1456335
  have hstable : (prefixWord ++ tailWord_1456335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456335).length < 2 ^ (prefixWord ++ tailWord_1456335).sum := by decide
  have hdescent : baseEnd_1456335 < baseStart_1456335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456362 : List Nat := [3, 1, 3, 1, 1, 2, 1, 1, 5, 2, 3]
def baseStart_1456362 : Nat := 118140960795 + 1456362 * 2 ^ 59
def prefixEnd_1456362 : Nat := 4983230072969 + 3 ^ 40 * 1456362 * 2
def baseEnd_1456362 : Nat := 747813712943336210677319

theorem tailTrace_1456362 : CollatzResearch.WordTrace tailWord_1456362 prefixEnd_1456362 747813712943336210677319 := by
  unfold tailWord_1456362
  simp only [CollatzResearch.WordTrace]
  refine ⟨13279471487464168918138835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35411923966571117115036893 13279471487464168918138835)
  ·
    refine ⟨19919207231196253377208253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13279471487464168918138835 19919207231196253377208253)
    ·
      refine ⟨7469702711698595016453095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19919207231196253377208253 7469702711698595016453095)
      ·
        refine ⟨11204554067547892524679643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7469702711698595016453095 11204554067547892524679643)
        ·
          refine ⟨16806831101321838787019465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11204554067547892524679643 16806831101321838787019465)
          ·
            refine ⟨12605123325991379090264599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16806831101321838787019465 12605123325991379090264599)
            ·
              refine ⟨18907684988987068635396899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12605123325991379090264599 18907684988987068635396899)
              ·
                refine ⟨28361527483480602953095349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18907684988987068635396899 28361527483480602953095349)
                ·
                  refine ⟨2658893201576306526852689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28361527483480602953095349 2658893201576306526852689)
                  ·
                    refine ⟨1994169901182229895139517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2658893201576306526852689 1994169901182229895139517)
                    ·
                      refine ⟨747813712943336210677319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1994169901182229895139517 747813712943336210677319)
                      ·
                        rfl

theorem cell23_1456362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 1, 1, 5, 2, 3].length) (baseStart_1456362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456362 prefixEnd_1456362 := by exact prefixLift 1456362
  have htrace : WordTrace (prefixWord ++ tailWord_1456362) baseStart_1456362 baseEnd_1456362 := by
    simpa [prefixWord, tailWord_1456362, baseEnd_1456362] using wordTrace_append hprefix tailTrace_1456362
  have hstable : (prefixWord ++ tailWord_1456362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456362).length < 2 ^ (prefixWord ++ tailWord_1456362).sum := by decide
  have hdescent : baseEnd_1456362 < baseStart_1456362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456393 : List Nat := [1, 2, 1, 1, 3, 5, 2, 3, 1, 2, 2]
def baseStart_1456393 : Nat := 118140960795 + 1456393 * 2 ^ 59
def prefixEnd_1456393 : Nat := 4983230072969 + 3 ^ 40 * 1456393 * 2
def baseEnd_1456393 : Nat := 747829630843625589389677

theorem tailTrace_1456393 : CollatzResearch.WordTrace tailWord_1456393 prefixEnd_1456393 747829630843625589389677 := by
  unfold tailWord_1456393
  simp only [CollatzResearch.WordTrace]
  refine ⟨53119016612744367966933833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35412677741829578644622555 53119016612744367966933833)
  ·
    refine ⟨39839262459558275975200375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53119016612744367966933833 39839262459558275975200375)
    ·
      refine ⟨59758893689337413962800563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39839262459558275975200375 59758893689337413962800563)
      ·
        refine ⟨89638340534006120944200845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59758893689337413962800563 89638340534006120944200845)
        ·
          refine ⟨33614377700252295354075317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89638340534006120944200845 33614377700252295354075317)
          ·
            refine ⟨3151347909398652689444561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33614377700252295354075317 3151347909398652689444561)
            ·
              refine ⟨2363510932048989517083421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3151347909398652689444561 2363510932048989517083421)
              ·
                refine ⟨886316599518371068906283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2363510932048989517083421 886316599518371068906283)
                ·
                  refine ⟨1329474899277556603359425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 886316599518371068906283 1329474899277556603359425)
                  ·
                    refine ⟨997106174458167452519569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1329474899277556603359425 997106174458167452519569)
                    ·
                      refine ⟨747829630843625589389677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 997106174458167452519569 747829630843625589389677)
                      ·
                        rfl

theorem cell23_1456393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 3, 1, 2, 2].length) (baseStart_1456393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456393 prefixEnd_1456393 := by exact prefixLift 1456393
  have htrace : WordTrace (prefixWord ++ tailWord_1456393) baseStart_1456393 baseEnd_1456393 := by
    simpa [prefixWord, tailWord_1456393, baseEnd_1456393] using wordTrace_append hprefix tailTrace_1456393
  have hstable : (prefixWord ++ tailWord_1456393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456393).length < 2 ^ (prefixWord ++ tailWord_1456393).sum := by decide
  have hdescent : baseEnd_1456393 < baseStart_1456393 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456462 : List Nat := [4, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4]
def baseStart_1456462 : Nat := 118140960795 + 1456462 * 2 ^ 59
def prefixEnd_1456462 : Nat := 4983230072969 + 3 ^ 40 * 1456462 * 2
def baseEnd_1456462 : Nat := 747865061008785819426859

theorem tailTrace_1456462 : CollatzResearch.WordTrace tailWord_1456462 prefixEnd_1456462 747865061008785819426859 := by
  unfold tailWord_1456462
  simp only [CollatzResearch.WordTrace]
  refine ⟨6640191656186799093899455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35414355499662928500797093 6640191656186799093899455)
  ·
    refine ⟨9960287484280198640849183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6640191656186799093899455 9960287484280198640849183)
    ·
      refine ⟨14940431226420297961273775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9960287484280198640849183 14940431226420297961273775)
      ·
        refine ⟨22410646839630446941910663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14940431226420297961273775 22410646839630446941910663)
        ·
          refine ⟨33615970259445670412865995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22410646839630446941910663 33615970259445670412865995)
          ·
            refine ⟨50423955389168505619298993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33615970259445670412865995 50423955389168505619298993)
            ·
              refine ⟨37817966541876379214474245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50423955389168505619298993 37817966541876379214474245)
              ·
                refine ⟨7090868726601821102713921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37817966541876379214474245 7090868726601821102713921)
                ·
                  refine ⟨5318151544951365827035441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7090868726601821102713921 5318151544951365827035441)
                  ·
                    refine ⟨3988613658713524370276581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5318151544951365827035441 3988613658713524370276581)
                    ·
                      refine ⟨747865061008785819426859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3988613658713524370276581 747865061008785819426859)
                      ·
                        rfl

theorem cell23_1456462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 4, 2, 2, 4].length) (baseStart_1456462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456462 prefixEnd_1456462 := by exact prefixLift 1456462
  have htrace : WordTrace (prefixWord ++ tailWord_1456462) baseStart_1456462 baseEnd_1456462 := by
    simpa [prefixWord, tailWord_1456462, baseEnd_1456462] using wordTrace_append hprefix tailTrace_1456462
  have hstable : (prefixWord ++ tailWord_1456462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456462).length < 2 ^ (prefixWord ++ tailWord_1456462).sum := by decide
  have hdescent : baseEnd_1456462 < baseStart_1456462 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456466 : List Nat := [3, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2]
def baseStart_1456466 : Nat := 118140960795 + 1456466 * 2 ^ 59
def prefixEnd_1456466 : Nat := 4983230072969 + 3 ^ 40 * 1456466 * 2
def baseEnd_1456466 : Nat := 747867114931403803776841

theorem tailTrace_1456466 : CollatzResearch.WordTrace tailWord_1456466 prefixEnd_1456466 747867114931403803776841 := by
  unfold tailWord_1456466
  simp only [CollatzResearch.WordTrace]
  refine ⟨13280419785369975358585313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35414452760986600956227501 13280419785369975358585313)
  ·
    refine ⟨9960314839027481518938985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13280419785369975358585313 9960314839027481518938985)
    ·
      refine ⟨7470236129270611139204239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9960314839027481518938985 7470236129270611139204239)
      ·
        refine ⟨11205354193905916708806359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7470236129270611139204239 11205354193905916708806359)
        ·
          refine ⟨16808031290858875063209539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11205354193905916708806359 16808031290858875063209539)
          ·
            refine ⟨25212046936288312594814309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16808031290858875063209539 25212046936288312594814309)
            ·
              refine ⟨4727258800554058611527683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25212046936288312594814309 4727258800554058611527683)
              ·
                refine ⟨7090888200831087917291525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4727258800554058611527683 7090888200831087917291525)
                ·
                  refine ⟨1329541537655828984492161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7090888200831087917291525 1329541537655828984492161)
                  ·
                    refine ⟨997156153241871738369121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1329541537655828984492161 997156153241871738369121)
                    ·
                      refine ⟨747867114931403803776841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 997156153241871738369121 747867114931403803776841)
                      ·
                        rfl

theorem cell23_1456466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_1456466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456466 prefixEnd_1456466 := by exact prefixLift 1456466
  have htrace : WordTrace (prefixWord ++ tailWord_1456466) baseStart_1456466 baseEnd_1456466 := by
    simpa [prefixWord, tailWord_1456466, baseEnd_1456466] using wordTrace_append hprefix tailTrace_1456466
  have hstable : (prefixWord ++ tailWord_1456466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456466).length < 2 ^ (prefixWord ++ tailWord_1456466).sum := by decide
  have hdescent : baseEnd_1456466 < baseStart_1456466 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456526 : List Nat := [4, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2]
def baseStart_1456526 : Nat := 118140960795 + 1456526 * 2 ^ 59
def prefixEnd_1456526 : Nat := 4983230072969 + 3 ^ 40 * 1456526 * 2
def baseEnd_1456526 : Nat := 747897923770673569026565

theorem tailTrace_1456526 : CollatzResearch.WordTrace tailWord_1456526 prefixEnd_1456526 747897923770673569026565 := by
  unfold tailWord_1456526
  simp only [CollatzResearch.WordTrace]
  refine ⟨6640483440157816460190679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35415911680841687787683621 6640483440157816460190679)
  ·
    refine ⟨9960725160236724690286019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6640483440157816460190679 9960725160236724690286019)
    ·
      refine ⟨14941087740355087035429029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9960725160236724690286019 14941087740355087035429029)
      ·
        refine ⟨2801453951316578819142943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14941087740355087035429029 2801453951316578819142943)
        ·
          refine ⟨4202180926974868228714415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2801453951316578819142943 4202180926974868228714415)
          ·
            refine ⟨6303271390462302343071623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4202180926974868228714415 6303271390462302343071623)
            ·
              refine ⟨9454907085693453514607435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6303271390462302343071623 9454907085693453514607435)
              ·
                refine ⟨14182360628540180271911153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9454907085693453514607435 14182360628540180271911153)
                ·
                  refine ⟨10636770471405135203933365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14182360628540180271911153 10636770471405135203933365)
                  ·
                    refine ⟨997197231694231425368753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10636770471405135203933365 997197231694231425368753)
                    ·
                      refine ⟨747897923770673569026565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 997197231694231425368753 747897923770673569026565)
                      ·
                        rfl

theorem cell23_1456526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_1456526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456526 prefixEnd_1456526 := by exact prefixLift 1456526
  have htrace : WordTrace (prefixWord ++ tailWord_1456526) baseStart_1456526 baseEnd_1456526 := by
    simpa [prefixWord, tailWord_1456526, baseEnd_1456526] using wordTrace_append hprefix tailTrace_1456526
  have hstable : (prefixWord ++ tailWord_1456526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456526).length < 2 ^ (prefixWord ++ tailWord_1456526).sum := by decide
  have hdescent : baseEnd_1456526 < baseStart_1456526 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456549 : List Nat := [1, 3, 1, 2, 1, 1, 5, 2, 3, 4]
def baseStart_1456549 : Nat := 118140960795 + 1456549 * 2 ^ 59
def prefixEnd_1456549 : Nat := 4983230072969 + 3 ^ 40 * 1456549 * 2
def baseEnd_1456549 : Nat := 249303244608575659679653

theorem tailTrace_1456549 : CollatzResearch.WordTrace tailWord_1456549 prefixEnd_1456549 249303244608575659679653 := by
  unfold tailWord_1456549
  simp only [CollatzResearch.WordTrace]
  refine ⟨53124706400179206609612701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35416470933452804406408467 53124706400179206609612701)
  ·
    refine ⟨19921764900067202478604763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53124706400179206609612701 19921764900067202478604763)
    ·
      refine ⟨29882647350100803717907145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19921764900067202478604763 29882647350100803717907145)
      ·
        refine ⟨22411985512575602788430359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29882647350100803717907145 22411985512575602788430359)
        ·
          refine ⟨33617978268863404182645539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22411985512575602788430359 33617978268863404182645539)
          ·
            refine ⟨50426967403295106273968309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33617978268863404182645539 50426967403295106273968309)
            ·
              refine ⟨4727528194058916213184529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50426967403295106273968309 4727528194058916213184529)
              ·
                refine ⟨3545646145544187159888397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4727528194058916213184529 3545646145544187159888397)
                ·
                  refine ⟨1329617304579070184958149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3545646145544187159888397 1329617304579070184958149)
                  ·
                    refine ⟨249303244608575659679653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1329617304579070184958149 249303244608575659679653)
                    ·
                      rfl

theorem cell23_1456549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 5, 2, 3, 4].length) (baseStart_1456549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456549 prefixEnd_1456549 := by exact prefixLift 1456549
  have htrace : WordTrace (prefixWord ++ tailWord_1456549) baseStart_1456549 baseEnd_1456549 := by
    simpa [prefixWord, tailWord_1456549, baseEnd_1456549] using wordTrace_append hprefix tailTrace_1456549
  have hstable : (prefixWord ++ tailWord_1456549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456549).length < 2 ^ (prefixWord ++ tailWord_1456549).sum := by decide
  have hdescent : baseEnd_1456549 < baseStart_1456549 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456562 : List Nat := [3, 2, 1, 1, 1, 1, 4, 2, 8]
def baseStart_1456562 : Nat := 118140960795 + 1456562 * 2 ^ 59
def prefixEnd_1456562 : Nat := 4983230072969 + 3 ^ 40 * 1456562 * 2
def baseEnd_1456562 : Nat := 83101823230470603130711

theorem tailTrace_1456562 : CollatzResearch.WordTrace tailWord_1456562 prefixEnd_1456562 83101823230470603130711 := by
  unfold tailWord_1456562
  simp only [CollatzResearch.WordTrace]
  refine ⟨13281295137283027457458985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35416787032754739886557293 13281295137283027457458985)
  ·
    refine ⟨9960971352962270593094239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13281295137283027457458985 9960971352962270593094239)
    ·
      refine ⟨14941457029443405889641359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9960971352962270593094239 14941457029443405889641359)
      ·
        refine ⟨22412185544165108834462039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14941457029443405889641359 22412185544165108834462039)
        ·
          refine ⟨33618278316247663251693059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22412185544165108834462039 33618278316247663251693059)
          ·
            refine ⟨50427417474371494877539589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33618278316247663251693059 50427417474371494877539589)
            ·
              refine ⟨9455140776444655289538673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50427417474371494877539589 9455140776444655289538673)
              ·
                refine ⟨7091355582333491467154005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9455140776444655289538673 7091355582333491467154005)
                ·
                  refine ⟨83101823230470603130711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 7091355582333491467154005 83101823230470603130711)
                  ·
                    rfl

theorem cell23_1456562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 8].length) (baseStart_1456562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456562 prefixEnd_1456562 := by exact prefixLift 1456562
  have htrace : WordTrace (prefixWord ++ tailWord_1456562) baseStart_1456562 baseEnd_1456562 := by
    simpa [prefixWord, tailWord_1456562, baseEnd_1456562] using wordTrace_append hprefix tailTrace_1456562
  have hstable : (prefixWord ++ tailWord_1456562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456562).length < 2 ^ (prefixWord ++ tailWord_1456562).sum := by decide
  have hdescent : baseEnd_1456562 < baseStart_1456562 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456616 : List Nat := [2, 1, 4, 1, 1, 3, 2, 1, 1, 5, 2]
def baseStart_1456616 : Nat := 118140960795 + 1456616 * 2 ^ 59
def prefixEnd_1456616 : Nat := 4983230072969 + 3 ^ 40 * 1456616 * 2
def baseEnd_1456616 : Nat := 747944137029578216901151

theorem tailTrace_1456616 : CollatzResearch.WordTrace tailWord_1456616 prefixEnd_1456616 747944137029578216901151 := by
  unfold tailWord_1456616
  simp only [CollatzResearch.WordTrace]
  refine ⟨26563575045468238526150851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35418100060624318034867801 26563575045468238526150851)
  ·
    refine ⟨39845362568202357789226277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26563575045468238526150851 39845362568202357789226277)
    ·
      refine ⟨7471005481537942085479927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39845362568202357789226277 7471005481537942085479927)
      ·
        refine ⟨11206508222306913128219891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7471005481537942085479927 11206508222306913128219891)
        ·
          refine ⟨16809762333460369692329837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11206508222306913128219891 16809762333460369692329837)
          ·
            refine ⟨6303660875047638634623689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16809762333460369692329837 6303660875047638634623689)
            ·
              refine ⟨4727745656285728975967767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6303660875047638634623689 4727745656285728975967767)
              ·
                refine ⟨7091618484428593463951651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4727745656285728975967767 7091618484428593463951651)
                ·
                  refine ⟨10637427726642890195927477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7091618484428593463951651 10637427726642890195927477)
                  ·
                    refine ⟨997258849372770955868201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10637427726642890195927477 997258849372770955868201)
                    ·
                      refine ⟨747944137029578216901151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 997258849372770955868201 747944137029578216901151)
                      ·
                        rfl

theorem cell23_1456616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 2, 1, 1, 5, 2].length) (baseStart_1456616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456616 prefixEnd_1456616 := by exact prefixLift 1456616
  have htrace : WordTrace (prefixWord ++ tailWord_1456616) baseStart_1456616 baseEnd_1456616 := by
    simpa [prefixWord, tailWord_1456616, baseEnd_1456616] using wordTrace_append hprefix tailTrace_1456616
  have hstable : (prefixWord ++ tailWord_1456616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456616).length < 2 ^ (prefixWord ++ tailWord_1456616).sum := by decide
  have hdescent : baseEnd_1456616 < baseStart_1456616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456639 : List Nat := [1, 1, 2, 2, 1, 2, 3, 3, 4, 4]
def baseStart_1456639 : Nat := 118140960795 + 1456639 * 2 ^ 59
def prefixEnd_1456639 : Nat := 4983230072969 + 3 ^ 40 * 1456639 * 2
def baseEnd_1456639 : Nat := 249318649028210542304515

theorem tailTrace_1456639 : CollatzResearch.WordTrace tailWord_1456639 prefixEnd_1456639 249318649028210542304515 := by
  unfold tailWord_1456639
  simp only [CollatzResearch.WordTrace]
  refine ⟨53127988969853151980388971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35418659313235434653592647 53127988969853151980388971)
  ·
    refine ⟨79691983454779727970583457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53127988969853151980388971 79691983454779727970583457)
    ·
      refine ⟨59768987591084795977937593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79691983454779727970583457 59768987591084795977937593)
      ·
        refine ⟨44826740693313596983453195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59768987591084795977937593 44826740693313596983453195)
        ·
          refine ⟨67240111039970395475179793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44826740693313596983453195 67240111039970395475179793)
          ·
            refine ⟨50430083279977796606384845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67240111039970395475179793 50430083279977796606384845)
            ·
              refine ⟨18911281229991673727394317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50430083279977796606384845 18911281229991673727394317)
              ·
                refine ⟨7091730461246877647772869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18911281229991673727394317 7091730461246877647772869)
                ·
                  refine ⟨1329699461483789558957413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7091730461246877647772869 1329699461483789558957413)
                  ·
                    refine ⟨249318649028210542304515, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1329699461483789558957413 249318649028210542304515)
                    ·
                      rfl

theorem cell23_1456639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 3, 4, 4].length) (baseStart_1456639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456639 prefixEnd_1456639 := by exact prefixLift 1456639
  have htrace : WordTrace (prefixWord ++ tailWord_1456639) baseStart_1456639 baseEnd_1456639 := by
    simpa [prefixWord, tailWord_1456639, baseEnd_1456639] using wordTrace_append hprefix tailTrace_1456639
  have hstable : (prefixWord ++ tailWord_1456639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456639).length < 2 ^ (prefixWord ++ tailWord_1456639).sum := by decide
  have hdescent : baseEnd_1456639 < baseStart_1456639 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456659 : List Nat := [1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 4]
def baseStart_1456659 : Nat := 118140960795 + 1456659 * 2 ^ 59
def prefixEnd_1456659 : Nat := 4983230072969 + 3 ^ 40 * 1456659 * 2
def baseEnd_1456659 : Nat := 747966216697721548663453

theorem tailTrace_1456659 : CollatzResearch.WordTrace tailWord_1456659 prefixEnd_1456659 747966216697721548663453 := by
  unfold tailWord_1456659
  simp only [CollatzResearch.WordTrace]
  refine ⟨53128718429780695396117031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35419145619853796930744687 53128718429780695396117031)
  ·
    refine ⟨79693077644671043094175547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53128718429780695396117031 79693077644671043094175547)
    ·
      refine ⟨119539616467006564641263321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79693077644671043094175547 119539616467006564641263321)
      ·
        refine ⟨89654712350254923480947491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119539616467006564641263321 89654712350254923480947491)
        ·
          refine ⟨134482068525382385221421237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89654712350254923480947491 134482068525382385221421237)
          ·
            refine ⟨12607693924254598614508241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 134482068525382385221421237 12607693924254598614508241)
            ·
              refine ⟨9455770443190948960881181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12607693924254598614508241 9455770443190948960881181)
              ·
                refine ⟨3545913916196605860330443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9455770443190948960881181 3545913916196605860330443)
                ·
                  refine ⟨5318870874294908790495665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3545913916196605860330443 5318870874294908790495665)
                  ·
                    refine ⟨3989153155721181592871749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5318870874294908790495665 3989153155721181592871749)
                    ·
                      refine ⟨747966216697721548663453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3989153155721181592871749 747966216697721548663453)
                      ·
                        rfl

theorem cell23_1456659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 2, 3, 1, 2, 4].length) (baseStart_1456659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456659 prefixEnd_1456659 := by exact prefixLift 1456659
  have htrace : WordTrace (prefixWord ++ tailWord_1456659) baseStart_1456659 baseEnd_1456659 := by
    simpa [prefixWord, tailWord_1456659, baseEnd_1456659] using wordTrace_append hprefix tailTrace_1456659
  have hstable : (prefixWord ++ tailWord_1456659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456659).length < 2 ^ (prefixWord ++ tailWord_1456659).sum := by decide
  have hdescent : baseEnd_1456659 < baseStart_1456659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456660 : List Nat := [2, 4, 3, 1, 1, 3, 1, 2, 1, 5]
def baseStart_1456660 : Nat := 118140960795 + 1456660 * 2 ^ 59
def prefixEnd_1456660 : Nat := 4983230072969 + 3 ^ 40 * 1456660 * 2
def baseEnd_1456660 : Nat := 249322243392792014916983

theorem tailTrace_1456660 : CollatzResearch.WordTrace tailWord_1456660 prefixEnd_1456660 249322243392792014916983 := by
  unfold tailWord_1456660
  simp only [CollatzResearch.WordTrace]
  refine ⟨26564377451388536283451717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35419169935184715044602289 26564377451388536283451717)
  ·
    refine ⟨4980820772135350553147197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26564377451388536283451717 4980820772135350553147197)
    ·
      refine ⟨1867807789550756457430199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4980820772135350553147197 1867807789550756457430199)
      ·
        refine ⟨2801711684326134686145299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1867807789550756457430199 2801711684326134686145299)
        ·
          refine ⟨4202567526489202029217949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2801711684326134686145299 4202567526489202029217949)
          ·
            refine ⟨1575962822433450760956731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4202567526489202029217949 1575962822433450760956731)
            ·
              refine ⟨2363944233650176141435097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1575962822433450760956731 2363944233650176141435097)
              ·
                refine ⟨1772958175237632106076323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2363944233650176141435097 1772958175237632106076323)
                ·
                  refine ⟨2659437262856448159114485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1772958175237632106076323 2659437262856448159114485)
                  ·
                    refine ⟨249322243392792014916983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2659437262856448159114485 249322243392792014916983)
                    ·
                      rfl

theorem cell23_1456660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_1456660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456660 prefixEnd_1456660 := by exact prefixLift 1456660
  have htrace : WordTrace (prefixWord ++ tailWord_1456660) baseStart_1456660 baseEnd_1456660 := by
    simpa [prefixWord, tailWord_1456660, baseEnd_1456660] using wordTrace_append hprefix tailTrace_1456660
  have hstable : (prefixWord ++ tailWord_1456660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456660).length < 2 ^ (prefixWord ++ tailWord_1456660).sum := by decide
  have hdescent : baseEnd_1456660 < baseStart_1456660 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456663 : List Nat := [1, 1, 3, 6, 1, 1, 1, 1, 3, 1, 4]
def baseStart_1456663 : Nat := 118140960795 + 1456663 * 2 ^ 59
def prefixEnd_1456663 : Nat := 4983230072969 + 3 ^ 40 * 1456663 * 2
def baseEnd_1456663 : Nat := 747968270620339533013435

theorem tailTrace_1456663 : CollatzResearch.WordTrace tailWord_1456663 prefixEnd_1456663 747968270620339533013435 := by
  unfold tailWord_1456663
  simp only [CollatzResearch.WordTrace]
  refine ⟨53128864321766204079262643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35419242881177469386175095 53128864321766204079262643)
  ·
    refine ⟨79693296482649306118893965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53128864321766204079262643 79693296482649306118893965)
    ·
      refine ⟨29884986180993489794585237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79693296482649306118893965 29884986180993489794585237)
      ·
        refine ⟨1400858727234069834121183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29884986180993489794585237 1400858727234069834121183)
        ·
          refine ⟨2101288090851104751181775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1400858727234069834121183 2101288090851104751181775)
          ·
            refine ⟨3151932136276657126772663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2101288090851104751181775 3151932136276657126772663)
            ·
              refine ⟨4727898204414985690158995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3151932136276657126772663 4727898204414985690158995)
              ·
                refine ⟨7091847306622478535238493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4727898204414985690158995 7091847306622478535238493)
                ·
                  refine ⟨2659442739983429450714435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7091847306622478535238493 2659442739983429450714435)
                  ·
                    refine ⟨3989164109975144176071653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2659442739983429450714435 3989164109975144176071653)
                    ·
                      refine ⟨747968270620339533013435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3989164109975144176071653 747968270620339533013435)
                      ·
                        rfl

theorem cell23_1456663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_1456663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456663 prefixEnd_1456663 := by exact prefixLift 1456663
  have htrace : WordTrace (prefixWord ++ tailWord_1456663) baseStart_1456663 baseEnd_1456663 := by
    simpa [prefixWord, tailWord_1456663, baseEnd_1456663] using wordTrace_append hprefix tailTrace_1456663
  have hstable : (prefixWord ++ tailWord_1456663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456663).length < 2 ^ (prefixWord ++ tailWord_1456663).sum := by decide
  have hdescent : baseEnd_1456663 < baseStart_1456663 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456669 : List Nat := [1, 4, 2, 2, 1, 2, 2, 9]
def baseStart_1456669 : Nat := 118140960795 + 1456669 * 2 ^ 59
def prefixEnd_1456669 : Nat := 4983230072969 + 3 ^ 40 * 1456669 * 2
def baseEnd_1456669 : Nat := 27702642648306167019941

theorem tailTrace_1456669 : CollatzResearch.WordTrace tailWord_1456669 prefixEnd_1456669 27702642648306167019941 := by
  unfold tailWord_1456669
  simp only [CollatzResearch.WordTrace]
  refine ⟨53129083159744467103981061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35419388773162978069320707 53129083159744467103981061)
  ·
    refine ⟨9961703092452087581996449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53129083159744467103981061 9961703092452087581996449)
    ·
      refine ⟨7471277319339065686497337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9961703092452087581996449 7471277319339065686497337)
      ·
        refine ⟨5603457989504299264873003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7471277319339065686497337 5603457989504299264873003)
        ·
          refine ⟨8405186984256448897309505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5603457989504299264873003 8405186984256448897309505)
          ·
            refine ⟨6303890238192336672982129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8405186984256448897309505 6303890238192336672982129)
            ·
              refine ⟨4727917678644252504736597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6303890238192336672982129 4727917678644252504736597)
              ·
                refine ⟨27702642648306167019941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4727917678644252504736597 27702642648306167019941)
                ·
                  rfl

theorem cell23_1456669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 2, 9].length) (baseStart_1456669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456669 prefixEnd_1456669 := by exact prefixLift 1456669
  have htrace : WordTrace (prefixWord ++ tailWord_1456669) baseStart_1456669 baseEnd_1456669 := by
    simpa [prefixWord, tailWord_1456669, baseEnd_1456669] using wordTrace_append hprefix tailTrace_1456669
  have hstable : (prefixWord ++ tailWord_1456669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456669).length < 2 ^ (prefixWord ++ tailWord_1456669).sum := by decide
  have hdescent : baseEnd_1456669 < baseStart_1456669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456680 : List Nat := [2, 1, 5, 2, 1, 2, 3, 1, 1, 1, 4]
def baseStart_1456680 : Nat := 118140960795 + 1456680 * 2 ^ 59
def prefixEnd_1456680 : Nat := 4983230072969 + 3 ^ 40 * 1456680 * 2
def baseEnd_1456680 : Nat := 747976999791465966500857

theorem tailTrace_1456680 : CollatzResearch.WordTrace tailWord_1456680 prefixEnd_1456680 747976999791465966500857 := by
  unfold tailWord_1456680
  simp only [CollatzResearch.WordTrace]
  refine ⟨26564742181352307991315747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35419656241803077321754329 26564742181352307991315747)
  ·
    refine ⟨39847113272028461986973621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26564742181352307991315747 39847113272028461986973621)
    ·
      refine ⟨3735666869252668311278777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39847113272028461986973621 3735666869252668311278777)
      ·
        refine ⟨2801750151939501233459083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3735666869252668311278777 2801750151939501233459083)
        ·
          refine ⟨4202625227909251850188625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2801750151939501233459083 4202625227909251850188625)
          ·
            refine ⟨3151968920931938887641469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4202625227909251850188625 3151968920931938887641469)
            ·
              refine ⟨1181988345349477082865551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3151968920931938887641469 1181988345349477082865551)
              ·
                refine ⟨1772982518024215624298327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1181988345349477082865551 1772982518024215624298327)
                ·
                  refine ⟨2659473777036323436447491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1772982518024215624298327 2659473777036323436447491)
                  ·
                    refine ⟨3989210665554485154671237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2659473777036323436447491 3989210665554485154671237)
                    ·
                      refine ⟨747976999791465966500857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3989210665554485154671237 747976999791465966500857)
                      ·
                        rfl

theorem cell23_1456680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_1456680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456680 prefixEnd_1456680 := by exact prefixLift 1456680
  have htrace : WordTrace (prefixWord ++ tailWord_1456680) baseStart_1456680 baseEnd_1456680 := by
    simpa [prefixWord, tailWord_1456680, baseEnd_1456680] using wordTrace_append hprefix tailTrace_1456680
  have hstable : (prefixWord ++ tailWord_1456680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456680).length < 2 ^ (prefixWord ++ tailWord_1456680).sum := by decide
  have hdescent : baseEnd_1456680 < baseStart_1456680 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456686 : List Nat := [4, 1, 3, 1, 4, 10]
def baseStart_1456686 : Nat := 118140960795 + 1456686 * 2 ^ 59
def prefixEnd_1456686 : Nat := 4983230072969 + 3 ^ 40 * 1456686 * 2
def baseEnd_1456686 : Nat := 3078107327882275485703

theorem tailTrace_1456686 : CollatzResearch.WordTrace tailWord_1456686 prefixEnd_1456686 3078107327882275485703 := by
  unfold tailWord_1456686
  simp only [CollatzResearch.WordTrace]
  refine ⟨6641212900085359875918739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35419802133788586004899941 6641212900085359875918739)
  ·
    refine ⟨9961819350128039813878109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6641212900085359875918739 9961819350128039813878109)
    ·
      refine ⟨3735682256298014930204291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9961819350128039813878109 3735682256298014930204291)
      ·
        refine ⟨5603523384447022395306437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3735682256298014930204291 5603523384447022395306437)
        ·
          refine ⟨1050660634583816699119957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5603523384447022395306437 1050660634583816699119957)
          ·
            refine ⟨3078107327882275485703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1050660634583816699119957 3078107327882275485703)
            ·
              rfl

theorem cell23_1456686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 10].length) (baseStart_1456686 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456686 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456686 prefixEnd_1456686 := by exact prefixLift 1456686
  have htrace : WordTrace (prefixWord ++ tailWord_1456686) baseStart_1456686 baseEnd_1456686 := by
    simpa [prefixWord, tailWord_1456686, baseEnd_1456686] using wordTrace_append hprefix tailTrace_1456686
  have hstable : (prefixWord ++ tailWord_1456686).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456686).length < 2 ^ (prefixWord ++ tailWord_1456686).sum := by decide
  have hdescent : baseEnd_1456686 < baseStart_1456686 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456710 : List Nat := [6, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_1456710 : Nat := 118140960795 + 1456710 * 2 ^ 59
def prefixEnd_1456710 : Nat := 4983230072969 + 3 ^ 40 * 1456710 * 2
def baseEnd_1456710 : Nat := 747992404211100849125719

theorem tailTrace_1456710 : CollatzResearch.WordTrace tailWord_1456710 prefixEnd_1456710 747992404211100849125719 := by
  unfold tailWord_1456710
  simp only [CollatzResearch.WordTrace]
  refine ⟨1660330579768622847069487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35420385701730620737482389 1660330579768622847069487)
  ·
    refine ⟨2490495869652934270604231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1660330579768622847069487 2490495869652934270604231)
    ·
      refine ⟨3735743804479401405906347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2490495869652934270604231 3735743804479401405906347)
      ·
        refine ⟨5603615706719102108859521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3735743804479401405906347 5603615706719102108859521)
        ·
          refine ⟨4202711780039326581644641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5603615706719102108859521 4202711780039326581644641)
          ·
            refine ⟨3152033835029494936233481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4202711780039326581644641 3152033835029494936233481)
            ·
              refine ⟨2364025376272121202175111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3152033835029494936233481 2364025376272121202175111)
              ·
                refine ⟨3546038064408181803262667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2364025376272121202175111 3546038064408181803262667)
                ·
                  refine ⟨5319057096612272704894001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3546038064408181803262667 5319057096612272704894001)
                  ·
                    refine ⟨3989292822459204528670501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5319057096612272704894001 3989292822459204528670501)
                    ·
                      refine ⟨747992404211100849125719, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3989292822459204528670501 747992404211100849125719)
                      ·
                        rfl

theorem cell23_1456710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_1456710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456710 prefixEnd_1456710 := by exact prefixLift 1456710
  have htrace : WordTrace (prefixWord ++ tailWord_1456710) baseStart_1456710 baseEnd_1456710 := by
    simpa [prefixWord, tailWord_1456710, baseEnd_1456710] using wordTrace_append hprefix tailTrace_1456710
  have hstable : (prefixWord ++ tailWord_1456710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456710).length < 2 ^ (prefixWord ++ tailWord_1456710).sum := by decide
  have hdescent : baseEnd_1456710 < baseStart_1456710 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456734 : List Nat := [4, 4, 1, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_1456734 : Nat := 118140960795 + 1456734 * 2 ^ 59
def prefixEnd_1456734 : Nat := 4983230072969 + 3 ^ 40 * 1456734 * 2
def baseEnd_1456734 : Nat := 748004727746808755225609

theorem tailTrace_1456734 : CollatzResearch.WordTrace tailWord_1456734 prefixEnd_1456734 748004727746808755225609 := by
  unfold tailWord_1456734
  simp only [CollatzResearch.WordTrace]
  refine ⟨6641431738063622900637157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35420969269672655470064837 6641431738063622900637157)
  ·
    refine ⟨1245268450886929293869467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6641431738063622900637157 1245268450886929293869467)
    ·
      refine ⟨1867902676330393940804201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1245268450886929293869467 1867902676330393940804201)
      ·
        refine ⟨1400927007247795455603151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1867902676330393940804201 1400927007247795455603151)
        ·
          refine ⟨2101390510871693183404727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1400927007247795455603151 2101390510871693183404727)
          ·
            refine ⟨3152085766307539775107091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2101390510871693183404727 3152085766307539775107091)
            ·
              refine ⟨4728128649461309662660637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3152085766307539775107091 4728128649461309662660637)
              ·
                refine ⟨1773048243547991123497739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4728128649461309662660637 1773048243547991123497739)
                ·
                  refine ⟨2659572365321986685246609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1773048243547991123497739 2659572365321986685246609)
                  ·
                    refine ⟨1994679273991490013934957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2659572365321986685246609 1994679273991490013934957)
                    ·
                      refine ⟨748004727746808755225609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1994679273991490013934957 748004727746808755225609)
                      ·
                        rfl

theorem cell23_1456734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_1456734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456734 prefixEnd_1456734 := by exact prefixLift 1456734
  have htrace : WordTrace (prefixWord ++ tailWord_1456734) baseStart_1456734 baseEnd_1456734 := by
    simpa [prefixWord, tailWord_1456734, baseEnd_1456734] using wordTrace_append hprefix tailTrace_1456734
  have hstable : (prefixWord ++ tailWord_1456734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456734).length < 2 ^ (prefixWord ++ tailWord_1456734).sum := by decide
  have hdescent : baseEnd_1456734 < baseStart_1456734 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456739 : List Nat := [1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 5]
def baseStart_1456739 : Nat := 118140960795 + 1456739 * 2 ^ 59
def prefixEnd_1456739 : Nat := 4983230072969 + 3 ^ 40 * 1456739 * 2
def baseEnd_1456739 : Nat := 748007295150081235663085

theorem tailTrace_1456739 : CollatzResearch.WordTrace tailWord_1456739 prefixEnd_1456739 748007295150081235663085 := by
  unfold tailWord_1456739
  simp only [CollatzResearch.WordTrace]
  refine ⟨53131636269490869059029271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35421090846327246039352847 53131636269490869059029271)
  ·
    refine ⟨79697454404236303588543907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53131636269490869059029271 79697454404236303588543907)
    ·
      refine ⟨119546181606354455382815861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79697454404236303588543907 119546181606354455382815861)
      ·
        refine ⟨11207454525595730192138987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119546181606354455382815861 11207454525595730192138987)
        ·
          refine ⟨16811181788393595288208481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11207454525595730192138987 16811181788393595288208481)
          ·
            refine ⟨12608386341295196466156361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16811181788393595288208481 12608386341295196466156361)
            ·
              refine ⟨9456289755971397349617271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12608386341295196466156361 9456289755971397349617271)
              ·
                refine ⟨14184434633957096024425907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9456289755971397349617271 14184434633957096024425907)
                ·
                  refine ⟨21276651950935644036638861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14184434633957096024425907 21276651950935644036638861)
                  ·
                    refine ⟨7978744481600866513739573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21276651950935644036638861 7978744481600866513739573)
                    ·
                      refine ⟨748007295150081235663085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7978744481600866513739573 748007295150081235663085)
                      ·
                        rfl

theorem cell23_1456739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 3, 5].length) (baseStart_1456739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456739 prefixEnd_1456739 := by exact prefixLift 1456739
  have htrace : WordTrace (prefixWord ++ tailWord_1456739) baseStart_1456739 baseEnd_1456739 := by
    simpa [prefixWord, tailWord_1456739, baseEnd_1456739] using wordTrace_append hprefix tailTrace_1456739
  have hstable : (prefixWord ++ tailWord_1456739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456739).length < 2 ^ (prefixWord ++ tailWord_1456739).sum := by decide
  have hdescent : baseEnd_1456739 < baseStart_1456739 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456759 : List Nat := [1, 1, 3, 1, 1, 3, 3, 3, 7]
def baseStart_1456759 : Nat := 118140960795 + 1456759 * 2 ^ 59
def prefixEnd_1456759 : Nat := 4983230072969 + 3 ^ 40 * 1456759 * 2
def baseEnd_1456759 : Nat := 83113062751463461934777

theorem tailTrace_1456759 : CollatzResearch.WordTrace tailWord_1456759 prefixEnd_1456759 83113062751463461934777 := by
  unfold tailWord_1456759
  simp only [CollatzResearch.WordTrace]
  refine ⟨53132365729418412474757331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35421577152945608316504887 53132365729418412474757331)
  ·
    refine ⟨79698548594127618712135997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53132365729418412474757331 79698548594127618712135997)
    ·
      refine ⟨29886955722797857017050999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79698548594127618712135997 29886955722797857017050999)
      ·
        refine ⟨44830433584196785525576499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29886955722797857017050999 44830433584196785525576499)
        ·
          refine ⟨67245650376295178288364749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44830433584196785525576499 67245650376295178288364749)
          ·
            refine ⟨25217118891110691858136781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67245650376295178288364749 25217118891110691858136781)
            ·
              refine ⟨9456419584166509446801293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25217118891110691858136781 9456419584166509446801293)
              ·
                refine ⟨3546157344062441042550485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9456419584166509446801293 3546157344062441042550485)
                ·
                  refine ⟨83113062751463461934777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3546157344062441042550485 83113062751463461934777)
                  ·
                    rfl

theorem cell23_1456759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 3, 3, 7].length) (baseStart_1456759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456759 prefixEnd_1456759 := by exact prefixLift 1456759
  have htrace : WordTrace (prefixWord ++ tailWord_1456759) baseStart_1456759 baseEnd_1456759 := by
    simpa [prefixWord, tailWord_1456759, baseEnd_1456759] using wordTrace_append hprefix tailTrace_1456759
  have hstable : (prefixWord ++ tailWord_1456759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456759).length < 2 ^ (prefixWord ++ tailWord_1456759).sum := by decide
  have hdescent : baseEnd_1456759 < baseStart_1456759 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456826 : List Nat := [3, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4]
def baseStart_1456826 : Nat := 118140960795 + 1456826 * 2 ^ 59
def prefixEnd_1456826 : Nat := 4983230072969 + 3 ^ 40 * 1456826 * 2
def baseEnd_1456826 : Nat := 748051967967022395275185

theorem tailTrace_1456826 : CollatzResearch.WordTrace tailWord_1456826 prefixEnd_1456826 748051967967022395275185 := by
  unfold tailWord_1456826
  simp only [CollatzResearch.WordTrace]
  refine ⟨13283702355043920729361583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35423206280117121944964221 13283702355043920729361583)
  ·
    refine ⟨19925553532565881094042375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13283702355043920729361583 19925553532565881094042375)
    ·
      refine ⟨29888330298848821641063563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19925553532565881094042375 29888330298848821641063563)
      ·
        refine ⟨44832495448273232461595345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29888330298848821641063563 44832495448273232461595345)
        ·
          refine ⟨33624371586204924346196509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44832495448273232461595345 33624371586204924346196509)
          ·
            refine ⟨12609139344826846629823691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33624371586204924346196509 12609139344826846629823691)
            ·
              refine ⟨18913709017240269944735537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12609139344826846629823691 18913709017240269944735537)
              ·
                refine ⟨14185281762930202458551653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18913709017240269944735537 14185281762930202458551653)
                ·
                  refine ⟨2659740330549412960978435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14185281762930202458551653 2659740330549412960978435)
                  ·
                    refine ⟨3989610495824119441467653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2659740330549412960978435 3989610495824119441467653)
                    ·
                      refine ⟨748051967967022395275185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3989610495824119441467653 748051967967022395275185)
                      ·
                        rfl

theorem cell23_1456826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 2, 4, 1, 4].length) (baseStart_1456826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456826 prefixEnd_1456826 := by exact prefixLift 1456826
  have htrace : WordTrace (prefixWord ++ tailWord_1456826) baseStart_1456826 baseEnd_1456826 := by
    simpa [prefixWord, tailWord_1456826, baseEnd_1456826] using wordTrace_append hprefix tailTrace_1456826
  have hstable : (prefixWord ++ tailWord_1456826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456826).length < 2 ^ (prefixWord ++ tailWord_1456826).sum := by decide
  have hdescent : baseEnd_1456826 < baseStart_1456826 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456859 : List Nat := [1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 7]
def baseStart_1456859 : Nat := 118140960795 + 1456859 * 2 ^ 59
def prefixEnd_1456859 : Nat := 4983230072969 + 3 ^ 40 * 1456859 * 2
def baseEnd_1456859 : Nat := 748068912828620766162533

theorem tailTrace_1456859 : CollatzResearch.WordTrace tailWord_1456859 prefixEnd_1456859 748068912828620766162533 := by
  unfold tailWord_1456859
  simp only [CollatzResearch.WordTrace]
  refine ⟨53136013029056129553397631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35424008686037419702265087 53136013029056129553397631)
  ·
    refine ⟨79704019543584194330096447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53136013029056129553397631 79704019543584194330096447)
    ·
      refine ⟨119556029315376291495144671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79704019543584194330096447 119556029315376291495144671)
      ·
        refine ⟨179334043973064437242717007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119556029315376291495144671 179334043973064437242717007)
        ·
          refine ⟨269001065959596655864075511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179334043973064437242717007 269001065959596655864075511)
          ·
            refine ⟨403501598939394983796113267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 269001065959596655864075511 403501598939394983796113267)
            ·
              refine ⟨605252398409092475694169901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 403501598939394983796113267 605252398409092475694169901)
              ·
                refine ⟨226969649403409678385313713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 605252398409092475694169901 226969649403409678385313713)
                ·
                  refine ⟨170227237052557258788985285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 226969649403409678385313713 170227237052557258788985285)
                  ·
                    refine ⟨31917606947354486022934741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 170227237052557258788985285 31917606947354486022934741)
                    ·
                      refine ⟨748068912828620766162533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31917606947354486022934741 748068912828620766162533)
                      ·
                        rfl

theorem cell23_1456859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3, 2, 4, 7].length) (baseStart_1456859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456859 prefixEnd_1456859 := by exact prefixLift 1456859
  have htrace : WordTrace (prefixWord ++ tailWord_1456859) baseStart_1456859 baseEnd_1456859 := by
    simpa [prefixWord, tailWord_1456859, baseEnd_1456859] using wordTrace_append hprefix tailTrace_1456859
  have hstable : (prefixWord ++ tailWord_1456859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456859).length < 2 ^ (prefixWord ++ tailWord_1456859).sum := by decide
  have hdescent : baseEnd_1456859 < baseStart_1456859 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456860 : List Nat := [2, 2, 5, 1, 1, 1, 2, 2, 2, 1, 4]
def baseStart_1456860 : Nat := 118140960795 + 1456860 * 2 ^ 59
def prefixEnd_1456860 : Nat := 4983230072969 + 3 ^ 40 * 1456860 * 2
def baseEnd_1456860 : Nat := 748069426309275262250029

theorem tailTrace_1456860 : CollatzResearch.WordTrace tailWord_1456860 prefixEnd_1456860 748069426309275262250029 := by
  unfold tailWord_1456860
  simp only [CollatzResearch.WordTrace]
  refine ⟨26568024751026253362092017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35424033001368337816122689 26568024751026253362092017)
  ·
    refine ⟨19926018563269690021569013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26568024751026253362092017 19926018563269690021569013)
    ·
      refine ⟨1868064240306533439522095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19926018563269690021569013 1868064240306533439522095)
      ·
        refine ⟨2802096360459800159283143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1868064240306533439522095 2802096360459800159283143)
        ·
          refine ⟨4203144540689700238924715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2802096360459800159283143 4203144540689700238924715)
          ·
            refine ⟨6304716811034550358387073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4203144540689700238924715 6304716811034550358387073)
            ·
              refine ⟨4728537608275912768790305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6304716811034550358387073 4728537608275912768790305)
              ·
                refine ⟨3546403206206934576592729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4728537608275912768790305 3546403206206934576592729)
                ·
                  refine ⟨2659802404655200932444547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3546403206206934576592729 2659802404655200932444547)
                  ·
                    refine ⟨3989703606982801398666821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2659802404655200932444547 3989703606982801398666821)
                    ·
                      refine ⟨748069426309275262250029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3989703606982801398666821 748069426309275262250029)
                      ·
                        rfl

theorem cell23_1456860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 2, 2, 2, 1, 4].length) (baseStart_1456860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456860 prefixEnd_1456860 := by exact prefixLift 1456860
  have htrace : WordTrace (prefixWord ++ tailWord_1456860) baseStart_1456860 baseEnd_1456860 := by
    simpa [prefixWord, tailWord_1456860, baseEnd_1456860] using wordTrace_append hprefix tailTrace_1456860
  have hstable : (prefixWord ++ tailWord_1456860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456860).length < 2 ^ (prefixWord ++ tailWord_1456860).sum := by decide
  have hdescent : baseEnd_1456860 < baseStart_1456860 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456863 : List Nat := [1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 3]
def baseStart_1456863 : Nat := 118140960795 + 1456863 * 2 ^ 59
def prefixEnd_1456863 : Nat := 4983230072969 + 3 ^ 40 * 1456863 * 2
def baseEnd_1456863 : Nat := 748070966751238750512515

theorem tailTrace_1456863 : CollatzResearch.WordTrace tailWord_1456863 prefixEnd_1456863 748070966751238750512515 := by
  unfold tailWord_1456863
  simp only [CollatzResearch.WordTrace]
  refine ⟨53136158921041638236543243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35424105947361092157695495 53136158921041638236543243)
  ·
    refine ⟨79704238381562457354814865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53136158921041638236543243 79704238381562457354814865)
    ·
      refine ⟨59778178786171843016111149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79704238381562457354814865 59778178786171843016111149)
      ·
        refine ⟨22416817044814441131041681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59778178786171843016111149 22416817044814441131041681)
        ·
          refine ⟨16812612783610830848281261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22416817044814441131041681 16812612783610830848281261)
          ·
            refine ⟨6304729793854061568105473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16812612783610830848281261 6304729793854061568105473)
            ·
              refine ⟨4728547345390546176079105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6304729793854061568105473 4728547345390546176079105)
              ·
                refine ⟨3546410509042909632059329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4728547345390546176079105 3546410509042909632059329)
                ·
                  refine ⟨2659807881782182224044497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3546410509042909632059329 2659807881782182224044497)
                  ·
                    refine ⟨1994855911336636668033373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2659807881782182224044497 1994855911336636668033373)
                    ·
                      refine ⟨748070966751238750512515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1994855911336636668033373 748070966751238750512515)
                      ·
                        rfl

theorem cell23_1456863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 2, 2, 2, 2, 3].length) (baseStart_1456863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456863 prefixEnd_1456863 := by exact prefixLift 1456863
  have htrace : WordTrace (prefixWord ++ tailWord_1456863) baseStart_1456863 baseEnd_1456863 := by
    simpa [prefixWord, tailWord_1456863, baseEnd_1456863] using wordTrace_append hprefix tailTrace_1456863
  have hstable : (prefixWord ++ tailWord_1456863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456863).length < 2 ^ (prefixWord ++ tailWord_1456863).sum := by decide
  have hdescent : baseEnd_1456863 < baseStart_1456863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456876 : List Nat := [2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 3]
def baseStart_1456876 : Nat := 118140960795 + 1456876 * 2 ^ 59
def prefixEnd_1456876 : Nat := 4983230072969 + 3 ^ 40 * 1456876 * 2
def baseEnd_1456876 : Nat := 748077641999747199649955

theorem tailTrace_1456876 : CollatzResearch.WordTrace tailWord_1456876 prefixEnd_1456876 748077641999747199649955 := by
  unfold tailWord_1456876
  simp only [CollatzResearch.WordTrace]
  refine ⟨26568316534997270728383241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35424422046663027637844321 26568316534997270728383241)
  ·
    refine ⟨19926237401247953046287431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26568316534997270728383241 19926237401247953046287431)
    ·
      refine ⟨29889356101871929569431147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19926237401247953046287431 29889356101871929569431147)
      ·
        refine ⟨44834034152807894354146721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29889356101871929569431147 44834034152807894354146721)
        ·
          refine ⟨33625525614605920765610041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44834034152807894354146721 33625525614605920765610041)
          ·
            refine ⟨25219144210954440574207531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33625525614605920765610041 25219144210954440574207531)
            ·
              refine ⟨37828716316431660861311297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25219144210954440574207531 37828716316431660861311297)
              ·
                refine ⟨28371537237323745645983473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37828716316431660861311297 28371537237323745645983473)
                ·
                  refine ⟨21278652927992809234487605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28371537237323745645983473 21278652927992809234487605)
                  ·
                    refine ⟨1994873711999325865733213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21278652927992809234487605 1994873711999325865733213)
                    ·
                      refine ⟨748077641999747199649955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1994873711999325865733213 748077641999747199649955)
                      ·
                        rfl

theorem cell23_1456876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 3].length) (baseStart_1456876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456876 prefixEnd_1456876 := by exact prefixLift 1456876
  have htrace : WordTrace (prefixWord ++ tailWord_1456876) baseStart_1456876 baseEnd_1456876 := by
    simpa [prefixWord, tailWord_1456876, baseEnd_1456876] using wordTrace_append hprefix tailTrace_1456876
  have hstable : (prefixWord ++ tailWord_1456876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456876).length < 2 ^ (prefixWord ++ tailWord_1456876).sum := by decide
  have hdescent : baseEnd_1456876 < baseStart_1456876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1456927 : List Nat := [1, 1, 2, 4, 2, 2, 2, 4, 1, 1, 3]
def baseStart_1456927 : Nat := 118140960795 + 1456927 * 2 ^ 59
def prefixEnd_1456927 : Nat := 4983230072969 + 3 ^ 40 * 1456927 * 2
def baseEnd_1456927 : Nat := 748103829513126500112221

theorem tailTrace_1456927 : CollatzResearch.WordTrace tailWord_1456927 prefixEnd_1456927 748103829513126500112221 := by
  unfold tailWord_1456927
  simp only [CollatzResearch.WordTrace]
  refine ⟨53138493192809777166873035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35425662128539851444582023 53138493192809777166873035)
  ·
    refine ⟨79707739789214665750309553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53138493192809777166873035 79707739789214665750309553)
    ·
      refine ⟨59780804841910999312732165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79707739789214665750309553 59780804841910999312732165)
      ·
        refine ⟨11208900907858312371137281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59780804841910999312732165 11208900907858312371137281)
        ·
          refine ⟨8406675680893734278352961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11208900907858312371137281 8406675680893734278352961)
          ·
            refine ⟨6305006760670300708764721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8406675680893734278352961 6305006760670300708764721)
            ·
              refine ⟨4728755070502725531573541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6305006760670300708764721 4728755070502725531573541)
              ·
                refine ⟨886641575719261037170039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4728755070502725531573541 886641575719261037170039)
                ·
                  refine ⟨1329962363578891555755059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 886641575719261037170039 1329962363578891555755059)
                  ·
                    refine ⟨1994943545368337333632589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1329962363578891555755059 1994943545368337333632589)
                    ·
                      refine ⟨748103829513126500112221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1994943545368337333632589 748103829513126500112221)
                      ·
                        rfl

theorem cell23_1456927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_1456927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1456927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1456927 prefixEnd_1456927 := by exact prefixLift 1456927
  have htrace : WordTrace (prefixWord ++ tailWord_1456927) baseStart_1456927 baseEnd_1456927 := by
    simpa [prefixWord, tailWord_1456927, baseEnd_1456927] using wordTrace_append hprefix tailTrace_1456927
  have hstable : (prefixWord ++ tailWord_1456927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1456927).length < 2 ^ (prefixWord ++ tailWord_1456927).sum := by decide
  have hdescent : baseEnd_1456927 < baseStart_1456927 := by decide
  rcases family_descends (prefixWord ++ tailWord_1456927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457016 : List Nat := [2, 1, 2, 1, 1, 1, 1, 3, 3, 8]
def baseStart_1457016 : Nat := 118140960795 + 1457016 * 2 ^ 59
def prefixEnd_1457016 : Nat := 4983230072969 + 3 ^ 40 * 1457016 * 2
def baseEnd_1457016 : Nat := 249383176430458883966437

theorem tailTrace_1457016 : CollatzResearch.WordTrace tailWord_1457016 prefixEnd_1457016 249383176430458883966437 := by
  unfold tailWord_1457016
  simp only [CollatzResearch.WordTrace]
  refine ⟨26570869644743672683431451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35427826192991563577908601 26570869644743672683431451)
  ·
    refine ⟨39856304467115509025147177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26570869644743672683431451 39856304467115509025147177)
    ·
      refine ⟨29892228350336631768860383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39856304467115509025147177 29892228350336631768860383)
      ·
        refine ⟨44838342525504947653290575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29892228350336631768860383 44838342525504947653290575)
        ·
          refine ⟨67257513788257421479935863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44838342525504947653290575 67257513788257421479935863)
          ·
            refine ⟨100886270682386132219903795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67257513788257421479935863 100886270682386132219903795)
            ·
              refine ⟨151329406023579198329855693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100886270682386132219903795 151329406023579198329855693)
              ·
                refine ⟨56748527258842199373695885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151329406023579198329855693 56748527258842199373695885)
                ·
                  refine ⟨21280697722065824765135957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56748527258842199373695885 21280697722065824765135957)
                  ·
                    refine ⟨249383176430458883966437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21280697722065824765135957 249383176430458883966437)
                    ·
                      rfl

theorem cell23_1457016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_1457016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457016 prefixEnd_1457016 := by exact prefixLift 1457016
  have htrace : WordTrace (prefixWord ++ tailWord_1457016) baseStart_1457016 baseEnd_1457016 := by
    simpa [prefixWord, tailWord_1457016, baseEnd_1457016] using wordTrace_append hprefix tailTrace_1457016
  have hstable : (prefixWord ++ tailWord_1457016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457016).length < 2 ^ (prefixWord ++ tailWord_1457016).sum := by decide
  have hdescent : baseEnd_1457016 < baseStart_1457016 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457034 : List Nat := [3, 1, 2, 4, 1, 2, 2, 2, 2, 1, 3]
def baseStart_1457034 : Nat := 118140960795 + 1457034 * 2 ^ 59
def prefixEnd_1457034 : Nat := 4983230072969 + 3 ^ 40 * 1457034 * 2
def baseEnd_1457034 : Nat := 748158771943157581474229

theorem tailTrace_1457034 : CollatzResearch.WordTrace tailWord_1457034 prefixEnd_1457034 748158771943157581474229 := by
  unfold tailWord_1457034
  simp only [CollatzResearch.WordTrace]
  refine ⟨13285598950855533610254539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35428263868948089627345437 13285598950855533610254539)
  ·
    refine ⟨19928398426283300415381809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13285598950855533610254539 19928398426283300415381809)
    ·
      refine ⟨14946298819712475311536357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19928398426283300415381809 14946298819712475311536357)
      ·
        refine ⟨2802431028696089120913067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14946298819712475311536357 2802431028696089120913067)
        ·
          refine ⟨4203646543044133681369601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2802431028696089120913067 4203646543044133681369601)
          ·
            refine ⟨3152734907283100261027201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4203646543044133681369601 3152734907283100261027201)
            ·
              refine ⟨2364551180462325195770401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3152734907283100261027201 2364551180462325195770401)
              ·
                refine ⟨1773413385346743896827801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2364551180462325195770401 1773413385346743896827801)
                ·
                  refine ⟨1330060039010057922620851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1773413385346743896827801 1330060039010057922620851)
                  ·
                    refine ⟨1995090058515086883931277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1330060039010057922620851 1995090058515086883931277)
                    ·
                      refine ⟨748158771943157581474229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1995090058515086883931277 748158771943157581474229)
                      ·
                        rfl

theorem cell23_1457034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_1457034 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457034 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457034 prefixEnd_1457034 := by exact prefixLift 1457034
  have htrace : WordTrace (prefixWord ++ tailWord_1457034) baseStart_1457034 baseEnd_1457034 := by
    simpa [prefixWord, tailWord_1457034, baseEnd_1457034] using wordTrace_append hprefix tailTrace_1457034
  have hstable : (prefixWord ++ tailWord_1457034).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457034).length < 2 ^ (prefixWord ++ tailWord_1457034).sum := by decide
  have hdescent : baseEnd_1457034 < baseStart_1457034 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457050 : List Nat := [3, 1, 1, 4, 3, 1, 1, 1, 2, 6]
def baseStart_1457050 : Nat := 118140960795 + 1457050 * 2 ^ 59
def prefixEnd_1457050 : Nat := 4983230072969 + 3 ^ 40 * 1457050 * 2
def baseEnd_1457050 : Nat := 249388995877876506291385

theorem tailTrace_1457050 : CollatzResearch.WordTrace tailWord_1457050 prefixEnd_1457050 249388995877876506291385 := by
  unfold tailWord_1457050
  simp only [CollatzResearch.WordTrace]
  refine ⟨13285744842841042293400151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35428652914242779449067069 13285744842841042293400151)
  ·
    refine ⟨19928617264261563440100227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13285744842841042293400151 19928617264261563440100227)
    ·
      refine ⟨29892925896392345160150341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19928617264261563440100227 29892925896392345160150341)
      ·
        refine ⟨5604923605573564717528189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29892925896392345160150341 5604923605573564717528189)
        ·
          refine ⟨2101846352090086769073071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5604923605573564717528189 2101846352090086769073071)
          ·
            refine ⟨3152769528135130153609607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2101846352090086769073071 3152769528135130153609607)
            ·
              refine ⟨4729154292202695230414411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3152769528135130153609607 4729154292202695230414411)
              ·
                refine ⟨7093731438304042845621617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4729154292202695230414411 7093731438304042845621617)
                ·
                  refine ⟨5320298578728032134216213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7093731438304042845621617 5320298578728032134216213)
                  ·
                    refine ⟨249388995877876506291385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5320298578728032134216213 249388995877876506291385)
                    ·
                      rfl

theorem cell23_1457050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 1, 1, 2, 6].length) (baseStart_1457050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457050 prefixEnd_1457050 := by exact prefixLift 1457050
  have htrace : WordTrace (prefixWord ++ tailWord_1457050) baseStart_1457050 baseEnd_1457050 := by
    simpa [prefixWord, tailWord_1457050, baseEnd_1457050] using wordTrace_append hprefix tailTrace_1457050
  have hstable : (prefixWord ++ tailWord_1457050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457050).length < 2 ^ (prefixWord ++ tailWord_1457050).sum := by decide
  have hdescent : baseEnd_1457050 < baseStart_1457050 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457057 : List Nat := [1, 2, 3, 4, 1, 1, 1, 3, 1, 4, 2]
def baseStart_1457057 : Nat := 118140960795 + 1457057 * 2 ^ 59
def prefixEnd_1457057 : Nat := 4983230072969 + 3 ^ 40 * 1457057 * 2
def baseEnd_1457057 : Nat := 748170581998210991486623

theorem tailTrace_1457057 : CollatzResearch.WordTrace tailWord_1457057 prefixEnd_1457057 748170581998210991486623 := by
  unfold tailWord_1457057
  simp only [CollatzResearch.WordTrace]
  refine ⟨53143234682338809369105425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35428823121559206246070283 53143234682338809369105425)
  ·
    refine ⟨39857426011754107026829069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53143234682338809369105425 39857426011754107026829069)
    ·
      refine ⟨14946534754407790135060901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39857426011754107026829069 14946534754407790135060901)
      ·
        refine ⟨2802475266451460650323919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14946534754407790135060901 2802475266451460650323919)
        ·
          refine ⟨4203712899677190975485879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2802475266451460650323919 4203712899677190975485879)
          ·
            refine ⟨6305569349515786463228819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4203712899677190975485879 6305569349515786463228819)
            ·
              refine ⟨9458354024273679694843229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6305569349515786463228819 9458354024273679694843229)
              ·
                refine ⟨3546882759102629885566211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9458354024273679694843229 3546882759102629885566211)
                ·
                  refine ⟨5320324138653944828349317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3546882759102629885566211 5320324138653944828349317)
                  ·
                    refine ⟨997560775997614655315497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5320324138653944828349317 997560775997614655315497)
                    ·
                      refine ⟨748170581998210991486623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 997560775997614655315497 748170581998210991486623)
                      ·
                        rfl

theorem cell23_1457057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_1457057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457057 prefixEnd_1457057 := by exact prefixLift 1457057
  have htrace : WordTrace (prefixWord ++ tailWord_1457057) baseStart_1457057 baseEnd_1457057 := by
    simpa [prefixWord, tailWord_1457057, baseEnd_1457057] using wordTrace_append hprefix tailTrace_1457057
  have hstable : (prefixWord ++ tailWord_1457057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457057).length < 2 ^ (prefixWord ++ tailWord_1457057).sum := by decide
  have hdescent : baseEnd_1457057 < baseStart_1457057 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457080 : List Nat := [2, 1, 2, 1, 2, 4, 1, 5, 5]
def baseStart_1457080 : Nat := 118140960795 + 1457080 * 2 ^ 59
def prefixEnd_1457080 : Nat := 4983230072969 + 3 ^ 40 * 1457080 * 2
def baseEnd_1457080 : Nat := 83131376894807155722113

theorem tailTrace_1457080 : CollatzResearch.WordTrace tailWord_1457080 prefixEnd_1457080 83131376894807155722113 := by
  unfold tailWord_1457080
  simp only [CollatzResearch.WordTrace]
  refine ⟨26572036780627742148596347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35429382374170322864795129 26572036780627742148596347)
  ·
    refine ⟨39858055170941613222894521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26572036780627742148596347 39858055170941613222894521)
    ·
      refine ⟨29893541378206209917170891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39858055170941613222894521 29893541378206209917170891)
      ·
        refine ⟨44840312067309314875756337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29893541378206209917170891 44840312067309314875756337)
        ·
          refine ⟨33630234050481986156817253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44840312067309314875756337 33630234050481986156817253)
          ·
            refine ⟨6305668884465372404403235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33630234050481986156817253 6305668884465372404403235)
            ·
              refine ⟨9458503326698058606604853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6305668884465372404403235 9458503326698058606604853)
              ·
                refine ⟨886734686877942994369205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9458503326698058606604853 886734686877942994369205)
                ·
                  refine ⟨83131376894807155722113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 886734686877942994369205 83131376894807155722113)
                  ·
                    rfl

theorem cell23_1457080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 4, 1, 5, 5].length) (baseStart_1457080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457080 prefixEnd_1457080 := by exact prefixLift 1457080
  have htrace : WordTrace (prefixWord ++ tailWord_1457080) baseStart_1457080 baseEnd_1457080 := by
    simpa [prefixWord, tailWord_1457080, baseEnd_1457080] using wordTrace_append hprefix tailTrace_1457080
  have hstable : (prefixWord ++ tailWord_1457080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457080).length < 2 ^ (prefixWord ++ tailWord_1457080).sum := by decide
  have hdescent : baseEnd_1457080 < baseStart_1457080 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457123 : List Nat := [1, 1, 1, 6, 1, 1, 1, 1, 2, 8]
def baseStart_1457123 : Nat := 118140960795 + 1457123 * 2 ^ 59
def prefixEnd_1457123 : Nat := 4983230072969 + 3 ^ 40 * 1457123 * 2
def baseEnd_1457123 : Nat := 249401490573802577753773

theorem tailTrace_1457123 : CollatzResearch.WordTrace tailWord_1457123 prefixEnd_1457123 249401490573802577753773 := by
  unfold tailWord_1457123
  simp only [CollatzResearch.WordTrace]
  refine ⟨53145641900099702641008023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35430427933399801760672015 53145641900099702641008023)
  ·
    refine ⟨79718462850149553961512035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53145641900099702641008023 79718462850149553961512035)
    ·
      refine ⟨119577694275224330942268053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79718462850149553961512035 119577694275224330942268053)
      ·
        refine ⟨5605204419151140512918815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 119577694275224330942268053 5605204419151140512918815)
        ·
          refine ⟨8407806628726710769378223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5605204419151140512918815 8407806628726710769378223)
          ·
            refine ⟨12611709943090066154067335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8407806628726710769378223 12611709943090066154067335)
            ·
              refine ⟨18917564914635099231101003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12611709943090066154067335 18917564914635099231101003)
              ·
                refine ⟨28376347371952648846651505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18917564914635099231101003 28376347371952648846651505)
                ·
                  refine ⟨21282260528964486634988629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28376347371952648846651505 21282260528964486634988629)
                  ·
                    refine ⟨249401490573802577753773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21282260528964486634988629 249401490573802577753773)
                    ·
                      rfl

theorem cell23_1457123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 8].length) (baseStart_1457123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457123 prefixEnd_1457123 := by exact prefixLift 1457123
  have htrace : WordTrace (prefixWord ++ tailWord_1457123) baseStart_1457123 baseEnd_1457123 := by
    simpa [prefixWord, tailWord_1457123, baseEnd_1457123] using wordTrace_append hprefix tailTrace_1457123
  have hstable : (prefixWord ++ tailWord_1457123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457123).length < 2 ^ (prefixWord ++ tailWord_1457123).sum := by decide
  have hdescent : baseEnd_1457123 < baseStart_1457123 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457130 : List Nat := [3, 1, 3, 1, 2, 2, 2, 1, 1, 3, 4]
def baseStart_1457130 : Nat := 118140960795 + 1457130 * 2 ^ 59
def prefixEnd_1457130 : Nat := 4983230072969 + 3 ^ 40 * 1457130 * 2
def baseEnd_1457130 : Nat := 748208066085989205873787

theorem tailTrace_1457130 : CollatzResearch.WordTrace tailWord_1457130 prefixEnd_1457130 748208066085989205873787 := by
  unfold tailWord_1457130
  simp only [CollatzResearch.WordTrace]
  refine ⟨13286474302768585709128211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35430598140716228557675229 13286474302768585709128211)
  ·
    refine ⟨19929711454152878563692317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13286474302768585709128211 19929711454152878563692317)
    ·
      refine ⟨7473641795307329461384619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19929711454152878563692317 7473641795307329461384619)
      ·
        refine ⟨11210462692960994192076929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7473641795307329461384619 11210462692960994192076929)
        ·
          refine ⟨8407847019720745644057697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11210462692960994192076929 8407847019720745644057697)
          ·
            refine ⟨6305885264790559233043273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8407847019720745644057697 6305885264790559233043273)
            ·
              refine ⟨4729413948592919424782455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6305885264790559233043273 4729413948592919424782455)
              ·
                refine ⟨7094120922889379137173683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4729413948592919424782455 7094120922889379137173683)
                ·
                  refine ⟨10641181384334068705760525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7094120922889379137173683 10641181384334068705760525)
                  ·
                    refine ⟨3990443019125275764660197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10641181384334068705760525 3990443019125275764660197)
                    ·
                      refine ⟨748208066085989205873787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3990443019125275764660197 748208066085989205873787)
                      ·
                        rfl

theorem cell23_1457130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_1457130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457130 prefixEnd_1457130 := by exact prefixLift 1457130
  have htrace : WordTrace (prefixWord ++ tailWord_1457130) baseStart_1457130 baseEnd_1457130 := by
    simpa [prefixWord, tailWord_1457130, baseEnd_1457130] using wordTrace_append hprefix tailTrace_1457130
  have hstable : (prefixWord ++ tailWord_1457130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457130).length < 2 ^ (prefixWord ++ tailWord_1457130).sum := by decide
  have hdescent : baseEnd_1457130 < baseStart_1457130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457154 : List Nat := [3, 4, 1, 3, 1, 1, 1, 1, 1, 2, 5]
def baseStart_1457154 : Nat := 118140960795 + 1457154 * 2 ^ 59
def prefixEnd_1457154 : Nat := 4983230072969 + 3 ^ 40 * 1457154 * 2
def baseEnd_1457154 : Nat := 748220389621697111973677

theorem tailTrace_1457154 : CollatzResearch.WordTrace tailWord_1457154 prefixEnd_1457154 748220389621697111973677 := by
  unfold tailWord_1457154
  simp only [CollatzResearch.WordTrace]
  refine ⟨13286693140746848733846629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35431181708658263290257677 13286693140746848733846629)
  ·
    refine ⟨2491254963890034137596243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13286693140746848733846629 2491254963890034137596243)
    ·
      refine ⟨3736882445835051206394365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2491254963890034137596243 3736882445835051206394365)
      ·
        refine ⟨1401330917188144202397887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3736882445835051206394365 1401330917188144202397887)
        ·
          refine ⟨2101996375782216303596831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1401330917188144202397887 2101996375782216303596831)
          ·
            refine ⟨3152994563673324455395247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2101996375782216303596831 3152994563673324455395247)
            ·
              refine ⟨4729491845509986683092871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3152994563673324455395247 4729491845509986683092871)
              ·
                refine ⟨7094237768264980024639307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4729491845509986683092871 7094237768264980024639307)
                ·
                  refine ⟨10641356652397470036958961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7094237768264980024639307 10641356652397470036958961)
                  ·
                    refine ⟨7981017489298102527719221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10641356652397470036958961 7981017489298102527719221)
                    ·
                      refine ⟨748220389621697111973677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7981017489298102527719221 748220389621697111973677)
                      ·
                        rfl

theorem cell23_1457154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 1, 1, 1, 2, 5].length) (baseStart_1457154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457154 prefixEnd_1457154 := by exact prefixLift 1457154
  have htrace : WordTrace (prefixWord ++ tailWord_1457154) baseStart_1457154 baseEnd_1457154 := by
    simpa [prefixWord, tailWord_1457154, baseEnd_1457154] using wordTrace_append hprefix tailTrace_1457154
  have hstable : (prefixWord ++ tailWord_1457154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457154).length < 2 ^ (prefixWord ++ tailWord_1457154).sum := by decide
  have hdescent : baseEnd_1457154 < baseStart_1457154 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457204 : List Nat := [2, 5, 1, 2, 1, 2, 2, 2, 6]
def baseStart_1457204 : Nat := 118140960795 + 1457204 * 2 ^ 59
def prefixEnd_1457204 : Nat := 4983230072969 + 3 ^ 40 * 1457204 * 2
def baseEnd_1457204 : Nat := 83138451517157990705383

theorem tailTrace_1457204 : CollatzResearch.WordTrace tailWord_1457204 prefixEnd_1457204 83138451517157990705383 := by
  unfold tailWord_1457204
  simp only [CollatzResearch.WordTrace]
  refine ⟨26574298106403126737353333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35432397475204168983137777 26574298106403126737353333)
  ·
    refine ⟨2491340447475293131626875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 26574298106403126737353333 2491340447475293131626875)
    ·
      refine ⟨3737010671212939697440313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2491340447475293131626875 3737010671212939697440313)
      ·
        refine ⟨2802758003409704773080235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3737010671212939697440313 2802758003409704773080235)
        ·
          refine ⟨4204137005114557159620353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2802758003409704773080235 4204137005114557159620353)
          ·
            refine ⟨3153102753835917869715265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4204137005114557159620353 3153102753835917869715265)
            ·
              refine ⟨2364827065376938402286449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3153102753835917869715265 2364827065376938402286449)
              ·
                refine ⟨1773620299032703801714837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2364827065376938402286449 1773620299032703801714837)
                ·
                  refine ⟨83138451517157990705383, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1773620299032703801714837 83138451517157990705383)
                  ·
                    rfl

theorem cell23_1457204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 2, 2, 6].length) (baseStart_1457204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457204 prefixEnd_1457204 := by exact prefixLift 1457204
  have htrace : WordTrace (prefixWord ++ tailWord_1457204) baseStart_1457204 baseEnd_1457204 := by
    simpa [prefixWord, tailWord_1457204, baseEnd_1457204] using wordTrace_append hprefix tailTrace_1457204
  have hstable : (prefixWord ++ tailWord_1457204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457204).length < 2 ^ (prefixWord ++ tailWord_1457204).sum := by decide
  have hdescent : baseEnd_1457204 < baseStart_1457204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457237 : List Nat := [1, 3, 2, 2, 1, 2, 2, 4, 1, 1, 4]
def baseStart_1457237 : Nat := 118140960795 + 1457237 * 2 ^ 59
def prefixEnd_1457237 : Nat := 4983230072969 + 3 ^ 40 * 1457237 * 2
def baseEnd_1457237 : Nat := 748263008516020287235795

theorem tailTrace_1457237 : CollatzResearch.WordTrace tailWord_1457237 prefixEnd_1457237 748263008516020287235795 := by
  unfold tailWord_1457237
  simp only [CollatzResearch.WordTrace]
  refine ⟨53149799821686700110657965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35433199881124466740438643 53149799821686700110657965)
  ·
    refine ⟨19931174933132512541496737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53149799821686700110657965 19931174933132512541496737)
    ·
      refine ⟨14948381199849384406122553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19931174933132512541496737 14948381199849384406122553)
      ·
        refine ⟨11211285899887038304591915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14948381199849384406122553 11211285899887038304591915)
        ·
          refine ⟨16816928849830557456887873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11211285899887038304591915 16816928849830557456887873)
          ·
            refine ⟨12612696637372918092665905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16816928849830557456887873 12612696637372918092665905)
            ·
              refine ⟨9459522478029688569499429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12612696637372918092665905 9459522478029688569499429)
              ·
                refine ⟨1773660464630566606781143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9459522478029688569499429 1773660464630566606781143)
                ·
                  refine ⟨2660490696945849910171715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1773660464630566606781143 2660490696945849910171715)
                  ·
                    refine ⟨3990736045418774865257573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2660490696945849910171715 3990736045418774865257573)
                    ·
                      refine ⟨748263008516020287235795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3990736045418774865257573 748263008516020287235795)
                      ·
                        rfl

theorem cell23_1457237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 2, 4, 1, 1, 4].length) (baseStart_1457237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457237 prefixEnd_1457237 := by exact prefixLift 1457237
  have htrace : WordTrace (prefixWord ++ tailWord_1457237) baseStart_1457237 baseEnd_1457237 := by
    simpa [prefixWord, tailWord_1457237, baseEnd_1457237] using wordTrace_append hprefix tailTrace_1457237
  have hstable : (prefixWord ++ tailWord_1457237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457237).length < 2 ^ (prefixWord ++ tailWord_1457237).sum := by decide
  have hdescent : baseEnd_1457237 < baseStart_1457237 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457271 : List Nat := [1, 1, 3, 1, 1, 4, 1, 6, 1, 2, 2]
def baseStart_1457271 : Nat := 118140960795 + 1457271 * 2 ^ 59
def prefixEnd_1457271 : Nat := 4983230072969 + 3 ^ 40 * 1457271 * 2
def baseEnd_1457271 : Nat := 748280466858273154210639

theorem tailTrace_1457271 : CollatzResearch.WordTrace tailWord_1457271 prefixEnd_1457271 748280466858273154210639 := by
  unfold tailWord_1457271
  simp only [CollatzResearch.WordTrace]
  refine ⟨53151039903563523917395667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35434026602375682611597111 53151039903563523917395667)
  ·
    refine ⟨79726559855345285876093501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53151039903563523917395667 79726559855345285876093501)
    ·
      refine ⟨29897459945754482203535063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79726559855345285876093501 29897459945754482203535063)
      ·
        refine ⟨44846189918631723305302595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29897459945754482203535063 44846189918631723305302595)
        ·
          refine ⟨67269284877947584957953893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44846189918631723305302595 67269284877947584957953893)
          ·
            refine ⟨12612990914615172179616355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67269284877947584957953893 12612990914615172179616355)
            ·
              refine ⟨18919486371922758269424533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12612990914615172179616355 18919486371922758269424533)
              ·
                refine ⟨886850923683879293879275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18919486371922758269424533 886850923683879293879275)
                ·
                  refine ⟨1330276385525818940818913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 886850923683879293879275 1330276385525818940818913)
                  ·
                    refine ⟨997707289144364205614185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1330276385525818940818913 997707289144364205614185)
                    ·
                      refine ⟨748280466858273154210639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 997707289144364205614185 748280466858273154210639)
                      ·
                        rfl

theorem cell23_1457271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 6, 1, 2, 2].length) (baseStart_1457271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457271 prefixEnd_1457271 := by exact prefixLift 1457271
  have htrace : WordTrace (prefixWord ++ tailWord_1457271) baseStart_1457271 baseEnd_1457271 := by
    simpa [prefixWord, tailWord_1457271, baseEnd_1457271] using wordTrace_append hprefix tailTrace_1457271
  have hstable : (prefixWord ++ tailWord_1457271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457271).length < 2 ^ (prefixWord ++ tailWord_1457271).sum := by decide
  have hdescent : baseEnd_1457271 < baseStart_1457271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457281 : List Nat := [1, 2, 4, 2, 2, 2, 3, 1, 2, 4]
def baseStart_1457281 : Nat := 118140960795 + 1457281 * 2 ^ 59
def prefixEnd_1457281 : Nat := 4983230072969 + 3 ^ 40 * 1457281 * 2
def baseEnd_1457281 : Nat := 249428533888272705028531

theorem tailTrace_1457281 : CollatzResearch.WordTrace tailWord_1457281 prefixEnd_1457281 249428533888272705028531 := by
  unfold tailWord_1457281
  simp only [CollatzResearch.WordTrace]
  refine ⟨53151404633527295625259697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35434269755684863750173131 53151404633527295625259697)
  ·
    refine ⟨39863553475145471718944773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53151404633527295625259697 39863553475145471718944773)
    ·
      refine ⟨7474416276589775947302145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39863553475145471718944773 7474416276589775947302145)
      ·
        refine ⟨5605812207442331960476609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7474416276589775947302145 5605812207442331960476609)
        ·
          refine ⟨4204359155581748970357457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5605812207442331960476609 4204359155581748970357457)
          ·
            refine ⟨3153269366686311727768093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4204359155581748970357457 3153269366686311727768093)
            ·
              refine ⟨1182476012507366897913035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3153269366686311727768093 1182476012507366897913035)
              ·
                refine ⟨1773714018761050346869553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1182476012507366897913035 1773714018761050346869553)
                ·
                  refine ⟨1330285514070787760152165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1773714018761050346869553 1330285514070787760152165)
                  ·
                    refine ⟨249428533888272705028531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1330285514070787760152165 249428533888272705028531)
                    ·
                      rfl

theorem cell23_1457281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 3, 1, 2, 4].length) (baseStart_1457281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457281 prefixEnd_1457281 := by exact prefixLift 1457281
  have htrace : WordTrace (prefixWord ++ tailWord_1457281) baseStart_1457281 baseEnd_1457281 := by
    simpa [prefixWord, tailWord_1457281, baseEnd_1457281] using wordTrace_append hprefix tailTrace_1457281
  have hstable : (prefixWord ++ tailWord_1457281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457281).length < 2 ^ (prefixWord ++ tailWord_1457281).sum := by decide
  have hdescent : baseEnd_1457281 < baseStart_1457281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457284 : List Nat := [2, 3, 2, 1, 2, 4, 1, 1, 1, 2, 4]
def baseStart_1457284 : Nat := 118140960795 + 1457284 * 2 ^ 59
def prefixEnd_1457284 : Nat := 4983230072969 + 3 ^ 40 * 1457284 * 2
def baseEnd_1457284 : Nat := 748287142106781603348079

theorem tailTrace_1457284 : CollatzResearch.WordTrace tailWord_1457284 prefixEnd_1457284 748287142106781603348079 := by
  unfold tailWord_1457284
  simp only [CollatzResearch.WordTrace]
  refine ⟨26575757026258213568809453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35434342701677618091745937 26575757026258213568809453)
  ·
    refine ⟨9965908884846830088303545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26575757026258213568809453 9965908884846830088303545)
    ·
      refine ⟨7474431663635122566227659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9965908884846830088303545 7474431663635122566227659)
      ·
        refine ⟨11211647495452683849341489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7474431663635122566227659 11211647495452683849341489)
        ·
          refine ⟨8408735621589512887006117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11211647495452683849341489 8408735621589512887006117)
          ·
            refine ⟨1576637929048033666313647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8408735621589512887006117 1576637929048033666313647)
            ·
              refine ⟨2364956893572050499470471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1576637929048033666313647 2364956893572050499470471)
              ·
                refine ⟨3547435340358075749205707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2364956893572050499470471 3547435340358075749205707)
                ·
                  refine ⟨5321153010537113623808561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3547435340358075749205707 5321153010537113623808561)
                  ·
                    refine ⟨3990864757902835217856421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5321153010537113623808561 3990864757902835217856421)
                    ·
                      refine ⟨748287142106781603348079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3990864757902835217856421 748287142106781603348079)
                      ·
                        rfl

theorem cell23_1457284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_1457284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457284 prefixEnd_1457284 := by exact prefixLift 1457284
  have htrace : WordTrace (prefixWord ++ tailWord_1457284) baseStart_1457284 baseEnd_1457284 := by
    simpa [prefixWord, tailWord_1457284, baseEnd_1457284] using wordTrace_append hprefix tailTrace_1457284
  have hstable : (prefixWord ++ tailWord_1457284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457284).length < 2 ^ (prefixWord ++ tailWord_1457284).sum := by decide
  have hdescent : baseEnd_1457284 < baseStart_1457284 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457294 : List Nat := [4, 1, 1, 3, 2, 3, 2, 7]
def baseStart_1457294 : Nat := 118140960795 + 1457294 * 2 ^ 59
def prefixEnd_1457294 : Nat := 4983230072969 + 3 ^ 40 * 1457294 * 2
def baseEnd_1457294 : Nat := 27714528774567650526779

theorem tailTrace_1457294 : CollatzResearch.WordTrace tailWord_1457294 prefixEnd_1457294 27714528774567650526779 := by
  unfold tailWord_1457294
  simp only [CollatzResearch.WordTrace]
  refine ⟨6643984847810024855685367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35434585854986799230321957 6643984847810024855685367)
  ·
    refine ⟨9965977271715037283528051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6643984847810024855685367 9965977271715037283528051)
    ·
      refine ⟨14948965907572555925292077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9965977271715037283528051 14948965907572555925292077)
      ·
        refine ⟨5605862215339708471984529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14948965907572555925292077 5605862215339708471984529)
        ·
          refine ⟨4204396661504781353988397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5605862215339708471984529 4204396661504781353988397)
          ·
            refine ⟨1576648748064293007745649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4204396661504781353988397 1576648748064293007745649)
            ·
              refine ⟨1182486561048219755809237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1576648748064293007745649 1182486561048219755809237)
              ·
                refine ⟨27714528774567650526779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1182486561048219755809237 27714528774567650526779)
                ·
                  rfl

theorem cell23_1457294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 3, 2, 7].length) (baseStart_1457294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457294 prefixEnd_1457294 := by exact prefixLift 1457294
  have htrace : WordTrace (prefixWord ++ tailWord_1457294) baseStart_1457294 baseEnd_1457294 := by
    simpa [prefixWord, tailWord_1457294, baseEnd_1457294] using wordTrace_append hprefix tailTrace_1457294
  have hstable : (prefixWord ++ tailWord_1457294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457294).length < 2 ^ (prefixWord ++ tailWord_1457294).sum := by decide
  have hdescent : baseEnd_1457294 < baseStart_1457294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457304 : List Nat := [2, 1, 2, 4, 2, 1, 1, 2, 4, 1, 3]
def baseStart_1457304 : Nat := 118140960795 + 1457304 * 2 ^ 59
def prefixEnd_1457304 : Nat := 4983230072969 + 3 ^ 40 * 1457304 * 2
def baseEnd_1457304 : Nat := 748297411719871525097987

theorem tailTrace_1457304 : CollatzResearch.WordTrace tailWord_1457304 prefixEnd_1457304 748297411719871525097987 := by
  unfold tailWord_1457304
  simp only [CollatzResearch.WordTrace]
  refine ⟨26576121756221985276673483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35434829008295980368897977 26576121756221985276673483)
  ·
    refine ⟨39864182634332977915010225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26576121756221985276673483 39864182634332977915010225)
    ·
      refine ⟨29898136975749733436257669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39864182634332977915010225 29898136975749733436257669)
      ·
        refine ⟨5605900682953075019298313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29898136975749733436257669 5605900682953075019298313)
        ·
          refine ⟨4204425512214806264473735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5605900682953075019298313 4204425512214806264473735)
          ·
            refine ⟨6306638268322209396710603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4204425512214806264473735 6306638268322209396710603)
            ·
              refine ⟨9459957402483314095065905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6306638268322209396710603 9459957402483314095065905)
              ·
                refine ⟨7094968051862485571299429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9459957402483314095065905 7094968051862485571299429)
                ·
                  refine ⟨1330306509724216044618643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7094968051862485571299429 1330306509724216044618643)
                  ·
                    refine ⟨1995459764586324066927965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1330306509724216044618643 1995459764586324066927965)
                    ·
                      refine ⟨748297411719871525097987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1995459764586324066927965 748297411719871525097987)
                      ·
                        rfl

theorem cell23_1457304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 2, 4, 1, 3].length) (baseStart_1457304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457304 prefixEnd_1457304 := by exact prefixLift 1457304
  have htrace : WordTrace (prefixWord ++ tailWord_1457304) baseStart_1457304 baseEnd_1457304 := by
    simpa [prefixWord, tailWord_1457304, baseEnd_1457304] using wordTrace_append hprefix tailTrace_1457304
  have hstable : (prefixWord ++ tailWord_1457304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457304).length < 2 ^ (prefixWord ++ tailWord_1457304).sum := by decide
  have hdescent : baseEnd_1457304 < baseStart_1457304 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457322 : List Nat := [3, 1, 5, 1, 1, 2, 3, 2, 1, 2, 2]
def baseStart_1457322 : Nat := 118140960795 + 1457322 * 2 ^ 59
def prefixEnd_1457322 : Nat := 4983230072969 + 3 ^ 40 * 1457322 * 2
def baseEnd_1457322 : Nat := 748306654371652454672905

theorem tailTrace_1457322 : CollatzResearch.WordTrace tailWord_1457322 prefixEnd_1457322 748306654371652454672905 := by
  unfold tailWord_1457322
  simp only [CollatzResearch.WordTrace]
  refine ⟨13288225006594689906875555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35435266684252506418334813 13288225006594689906875555)
  ·
    refine ⟨19932337509892034860313333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13288225006594689906875555 19932337509892034860313333)
    ·
      refine ⟨1868656641552378268154375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19932337509892034860313333 1868656641552378268154375)
      ·
        refine ⟨2802984962328567402231563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1868656641552378268154375 2802984962328567402231563)
        ·
          refine ⟨4204477443492851103347345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2802984962328567402231563 4204477443492851103347345)
          ·
            refine ⟨3153358082619638327510509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4204477443492851103347345 3153358082619638327510509)
            ·
              refine ⟨1182509280982364372816441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3153358082619638327510509 1182509280982364372816441)
              ·
                refine ⟨886881960736773279612331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1182509280982364372816441 886881960736773279612331)
                ·
                  refine ⟨1330322941105159919418497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 886881960736773279612331 1330322941105159919418497)
                  ·
                    refine ⟨997742205828869939563873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1330322941105159919418497 997742205828869939563873)
                    ·
                      refine ⟨748306654371652454672905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 997742205828869939563873 748306654371652454672905)
                      ·
                        rfl

theorem cell23_1457322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 2, 1, 2, 2].length) (baseStart_1457322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457322 prefixEnd_1457322 := by exact prefixLift 1457322
  have htrace : WordTrace (prefixWord ++ tailWord_1457322) baseStart_1457322 baseEnd_1457322 := by
    simpa [prefixWord, tailWord_1457322, baseEnd_1457322] using wordTrace_append hprefix tailTrace_1457322
  have hstable : (prefixWord ++ tailWord_1457322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457322).length < 2 ^ (prefixWord ++ tailWord_1457322).sum := by decide
  have hdescent : baseEnd_1457322 < baseStart_1457322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457384 : List Nat := [2, 1, 4, 1, 2, 1, 3, 4, 5]
def baseStart_1457384 : Nat := 118140960795 + 1457384 * 2 ^ 59
def prefixEnd_1457384 : Nat := 4983230072969 + 3 ^ 40 * 1457384 * 2
def baseEnd_1457384 : Nat := 83148721130247912455291

theorem tailTrace_1457384 : CollatzResearch.WordTrace tailWord_1457384 prefixEnd_1457384 83148721130247912455291 := by
  unfold tailWord_1457384
  simp only [CollatzResearch.WordTrace]
  refine ⟨26577580676077072108129603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35436774234769429477506137 26577580676077072108129603)
  ·
    refine ⟨39866371014115608162194405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26577580676077072108129603 39866371014115608162194405)
    ·
      refine ⟨7474944565146676530411451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39866371014115608162194405 7474944565146676530411451)
      ·
        refine ⟨11212416847720014795617177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7474944565146676530411451 11212416847720014795617177)
        ·
          refine ⟨8409312635790011096712883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11212416847720014795617177 8409312635790011096712883)
          ·
            refine ⟨12613968953685016645069325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8409312635790011096712883 12613968953685016645069325)
            ·
              refine ⟨4730238357631881241900997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12613968953685016645069325 4730238357631881241900997)
              ·
                refine ⟨886919692055977732856437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4730238357631881241900997 886919692055977732856437)
                ·
                  refine ⟨83148721130247912455291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 886919692055977732856437 83148721130247912455291)
                  ·
                    rfl

theorem cell23_1457384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 3, 4, 5].length) (baseStart_1457384 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457384 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457384 prefixEnd_1457384 := by exact prefixLift 1457384
  have htrace : WordTrace (prefixWord ++ tailWord_1457384) baseStart_1457384 baseEnd_1457384 := by
    simpa [prefixWord, tailWord_1457384, baseEnd_1457384] using wordTrace_append hprefix tailTrace_1457384
  have hstable : (prefixWord ++ tailWord_1457384).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457384).length < 2 ^ (prefixWord ++ tailWord_1457384).sum := by decide
  have hdescent : baseEnd_1457384 < baseStart_1457384 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457417 : List Nat := [1, 2, 1, 1, 3, 3, 3, 1, 1, 3, 4]
def baseStart_1457417 : Nat := 118140960795 + 1457417 * 2 ^ 59
def prefixEnd_1457417 : Nat := 4983230072969 + 3 ^ 40 * 1457417 * 2
def baseEnd_1457417 : Nat := 748355435033829582984967

theorem tailTrace_1457417 : CollatzResearch.WordTrace tailWord_1457417 prefixEnd_1457417 748355435033829582984967 := by
  unfold tailWord_1457417
  simp only [CollatzResearch.WordTrace]
  refine ⟨53156364961034590852210505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35437576640689727234807003 53156364961034590852210505)
  ·
    refine ⟨39867273720775943139157879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53156364961034590852210505 39867273720775943139157879)
    ·
      refine ⟨59800910581163914708736819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39867273720775943139157879 59800910581163914708736819)
      ·
        refine ⟨89701365871745872063105229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59800910581163914708736819 89701365871745872063105229)
        ·
          refine ⟨33638012201904702023664461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89701365871745872063105229 33638012201904702023664461)
          ·
            refine ⟨12614254575714263258874173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33638012201904702023664461 12614254575714263258874173)
            ·
              refine ⟨4730345465892848722077815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12614254575714263258874173 4730345465892848722077815)
              ·
                refine ⟨7095518198839273083116723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4730345465892848722077815 7095518198839273083116723)
                ·
                  refine ⟨10643277298258909624675085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7095518198839273083116723 10643277298258909624675085)
                  ·
                    refine ⟨3991228986847091109253157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10643277298258909624675085 3991228986847091109253157)
                    ·
                      refine ⟨748355435033829582984967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3991228986847091109253157 748355435033829582984967)
                      ·
                        rfl

theorem cell23_1457417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 3, 4].length) (baseStart_1457417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457417 prefixEnd_1457417 := by exact prefixLift 1457417
  have htrace : WordTrace (prefixWord ++ tailWord_1457417) baseStart_1457417 baseEnd_1457417 := by
    simpa [prefixWord, tailWord_1457417, baseEnd_1457417] using wordTrace_append hprefix tailTrace_1457417
  have hstable : (prefixWord ++ tailWord_1457417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457417).length < 2 ^ (prefixWord ++ tailWord_1457417).sum := by decide
  have hdescent : baseEnd_1457417 < baseStart_1457417 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457591 : List Nat := [1, 1, 3, 1, 3, 2, 2, 2, 4, 1, 3]
def baseStart_1457591 : Nat := 118140960795 + 1457591 * 2 ^ 59
def prefixEnd_1457591 : Nat := 4983230072969 + 3 ^ 40 * 1457591 * 2
def baseEnd_1457591 : Nat := 748444780667711902209167

theorem tailTrace_1457591 : CollatzResearch.WordTrace tailWord_1457591 prefixEnd_1457591 748444780667711902209167 := by
  unfold tailWord_1457591
  simp only [CollatzResearch.WordTrace]
  refine ⟨53162711262404218569044627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35441807508269479046029751 53162711262404218569044627)
  ·
    refine ⟨79744066893606327853566941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53162711262404218569044627 79744066893606327853566941)
    ·
      refine ⟨29904025085102372945087603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79744066893606327853566941 29904025085102372945087603)
      ·
        refine ⟨44856037627653559417631405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29904025085102372945087603 44856037627653559417631405)
        ·
          refine ⟨16821014110370084781611777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44856037627653559417631405 16821014110370084781611777)
          ·
            refine ⟨12615760582777563586208833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16821014110370084781611777 12615760582777563586208833)
            ·
              refine ⟨9461820437083172689656625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12615760582777563586208833 9461820437083172689656625)
              ·
                refine ⟨7096365327812379517242469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9461820437083172689656625 7096365327812379517242469)
                ·
                  refine ⟨1330568498964821159482963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7096365327812379517242469 1330568498964821159482963)
                  ·
                    refine ⟨1995852748447231739224445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1330568498964821159482963 1995852748447231739224445)
                    ·
                      refine ⟨748444780667711902209167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1995852748447231739224445 748444780667711902209167)
                      ·
                        rfl

theorem cell23_1457591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 2, 4, 1, 3].length) (baseStart_1457591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457591 prefixEnd_1457591 := by exact prefixLift 1457591
  have htrace : WordTrace (prefixWord ++ tailWord_1457591) baseStart_1457591 baseEnd_1457591 := by
    simpa [prefixWord, tailWord_1457591, baseEnd_1457591] using wordTrace_append hprefix tailTrace_1457591
  have hstable : (prefixWord ++ tailWord_1457591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457591).length < 2 ^ (prefixWord ++ tailWord_1457591).sum := by decide
  have hdescent : baseEnd_1457591 < baseStart_1457591 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457614 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4]
def baseStart_1457614 : Nat := 118140960795 + 1457614 * 2 ^ 59
def prefixEnd_1457614 : Nat := 4983230072969 + 3 ^ 40 * 1457614 * 2
def baseEnd_1457614 : Nat := 748456590722765312221561

theorem tailTrace_1457614 : CollatzResearch.WordTrace tailWord_1457614 prefixEnd_1457614 748456590722765312221561 := by
  unfold tailWord_1457614
  simp only [CollatzResearch.WordTrace]
  refine ⟨6645443767665111687141487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35442366760880595664754597 6645443767665111687141487)
  ·
    refine ⟨9968165651497667530712231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6645443767665111687141487 9968165651497667530712231)
    ·
      refine ⟨14952248477246501296068347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9968165651497667530712231 14952248477246501296068347)
      ·
        refine ⟨22428372715869751944102521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14952248477246501296068347 22428372715869751944102521)
        ·
          refine ⟨16821279536902313958076891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22428372715869751944102521 16821279536902313958076891)
          ·
            refine ⟨25231919305353470937115337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16821279536902313958076891 25231919305353470937115337)
            ·
              refine ⟨18923939479015103202836503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25231919305353470937115337 18923939479015103202836503)
              ·
                refine ⟨28385909218522654804254755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18923939479015103202836503 28385909218522654804254755)
                ·
                  refine ⟨42578863827783982206382133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28385909218522654804254755 42578863827783982206382133)
                  ·
                    refine ⟨3991768483854748331848325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42578863827783982206382133 3991768483854748331848325)
                    ·
                      refine ⟨748456590722765312221561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3991768483854748331848325 748456590722765312221561)
                      ·
                        rfl

theorem cell23_1457614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 1, 5, 4].length) (baseStart_1457614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457614 prefixEnd_1457614 := by exact prefixLift 1457614
  have htrace : WordTrace (prefixWord ++ tailWord_1457614) baseStart_1457614 baseEnd_1457614 := by
    simpa [prefixWord, tailWord_1457614, baseEnd_1457614] using wordTrace_append hprefix tailTrace_1457614
  have hstable : (prefixWord ++ tailWord_1457614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457614).length < 2 ^ (prefixWord ++ tailWord_1457614).sum := by decide
  have hdescent : baseEnd_1457614 < baseStart_1457614 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457624 : List Nat := [2, 1, 2, 2, 2, 1, 4, 1, 2, 6]
def baseStart_1457624 : Nat := 118140960795 + 1457624 * 2 ^ 59
def prefixEnd_1457624 : Nat := 4983230072969 + 3 ^ 40 * 1457624 * 2
def baseEnd_1457624 : Nat := 249487241843103424365505

theorem tailTrace_1457624 : CollatzResearch.WordTrace tailWord_1457624 prefixEnd_1457624 249487241843103424365505 := by
  unfold tailWord_1457624
  simp only [CollatzResearch.WordTrace]
  refine ⟨26581957435642332602497963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35442609914189776803330617 26581957435642332602497963)
  ·
    refine ⟨39872936153463498903746945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26581957435642332602497963 39872936153463498903746945)
    ·
      refine ⟨29904702115097624177810209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39872936153463498903746945 29904702115097624177810209)
      ·
        refine ⟨22428526586323218133357657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29904702115097624177810209 22428526586323218133357657)
        ·
          refine ⟨16821394939742413600018243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22428526586323218133357657 16821394939742413600018243)
          ·
            refine ⟨25232092409613620400027365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16821394939742413600018243 25232092409613620400027365)
            ·
              refine ⟨4731017326802553825005131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25232092409613620400027365 4731017326802553825005131)
              ·
                refine ⟨7096525990203830737507697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4731017326802553825005131 7096525990203830737507697)
                ·
                  refine ⟨5322394492652873053130773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7096525990203830737507697 5322394492652873053130773)
                  ·
                    refine ⟨249487241843103424365505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5322394492652873053130773 249487241843103424365505)
                    ·
                      rfl

theorem cell23_1457624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 2, 6].length) (baseStart_1457624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457624 prefixEnd_1457624 := by exact prefixLift 1457624
  have htrace : WordTrace (prefixWord ++ tailWord_1457624) baseStart_1457624 baseEnd_1457624 := by
    simpa [prefixWord, tailWord_1457624, baseEnd_1457624] using wordTrace_append hprefix tailTrace_1457624
  have hstable : (prefixWord ++ tailWord_1457624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457624).length < 2 ^ (prefixWord ++ tailWord_1457624).sum := by decide
  have hdescent : baseEnd_1457624 < baseStart_1457624 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457625 : List Nat := [1, 2, 1, 2, 4, 3, 3, 1, 2, 1, 3]
def baseStart_1457625 : Nat := 118140960795 + 1457625 * 2 ^ 59
def prefixEnd_1457625 : Nat := 4983230072969 + 3 ^ 40 * 1457625 * 2
def baseEnd_1457625 : Nat := 748462239009964769184011

theorem tailTrace_1457625 : CollatzResearch.WordTrace tailWord_1457625 prefixEnd_1457625 748462239009964769184011 := by
  unfold tailWord_1457625
  simp only [CollatzResearch.WordTrace]
  refine ⟨53163951344281042375782329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35442634229520694917188219 53163951344281042375782329)
  ·
    refine ⟨39872963508210781781836747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53163951344281042375782329 39872963508210781781836747)
    ·
      refine ⟨59809445262316172672755121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39872963508210781781836747 59809445262316172672755121)
      ·
        refine ⟨44857083946737129504566341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59809445262316172672755121 44857083946737129504566341)
        ·
          refine ⟨8410703240013211782106189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44857083946737129504566341 8410703240013211782106189)
          ·
            refine ⟨3154013715004954418289821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8410703240013211782106189 3154013715004954418289821)
            ·
              refine ⟨1182755143126857906858683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3154013715004954418289821 1182755143126857906858683)
              ·
                refine ⟨1774132714690286860288025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1182755143126857906858683 1774132714690286860288025)
                ·
                  refine ⟨1330599536017715145216019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1774132714690286860288025 1330599536017715145216019)
                  ·
                    refine ⟨1995899304026572717824029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1330599536017715145216019 1995899304026572717824029)
                    ·
                      refine ⟨748462239009964769184011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1995899304026572717824029 748462239009964769184011)
                      ·
                        rfl

theorem cell23_1457625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 3, 3, 1, 2, 1, 3].length) (baseStart_1457625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457625 prefixEnd_1457625 := by exact prefixLift 1457625
  have htrace : WordTrace (prefixWord ++ tailWord_1457625) baseStart_1457625 baseEnd_1457625 := by
    simpa [prefixWord, tailWord_1457625, baseEnd_1457625] using wordTrace_append hprefix tailTrace_1457625
  have hstable : (prefixWord ++ tailWord_1457625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457625).length < 2 ^ (prefixWord ++ tailWord_1457625).sum := by decide
  have hdescent : baseEnd_1457625 < baseStart_1457625 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457635 : List Nat := [1, 1, 1, 6, 2, 2, 2, 2, 1, 3, 2]
def baseStart_1457635 : Nat := 118140960795 + 1457635 * 2 ^ 59
def prefixEnd_1457635 : Nat := 4983230072969 + 3 ^ 40 * 1457635 * 2
def baseEnd_1457635 : Nat := 748467373816509730058965

theorem tailTrace_1457635 : CollatzResearch.WordTrace tailWord_1457635 prefixEnd_1457635 748467373816509730058965 := by
  unfold tailWord_1457635
  simp only [CollatzResearch.WordTrace]
  refine ⟨53164316074244814083646359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35442877382829876055764239 53164316074244814083646359)
  ·
    refine ⟨79746474111367221125469539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53164316074244814083646359 79746474111367221125469539)
    ·
      refine ⟨119619711167050831688204309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79746474111367221125469539 119619711167050831688204309)
      ·
        refine ⟨5607173960955507735384577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 119619711167050831688204309 5607173960955507735384577)
        ·
          refine ⟨4205380470716630801538433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5607173960955507735384577 4205380470716630801538433)
          ·
            refine ⟨3154035353037473101153825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4205380470716630801538433 3154035353037473101153825)
            ·
              refine ⟨2365526514778104825865369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3154035353037473101153825 2365526514778104825865369)
              ·
                refine ⟨1774144886083578619399027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2365526514778104825865369 1774144886083578619399027)
                ·
                  refine ⟨2661217329125367929098541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1774144886083578619399027 2661217329125367929098541)
                  ·
                    refine ⟨997956498422012973411953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2661217329125367929098541 997956498422012973411953)
                    ·
                      refine ⟨748467373816509730058965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 997956498422012973411953 748467373816509730058965)
                      ·
                        rfl

theorem cell23_1457635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_1457635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457635 prefixEnd_1457635 := by exact prefixLift 1457635
  have htrace : WordTrace (prefixWord ++ tailWord_1457635) baseStart_1457635 baseEnd_1457635 := by
    simpa [prefixWord, tailWord_1457635, baseEnd_1457635] using wordTrace_append hprefix tailTrace_1457635
  have hstable : (prefixWord ++ tailWord_1457635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457635).length < 2 ^ (prefixWord ++ tailWord_1457635).sum := by decide
  have hdescent : baseEnd_1457635 < baseStart_1457635 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457644 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 4]
def baseStart_1457644 : Nat := 118140960795 + 1457644 * 2 ^ 59
def prefixEnd_1457644 : Nat := 4983230072969 + 3 ^ 40 * 1457644 * 2
def baseEnd_1457644 : Nat := 748471995142400194846423

theorem tailTrace_1457644 : CollatzResearch.WordTrace tailWord_1457644 prefixEnd_1457644 748471995142400194846423 := by
  unfold tailWord_1457644
  simp only [CollatzResearch.WordTrace]
  refine ⟨26582322165606104310361993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35443096220808139080482657 26582322165606104310361993)
  ·
    refine ⟨19936741624204578232771495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26582322165606104310361993 19936741624204578232771495)
    ·
      refine ⟨29905112436306867349157243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19936741624204578232771495 29905112436306867349157243)
      ·
        refine ⟨44857668654460301023735865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29905112436306867349157243 44857668654460301023735865)
        ·
          refine ⟨33643251490845225767801899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44857668654460301023735865 33643251490845225767801899)
          ·
            refine ⟨50464877236267838651702849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33643251490845225767801899 50464877236267838651702849)
            ·
              refine ⟨37848657927200878988777137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50464877236267838651702849 37848657927200878988777137)
              ·
                refine ⟨28386493445400659241582853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37848657927200878988777137 28386493445400659241582853)
                ·
                  refine ⟨5322467521012623607796785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28386493445400659241582853 5322467521012623607796785)
                  ·
                    refine ⟨3991850640759467705847589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5322467521012623607796785 3991850640759467705847589)
                    ·
                      refine ⟨748471995142400194846423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3991850640759467705847589 748471995142400194846423)
                      ·
                        rfl

theorem cell23_1457644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_1457644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457644 prefixEnd_1457644 := by exact prefixLift 1457644
  have htrace : WordTrace (prefixWord ++ tailWord_1457644) baseStart_1457644 baseEnd_1457644 := by
    simpa [prefixWord, tailWord_1457644, baseEnd_1457644] using wordTrace_append hprefix tailTrace_1457644
  have hstable : (prefixWord ++ tailWord_1457644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457644).length < 2 ^ (prefixWord ++ tailWord_1457644).sum := by decide
  have hdescent : baseEnd_1457644 < baseStart_1457644 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457648 : List Nat := [2, 1, 1, 1, 3, 4, 1, 2, 4, 2, 2]
def baseStart_1457648 : Nat := 118140960795 + 1457648 * 2 ^ 59
def prefixEnd_1457648 : Nat := 4983230072969 + 3 ^ 40 * 1457648 * 2
def baseEnd_1457648 : Nat := 748474049065018179196405

theorem tailTrace_1457648 : CollatzResearch.WordTrace tailWord_1457648 prefixEnd_1457648 748474049065018179196405 := by
  unfold tailWord_1457648
  simp only [CollatzResearch.WordTrace]
  refine ⟨26582395111598858651934799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35443193482131811535913065 26582395111598858651934799)
  ·
    refine ⟨39873592667398287977902199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26582395111598858651934799 39873592667398287977902199)
    ·
      refine ⟨59810389001097431966853299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39873592667398287977902199 59810389001097431966853299)
      ·
        refine ⟨89715583501646147950279949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59810389001097431966853299 89715583501646147950279949)
        ·
          refine ⟨33643343813117305481354981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 89715583501646147950279949 33643343813117305481354981)
          ·
            refine ⟨6308126964959494777754059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33643343813117305481354981 6308126964959494777754059)
            ·
              refine ⟨9462190447439242166631089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6308126964959494777754059 9462190447439242166631089)
              ·
                refine ⟨7096642835579431624973317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9462190447439242166631089 7096642835579431624973317)
                ·
                  refine ⟨1330620531671143429682497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7096642835579431624973317 1330620531671143429682497)
                  ·
                    refine ⟨997965398753357572261873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1330620531671143429682497 997965398753357572261873)
                    ·
                      refine ⟨748474049065018179196405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 997965398753357572261873 748474049065018179196405)
                      ·
                        rfl

theorem cell23_1457648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 4, 1, 2, 4, 2, 2].length) (baseStart_1457648 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457648 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457648 prefixEnd_1457648 := by exact prefixLift 1457648
  have htrace : WordTrace (prefixWord ++ tailWord_1457648) baseStart_1457648 baseEnd_1457648 := by
    simpa [prefixWord, tailWord_1457648, baseEnd_1457648] using wordTrace_append hprefix tailTrace_1457648
  have hstable : (prefixWord ++ tailWord_1457648).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457648).length < 2 ^ (prefixWord ++ tailWord_1457648).sum := by decide
  have hdescent : baseEnd_1457648 < baseStart_1457648 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457671 : List Nat := [1, 1, 4, 3, 2, 1, 3, 1, 7]
def baseStart_1457671 : Nat := 118140960795 + 1457671 * 2 ^ 59
def prefixEnd_1457671 : Nat := 4983230072969 + 3 ^ 40 * 1457671 * 2
def baseEnd_1457671 : Nat := 83165095457785732134311

theorem tailTrace_1457671 : CollatzResearch.WordTrace tailWord_1457671 prefixEnd_1457671 83165095457785732134311 := by
  unfold tailWord_1457671
  simp only [CollatzResearch.WordTrace]
  refine ⟨53165629102114392231956867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35443752734742928154637911 53165629102114392231956867)
  ·
    refine ⟨79748443653171588347935301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53165629102114392231956867 79748443653171588347935301)
    ·
      refine ⟨14952833184969672815237869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79748443653171588347935301 14952833184969672815237869)
      ·
        refine ⟨5607312444363627305714201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14952833184969672815237869 5607312444363627305714201)
        ·
          refine ⟨4205484333272720479285651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5607312444363627305714201 4205484333272720479285651)
          ·
            refine ⟨6308226499909080718928477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4205484333272720479285651 6308226499909080718928477)
            ·
              refine ⟨2365584937465905269598179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6308226499909080718928477 2365584937465905269598179)
              ·
                refine ⟨3548377406198857904397269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2365584937465905269598179 3548377406198857904397269)
                ·
                  refine ⟨83165095457785732134311, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3548377406198857904397269 83165095457785732134311)
                  ·
                    rfl

theorem cell23_1457671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 3, 1, 7].length) (baseStart_1457671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457671 prefixEnd_1457671 := by exact prefixLift 1457671
  have htrace : WordTrace (prefixWord ++ tailWord_1457671) baseStart_1457671 baseEnd_1457671 := by
    simpa [prefixWord, tailWord_1457671, baseEnd_1457671] using wordTrace_append hprefix tailTrace_1457671
  have hstable : (prefixWord ++ tailWord_1457671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457671).length < 2 ^ (prefixWord ++ tailWord_1457671).sum := by decide
  have hdescent : baseEnd_1457671 < baseStart_1457671 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457738 : List Nat := [3, 1, 2, 1, 1, 3, 3, 1, 2, 4, 2]
def baseStart_1457738 : Nat := 118140960795 + 1457738 * 2 ^ 59
def prefixEnd_1457738 : Nat := 4983230072969 + 3 ^ 40 * 1457738 * 2
def baseEnd_1457738 : Nat := 748520262323922827070991

theorem tailTrace_1457738 : CollatzResearch.WordTrace tailWord_1457738 prefixEnd_1457738 748520262323922827070991 := by
  unfold tailWord_1457738
  simp only [CollatzResearch.WordTrace]
  refine ⟨13292018198217915668661467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35445381861914441783097245 13292018198217915668661467)
  ·
    refine ⟨19938027297326873502992201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13292018198217915668661467 19938027297326873502992201)
    ·
      refine ⟨14953520472995155127244151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19938027297326873502992201 14953520472995155127244151)
      ·
        refine ⟨22430280709492732690866227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14953520472995155127244151 22430280709492732690866227)
        ·
          refine ⟨33645421064239099036299341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22430280709492732690866227 33645421064239099036299341)
          ·
            refine ⟨12617032899089662138612253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33645421064239099036299341 12617032899089662138612253)
            ·
              refine ⟨4731387337158623301979595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12617032899089662138612253 4731387337158623301979595)
              ·
                refine ⟨7097081005737934952969393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4731387337158623301979595 7097081005737934952969393)
                ·
                  refine ⟨5322810754303451214727045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7097081005737934952969393 5322810754303451214727045)
                  ·
                    refine ⟨998027016431897102761321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5322810754303451214727045 998027016431897102761321)
                    ·
                      refine ⟨748520262323922827070991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 998027016431897102761321 748520262323922827070991)
                      ·
                        rfl

theorem cell23_1457738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 3, 1, 2, 4, 2].length) (baseStart_1457738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457738 prefixEnd_1457738 := by exact prefixLift 1457738
  have htrace : WordTrace (prefixWord ++ tailWord_1457738) baseStart_1457738 baseEnd_1457738 := by
    simpa [prefixWord, tailWord_1457738, baseEnd_1457738] using wordTrace_append hprefix tailTrace_1457738
  have hstable : (prefixWord ++ tailWord_1457738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457738).length < 2 ^ (prefixWord ++ tailWord_1457738).sum := by decide
  have hdescent : baseEnd_1457738 < baseStart_1457738 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457748 : List Nat := [2, 4, 1, 1, 1, 2, 3, 2, 3, 4]
def baseStart_1457748 : Nat := 118140960795 + 1457748 * 2 ^ 59
def prefixEnd_1457748 : Nat := 4983230072969 + 3 ^ 40 * 1457748 * 2
def baseEnd_1457748 : Nat := 249508465710155929315315

theorem tailTrace_1457748 : CollatzResearch.WordTrace tailWord_1457748 prefixEnd_1457748 249508465710155929315315 := by
  unfold tailWord_1457748
  simp only [CollatzResearch.WordTrace]
  refine ⟨26584218761417717191254949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35445625015223622921673265 26584218761417717191254949)
  ·
    refine ⟨4984541017765821973360303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26584218761417717191254949 4984541017765821973360303)
    ·
      refine ⟨7476811526648732960040455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4984541017765821973360303 7476811526648732960040455)
      ·
        refine ⟨11215217289973099440060683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7476811526648732960040455 11215217289973099440060683)
        ·
          refine ⟨16822825934959649160091025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11215217289973099440060683 16822825934959649160091025)
          ·
            refine ⟨12617119451219736870068269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16822825934959649160091025 12617119451219736870068269)
            ·
              refine ⟨4731419794207401326275601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12617119451219736870068269 4731419794207401326275601)
              ·
                refine ⟨3548564845655550994706701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4731419794207401326275601 3548564845655550994706701)
                ·
                  refine ⟨1330711817120831623015013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3548564845655550994706701 1330711817120831623015013)
                  ·
                    refine ⟨249508465710155929315315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1330711817120831623015013 249508465710155929315315)
                    ·
                      rfl

theorem cell23_1457748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 3, 2, 3, 4].length) (baseStart_1457748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457748 prefixEnd_1457748 := by exact prefixLift 1457748
  have htrace : WordTrace (prefixWord ++ tailWord_1457748) baseStart_1457748 baseEnd_1457748 := by
    simpa [prefixWord, tailWord_1457748, baseEnd_1457748] using wordTrace_append hprefix tailTrace_1457748
  have hstable : (prefixWord ++ tailWord_1457748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457748).length < 2 ^ (prefixWord ++ tailWord_1457748).sum := by decide
  have hdescent : baseEnd_1457748 < baseStart_1457748 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457765 : List Nat := [1, 3, 1, 3, 3, 1, 1, 5, 1, 4]
def baseStart_1457765 : Nat := 118140960795 + 1457765 * 2 ^ 59
def prefixEnd_1457765 : Nat := 4983230072969 + 3 ^ 40 * 1457765 * 2
def baseEnd_1457765 : Nat := 249511375433864740477789

theorem tailTrace_1457765 : CollatzResearch.WordTrace tailWord_1457765 prefixEnd_1457765 249511375433864740477789 := by
  unfold tailWord_1457765
  simp only [CollatzResearch.WordTrace]
  refine ⟨53169057563773846285878749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35446038375849230857252499 53169057563773846285878749)
  ·
    refine ⟨19938396586415192357204531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53169057563773846285878749 19938396586415192357204531)
    ·
      refine ⟨29907594879622788535806797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19938396586415192357204531 29907594879622788535806797)
      ·
        refine ⟨11215348079858545700927549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29907594879622788535806797 11215348079858545700927549)
        ·
          refine ⟨4205755529946954637847831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11215348079858545700927549 4205755529946954637847831)
          ·
            refine ⟨6308633294920431956771747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4205755529946954637847831 6308633294920431956771747)
            ·
              refine ⟨9462949942380647935157621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6308633294920431956771747 9462949942380647935157621)
              ·
                refine ⟨887151557098185743921027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9462949942380647935157621 887151557098185743921027)
                ·
                  refine ⟨1330727335647278615881541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 887151557098185743921027 1330727335647278615881541)
                  ·
                    refine ⟨249511375433864740477789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1330727335647278615881541 249511375433864740477789)
                    ·
                      rfl

theorem cell23_1457765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 5, 1, 4].length) (baseStart_1457765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457765 prefixEnd_1457765 := by exact prefixLift 1457765
  have htrace : WordTrace (prefixWord ++ tailWord_1457765) baseStart_1457765 baseEnd_1457765 := by
    simpa [prefixWord, tailWord_1457765, baseEnd_1457765] using wordTrace_append hprefix tailTrace_1457765
  have hstable : (prefixWord ++ tailWord_1457765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457765).length < 2 ^ (prefixWord ++ tailWord_1457765).sum := by decide
  have hdescent : baseEnd_1457765 < baseStart_1457765 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457778 : List Nat := [3, 2, 1, 2, 3, 1, 3, 2, 6]
def baseStart_1457778 : Nat := 118140960795 + 1457778 * 2 ^ 59
def prefixEnd_1457778 : Nat := 4983230072969 + 3 ^ 40 * 1457778 * 2
def baseEnd_1457778 : Nat := 83171200172233630063423

theorem tailTrace_1457778 : CollatzResearch.WordTrace tailWord_1457778 prefixEnd_1457778 83171200172233630063423 := by
  unfold tailWord_1457778
  simp only [CollatzResearch.WordTrace]
  refine ⟨13292382928181687376525497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35446354475151166337401325 13292382928181687376525497)
  ·
    refine ⟨9969287196136265532394123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13292382928181687376525497 9969287196136265532394123)
    ·
      refine ⟨14953930794204398298591185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9969287196136265532394123 14953930794204398298591185)
      ·
        refine ⟨11215448095653298723943389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14953930794204398298591185 11215448095653298723943389)
        ·
          refine ⟨4205793035869987021478771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11215448095653298723943389 4205793035869987021478771)
          ·
            refine ⟨6308689553804980532218157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4205793035869987021478771 6308689553804980532218157)
            ·
              refine ⟨2365758582676867699581809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6308689553804980532218157 2365758582676867699581809)
              ·
                refine ⟨1774318937007650774686357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2365758582676867699581809 1774318937007650774686357)
                ·
                  refine ⟨83171200172233630063423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1774318937007650774686357 83171200172233630063423)
                  ·
                    rfl

theorem cell23_1457778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 3, 2, 6].length) (baseStart_1457778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457778 prefixEnd_1457778 := by exact prefixLift 1457778
  have htrace : WordTrace (prefixWord ++ tailWord_1457778) baseStart_1457778 baseEnd_1457778 := by
    simpa [prefixWord, tailWord_1457778, baseEnd_1457778] using wordTrace_append hprefix tailTrace_1457778
  have hstable : (prefixWord ++ tailWord_1457778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457778).length < 2 ^ (prefixWord ++ tailWord_1457778).sum := by decide
  have hdescent : baseEnd_1457778 < baseStart_1457778 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457782 : List Nat := [5, 1, 1, 2, 2, 1, 2, 4, 1, 4]
def baseStart_1457782 : Nat := 118140960795 + 1457782 * 2 ^ 59
def prefixEnd_1457782 : Nat := 4983230072969 + 3 ^ 40 * 1457782 * 2
def baseEnd_1457782 : Nat := 249514285157573551640263

theorem tailTrace_1457782 : CollatzResearch.WordTrace tailWord_1457782 prefixEnd_1457782 249514285157573551640263 := by
  unfold tailWord_1457782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3323104850294516136827975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35446451736474838792831733 3323104850294516136827975)
  ·
    refine ⟨4984657275441774205241963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3323104850294516136827975 4984657275441774205241963)
    ·
      refine ⟨7476985913162661307862945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4984657275441774205241963 7476985913162661307862945)
      ·
        refine ⟨5607739434871995980897209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7476985913162661307862945 5607739434871995980897209)
        ·
          refine ⟨4205804576153996985672907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5607739434871995980897209 4205804576153996985672907)
          ·
            refine ⟨6308706864230995478509361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4205804576153996985672907 6308706864230995478509361)
            ·
              refine ⟨4731530148173246608882021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6308706864230995478509361 4731530148173246608882021)
              ·
                refine ⟨887161902782483739165379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4731530148173246608882021 887161902782483739165379)
                ·
                  refine ⟨1330742854173725608748069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 887161902782483739165379 1330742854173725608748069)
                  ·
                    refine ⟨249514285157573551640263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1330742854173725608748069 249514285157573551640263)
                    ·
                      rfl

theorem cell23_1457782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_1457782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457782 prefixEnd_1457782 := by exact prefixLift 1457782
  have htrace : WordTrace (prefixWord ++ tailWord_1457782) baseStart_1457782 baseEnd_1457782 := by
    simpa [prefixWord, tailWord_1457782, baseEnd_1457782] using wordTrace_append hprefix tailTrace_1457782
  have hstable : (prefixWord ++ tailWord_1457782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457782).length < 2 ^ (prefixWord ++ tailWord_1457782).sum := by decide
  have hdescent : baseEnd_1457782 < baseStart_1457782 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457821 : List Nat := [1, 4, 2, 1, 1, 1, 1, 3, 3, 6]
def baseStart_1457821 : Nat := 118140960795 + 1457821 * 2 ^ 59
def prefixEnd_1457821 : Nat := 4983230072969 + 3 ^ 40 * 1457821 * 2
def baseEnd_1457821 : Nat := 249520960406082000777703

theorem tailTrace_1457821 : CollatzResearch.WordTrace tailWord_1457821 prefixEnd_1457821 249520960406082000777703 := by
  unfold tailWord_1457821
  simp only [CollatzResearch.WordTrace]
  refine ⟨53171100051570967849917317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35447400034380645233278211 53171100051570967849917317)
  ·
    refine ⟨9969581259669556471859497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53171100051570967849917317 9969581259669556471859497)
    ·
      refine ⟨7477185944752167353894623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9969581259669556471859497 7477185944752167353894623)
      ·
        refine ⟨11215778917128251030841935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7477185944752167353894623 11215778917128251030841935)
        ·
          refine ⟨16823668375692376546262903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11215778917128251030841935 16823668375692376546262903)
          ·
            refine ⟨25235502563538564819394355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16823668375692376546262903 25235502563538564819394355)
            ·
              refine ⟨37853253845307847229091533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25235502563538564819394355 37853253845307847229091533)
              ·
                refine ⟨14194970191990442710909325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37853253845307847229091533 14194970191990442710909325)
                ·
                  refine ⟨5323113821996416016590997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14194970191990442710909325 5323113821996416016590997)
                  ·
                    refine ⟨249520960406082000777703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5323113821996416016590997 249520960406082000777703)
                    ·
                      rfl

theorem cell23_1457821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 3, 3, 6].length) (baseStart_1457821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457821 prefixEnd_1457821 := by exact prefixLift 1457821
  have htrace : WordTrace (prefixWord ++ tailWord_1457821) baseStart_1457821 baseEnd_1457821 := by
    simpa [prefixWord, tailWord_1457821, baseEnd_1457821] using wordTrace_append hprefix tailTrace_1457821
  have hstable : (prefixWord ++ tailWord_1457821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457821).length < 2 ^ (prefixWord ++ tailWord_1457821).sum := by decide
  have hdescent : baseEnd_1457821 < baseStart_1457821 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457882 : List Nat := [3, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3]
def baseStart_1457882 : Nat := 118140960795 + 1457882 * 2 ^ 59
def prefixEnd_1457882 : Nat := 4983230072969 + 3 ^ 40 * 1457882 * 2
def baseEnd_1457882 : Nat := 748594203538170263670329

theorem tailTrace_1457882 : CollatzResearch.WordTrace tailWord_1457882 prefixEnd_1457882 748594203538170263670329 := by
  unfold tailWord_1457882
  simp only [CollatzResearch.WordTrace]
  refine ⟨13293331226087493816971975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35448883269566650178591933 13293331226087493816971975)
  ·
    refine ⟨19939996839131240725457963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13293331226087493816971975 19939996839131240725457963)
    ·
      refine ⟨29909995258696861088186945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19939996839131240725457963 29909995258696861088186945)
      ·
        refine ⟨22432496444022645816140209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29909995258696861088186945 22432496444022645816140209)
        ·
          refine ⟨16824372333016984362105157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22432496444022645816140209 16824372333016984362105157)
          ·
            refine ⟨3154569812440684567894717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16824372333016984362105157 3154569812440684567894717)
            ·
              refine ⟨1182963679665256712960519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3154569812440684567894717 1182963679665256712960519)
              ·
                refine ⟨1774445519497885069440779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1182963679665256712960519 1774445519497885069440779)
                ·
                  refine ⟨2661668279246827604161169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1774445519497885069440779 2661668279246827604161169)
                  ·
                    refine ⟨1996251209435120703120877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2661668279246827604161169 1996251209435120703120877)
                    ·
                      refine ⟨748594203538170263670329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1996251209435120703120877 748594203538170263670329)
                      ·
                        rfl

theorem cell23_1457882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 1, 1, 2, 3].length) (baseStart_1457882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457882 prefixEnd_1457882 := by exact prefixLift 1457882
  have htrace : WordTrace (prefixWord ++ tailWord_1457882) baseStart_1457882 baseEnd_1457882 := by
    simpa [prefixWord, tailWord_1457882, baseEnd_1457882] using wordTrace_append hprefix tailTrace_1457882
  have hstable : (prefixWord ++ tailWord_1457882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457882).length < 2 ^ (prefixWord ++ tailWord_1457882).sum := by decide
  have hdescent : baseEnd_1457882 < baseStart_1457882 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457885 : List Nat := [1, 4, 3, 3, 2, 10]
def baseStart_1457885 : Nat := 118140960795 + 1457885 * 2 ^ 59
def prefixEnd_1457885 : Nat := 4983230072969 + 3 ^ 40 * 1457885 * 2
def baseEnd_1457885 : Nat := 3080640921728945481205

theorem tailTrace_1457885 : CollatzResearch.WordTrace tailWord_1457885 prefixEnd_1457885 3080640921728945481205 := by
  unfold tailWord_1457885
  simp only [CollatzResearch.WordTrace]
  refine ⟨53173434323339106780247109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35448956215559404520164739 53173434323339106780247109)
  ·
    refine ⟨9970018935626082521296333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53173434323339106780247109 9970018935626082521296333)
    ·
      refine ⟨3738757100859780945486125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9970018935626082521296333 3738757100859780945486125)
      ·
        refine ⟨1402033912822417854557297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3738757100859780945486125 1402033912822417854557297)
        ·
          refine ⟨1051525434616813390917973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1402033912822417854557297 1051525434616813390917973)
          ·
            refine ⟨3080640921728945481205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1051525434616813390917973 3080640921728945481205)
            ·
              rfl

theorem cell23_1457885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 10].length) (baseStart_1457885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457885 prefixEnd_1457885 := by exact prefixLift 1457885
  have htrace : WordTrace (prefixWord ++ tailWord_1457885) baseStart_1457885 baseEnd_1457885 := by
    simpa [prefixWord, tailWord_1457885, baseEnd_1457885] using wordTrace_append hprefix tailTrace_1457885
  have hstable : (prefixWord ++ tailWord_1457885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457885).length < 2 ^ (prefixWord ++ tailWord_1457885).sum := by decide
  have hdescent : baseEnd_1457885 < baseStart_1457885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457896 : List Nat := [2, 1, 4, 1, 3, 1, 4, 2, 1, 2, 2]
def baseStart_1457896 : Nat := 118140960795 + 1457896 * 2 ^ 59
def prefixEnd_1457896 : Nat := 4983230072969 + 3 ^ 40 * 1457896 * 2
def baseEnd_1457896 : Nat := 748601392267333208895265

theorem tailTrace_1457896 : CollatzResearch.WordTrace tailWord_1457896 prefixEnd_1457896 748601392267333208895265 := by
  unfold tailWord_1457896
  simp only [CollatzResearch.WordTrace]
  refine ⟨26586917763149627829448771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35449223684199503772598361 26586917763149627829448771)
  ·
    refine ⟨39880376644724441744173157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26586917763149627829448771 39880376644724441744173157)
    ·
      refine ⟨7477570620885832827032467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 39880376644724441744173157 7477570620885832827032467)
      ·
        refine ⟨11216355931328749240548701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7477570620885832827032467 11216355931328749240548701)
        ·
          refine ⟨4206133474248280965205763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11216355931328749240548701 4206133474248280965205763)
          ·
            refine ⟨6309200211372421447808645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4206133474248280965205763 6309200211372421447808645)
            ·
              refine ⟨1182975039632329021464121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6309200211372421447808645 1182975039632329021464121)
              ·
                refine ⟨887231279724246766098091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1182975039632329021464121 887231279724246766098091)
                ·
                  refine ⟨1330846919586370149147137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 887231279724246766098091 1330846919586370149147137)
                  ·
                    refine ⟨998135189689777611860353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1330846919586370149147137 998135189689777611860353)
                    ·
                      refine ⟨748601392267333208895265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 998135189689777611860353 748601392267333208895265)
                      ·
                        rfl

theorem cell23_1457896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 2, 1, 2, 2].length) (baseStart_1457896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457896 prefixEnd_1457896 := by exact prefixLift 1457896
  have htrace : WordTrace (prefixWord ++ tailWord_1457896) baseStart_1457896 baseEnd_1457896 := by
    simpa [prefixWord, tailWord_1457896, baseEnd_1457896] using wordTrace_append hprefix tailTrace_1457896
  have hstable : (prefixWord ++ tailWord_1457896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457896).length < 2 ^ (prefixWord ++ tailWord_1457896).sum := by decide
  have hdescent : baseEnd_1457896 < baseStart_1457896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457905 : List Nat := [1, 2, 2, 2, 2, 3, 1, 2, 3, 3, 2]
def baseStart_1457905 : Nat := 118140960795 + 1457905 * 2 ^ 59
def prefixEnd_1457905 : Nat := 4983230072969 + 3 ^ 40 * 1457905 * 2
def baseEnd_1457905 : Nat := 748606013593223673682723

theorem tailTrace_1457905 : CollatzResearch.WordTrace tailWord_1457905 prefixEnd_1457905 748606013593223673682723 := by
  unfold tailWord_1457905
  simp only [CollatzResearch.WordTrace]
  refine ⟨53174163783266650195975169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35449442522177766797316779 53174163783266650195975169)
  ·
    refine ⟨39880622837449987646981377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53174163783266650195975169 39880622837449987646981377)
    ·
      refine ⟨29910467128087490735236033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39880622837449987646981377 29910467128087490735236033)
      ·
        refine ⟨22432850346065618051427025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29910467128087490735236033 22432850346065618051427025)
        ·
          refine ⟨16824637759549213538570269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22432850346065618051427025 16824637759549213538570269)
          ·
            refine ⟨6309239159830955076963851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16824637759549213538570269 6309239159830955076963851)
            ·
              refine ⟨9463858739746432615445777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6309239159830955076963851 9463858739746432615445777)
              ·
                refine ⟨7097894054809824461584333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9463858739746432615445777 7097894054809824461584333)
                ·
                  refine ⟨2661710270553684173094125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7097894054809824461584333 2661710270553684173094125)
                  ·
                    refine ⟨998141351457631564910297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2661710270553684173094125 998141351457631564910297)
                    ·
                      refine ⟨748606013593223673682723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 998141351457631564910297 748606013593223673682723)
                      ·
                        rfl

theorem cell23_1457905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 2, 3, 3, 2].length) (baseStart_1457905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457905 prefixEnd_1457905 := by exact prefixLift 1457905
  have htrace : WordTrace (prefixWord ++ tailWord_1457905) baseStart_1457905 baseEnd_1457905 := by
    simpa [prefixWord, tailWord_1457905, baseEnd_1457905] using wordTrace_append hprefix tailTrace_1457905
  have hstable : (prefixWord ++ tailWord_1457905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457905).length < 2 ^ (prefixWord ++ tailWord_1457905).sum := by decide
  have hdescent : baseEnd_1457905 < baseStart_1457905 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457911 : List Nat := [1, 1, 3, 1, 1, 1, 5, 1, 1, 8]
def baseStart_1457911 : Nat := 118140960795 + 1457911 * 2 ^ 59
def prefixEnd_1457911 : Nat := 4983230072969 + 3 ^ 40 * 1457911 * 2
def baseEnd_1457911 : Nat := 249536364825716883402565

theorem tailTrace_1457911 : CollatzResearch.WordTrace tailWord_1457911 prefixEnd_1457911 249536364825716883402565 := by
  unfold tailWord_1457911
  simp only [CollatzResearch.WordTrace]
  refine ⟨53174382621244913220693587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35449588414163275480462391 53174382621244913220693587)
  ·
    refine ⟨79761573931867369831040381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53174382621244913220693587 79761573931867369831040381)
    ·
      refine ⟨29910590224450263686640143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79761573931867369831040381 29910590224450263686640143)
      ·
        refine ⟨44865885336675395529960215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29910590224450263686640143 44865885336675395529960215)
        ·
          refine ⟨67298828005013093294940323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44865885336675395529960215 67298828005013093294940323)
          ·
            refine ⟨100948242007519639942410485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67298828005013093294940323 100948242007519639942410485)
            ·
              refine ⟨9463897688204966244600983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 100948242007519639942410485 9463897688204966244600983)
              ·
                refine ⟨14195846532307449366901475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9463897688204966244600983 14195846532307449366901475)
                ·
                  refine ⟨21293769798461174050352213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14195846532307449366901475 21293769798461174050352213)
                  ·
                    refine ⟨249536364825716883402565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21293769798461174050352213 249536364825716883402565)
                    ·
                      rfl

theorem cell23_1457911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 8].length) (baseStart_1457911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457911 prefixEnd_1457911 := by exact prefixLift 1457911
  have htrace : WordTrace (prefixWord ++ tailWord_1457911) baseStart_1457911 baseEnd_1457911 := by
    simpa [prefixWord, tailWord_1457911, baseEnd_1457911] using wordTrace_append hprefix tailTrace_1457911
  have hstable : (prefixWord ++ tailWord_1457911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457911).length < 2 ^ (prefixWord ++ tailWord_1457911).sum := by decide
  have hdescent : baseEnd_1457911 < baseStart_1457911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457922 : List Nat := [3, 4, 1, 1, 1, 1, 1, 3, 3, 3, 2]
def baseStart_1457922 : Nat := 118140960795 + 1457922 * 2 ^ 59
def prefixEnd_1457922 : Nat := 4983230072969 + 3 ^ 40 * 1457922 * 2
def baseEnd_1457922 : Nat := 748614742764350107170145

theorem tailTrace_1457922 : CollatzResearch.WordTrace tailWord_1457922 prefixEnd_1457922 748614742764350107170145 := by
  unfold tailWord_1457922
  simp only [CollatzResearch.WordTrace]
  refine ⟨13293695956051265524836005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35449855882803374732896013 13293695956051265524836005)
  ·
    refine ⟨2492567991759612285906751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13293695956051265524836005 2492567991759612285906751)
    ·
      refine ⟨3738851987639418428860127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2492567991759612285906751 3738851987639418428860127)
      ·
        refine ⟨5608277981459127643290191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3738851987639418428860127 5608277981459127643290191)
        ·
          refine ⟨8412416972188691464935287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5608277981459127643290191 8412416972188691464935287)
          ·
            refine ⟨12618625458283037197402931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8412416972188691464935287 12618625458283037197402931)
            ·
              refine ⟨18927938187424555796104397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12618625458283037197402931 18927938187424555796104397)
              ·
                refine ⟨7097976820284208423539149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18927938187424555796104397 7097976820284208423539149)
                ·
                  refine ⟨2661741307606578158827181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7097976820284208423539149 2661741307606578158827181)
                  ·
                    refine ⟨998152990352466809560193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2661741307606578158827181 998152990352466809560193)
                    ·
                      refine ⟨748614742764350107170145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 998152990352466809560193 748614742764350107170145)
                      ·
                        rfl

theorem cell23_1457922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 3, 3, 3, 2].length) (baseStart_1457922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457922 prefixEnd_1457922 := by exact prefixLift 1457922
  have htrace : WordTrace (prefixWord ++ tailWord_1457922) baseStart_1457922 baseEnd_1457922 := by
    simpa [prefixWord, tailWord_1457922, baseEnd_1457922] using wordTrace_append hprefix tailTrace_1457922
  have hstable : (prefixWord ++ tailWord_1457922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457922).length < 2 ^ (prefixWord ++ tailWord_1457922).sum := by decide
  have hdescent : baseEnd_1457922 < baseStart_1457922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457933 : List Nat := [1, 7, 2, 1, 1, 1, 1, 3, 1, 2, 3]
def baseStart_1457933 : Nat := 118140960795 + 1457933 * 2 ^ 59
def prefixEnd_1457933 : Nat := 4983230072969 + 3 ^ 40 * 1457933 * 2
def baseEnd_1457933 : Nat := 748620391051549564132595

theorem tailTrace_1457933 : CollatzResearch.WordTrace tailWord_1457933 prefixEnd_1457933 748620391051549564132595 := by
  unfold tailWord_1457933
  simp only [CollatzResearch.WordTrace]
  refine ⟨53175185027165210977994453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35450123351443473985329635 53175185027165210977994453)
  ·
    refine ⟨1246293399074184632296745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 53175185027165210977994453 1246293399074184632296745)
    ·
      refine ⟨934720049305638474222559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1246293399074184632296745 934720049305638474222559)
      ·
        refine ⟨1402080073958457711333839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 934720049305638474222559 1402080073958457711333839)
        ·
          refine ⟨2103120110937686567000759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1402080073958457711333839 2103120110937686567000759)
          ·
            refine ⟨3154680166406529850501139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2103120110937686567000759 3154680166406529850501139)
            ·
              refine ⟨4732020249609794775751709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3154680166406529850501139 4732020249609794775751709)
              ·
                refine ⟨1774507593603673040906891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4732020249609794775751709 1774507593603673040906891)
                ·
                  refine ⟨2661761390405509561360337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1774507593603673040906891 2661761390405509561360337)
                  ·
                    refine ⟨1996321042804132171020253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2661761390405509561360337 1996321042804132171020253)
                    ·
                      refine ⟨748620391051549564132595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1996321042804132171020253 748620391051549564132595)
                      ·
                        rfl

theorem cell23_1457933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_1457933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457933 prefixEnd_1457933 := by exact prefixLift 1457933
  have htrace : WordTrace (prefixWord ++ tailWord_1457933) baseStart_1457933 baseEnd_1457933 := by
    simpa [prefixWord, tailWord_1457933, baseEnd_1457933] using wordTrace_append hprefix tailTrace_1457933
  have hstable : (prefixWord ++ tailWord_1457933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457933).length < 2 ^ (prefixWord ++ tailWord_1457933).sum := by decide
  have hdescent : baseEnd_1457933 < baseStart_1457933 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457948 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_1457948 : Nat := 118140960795 + 1457948 * 2 ^ 59
def prefixEnd_1457948 : Nat := 4983230072969 + 3 ^ 40 * 1457948 * 2
def baseEnd_1457948 : Nat := 748628093261367005445025

theorem tailTrace_1457948 : CollatzResearch.WordTrace tailWord_1457948 prefixEnd_1457948 748628093261367005445025 := by
  unfold tailWord_1457948
  simp only [CollatzResearch.WordTrace]
  refine ⟨26587866061055434269895249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35450488081407245693193665 26587866061055434269895249)
  ·
    refine ⟨19940899545791575702421437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26587866061055434269895249 19940899545791575702421437)
    ·
      refine ⟨7477837329671840888408039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19940899545791575702421437 7477837329671840888408039)
      ·
        refine ⟨11216755994507761332612059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7477837329671840888408039 11216755994507761332612059)
        ·
          refine ⟨16825133991761641998918089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11216755994507761332612059 16825133991761641998918089)
          ·
            refine ⟨12618850493821231499188567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16825133991761641998918089 12618850493821231499188567)
            ·
              refine ⟨18928275740731847248782851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12618850493821231499188567 18928275740731847248782851)
              ·
                refine ⟨28392413611097770873174277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18928275740731847248782851 28392413611097770873174277)
                ·
                  refine ⟨5323577552080832038720177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28392413611097770873174277 5323577552080832038720177)
                  ·
                    refine ⟨3992683164060624029040133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5323577552080832038720177 3992683164060624029040133)
                    ·
                      refine ⟨748628093261367005445025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3992683164060624029040133 748628093261367005445025)
                      ·
                        rfl

theorem cell23_1457948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_1457948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457948 prefixEnd_1457948 := by exact prefixLift 1457948
  have htrace : WordTrace (prefixWord ++ tailWord_1457948) baseStart_1457948 baseEnd_1457948 := by
    simpa [prefixWord, tailWord_1457948, baseEnd_1457948] using wordTrace_append hprefix tailTrace_1457948
  have hstable : (prefixWord ++ tailWord_1457948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457948).length < 2 ^ (prefixWord ++ tailWord_1457948).sum := by decide
  have hdescent : baseEnd_1457948 < baseStart_1457948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457952 : List Nat := [2, 1, 1, 5, 1, 1, 3, 1, 4, 2, 2]
def baseStart_1457952 : Nat := 118140960795 + 1457952 * 2 ^ 59
def prefixEnd_1457952 : Nat := 4983230072969 + 3 ^ 40 * 1457952 * 2
def baseEnd_1457952 : Nat := 748630147183984989795007

theorem tailTrace_1457952 : CollatzResearch.WordTrace tailWord_1457952 prefixEnd_1457952 748630147183984989795007 := by
  unfold tailWord_1457952
  simp only [CollatzResearch.WordTrace]
  refine ⟨26587939007048188611468055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35450585342730918148624073 26587939007048188611468055)
  ·
    refine ⟨39881908510572282917202083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26587939007048188611468055 39881908510572282917202083)
    ·
      refine ⟨59822862765858424375803125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39881908510572282917202083 59822862765858424375803125)
      ·
        refine ⟨5608393384299227285231543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 59822862765858424375803125 5608393384299227285231543)
        ·
          refine ⟨8412590076448840927847315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5608393384299227285231543 8412590076448840927847315)
          ·
            refine ⟨12618885114673261391770973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8412590076448840927847315 12618885114673261391770973)
            ·
              refine ⟨4732081918002473021914115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12618885114673261391770973 4732081918002473021914115)
              ·
                refine ⟨7098122877003709532871173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4732081918002473021914115 7098122877003709532871173)
                ·
                  refine ⟨1330898039438195537413345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7098122877003709532871173 1330898039438195537413345)
                  ·
                    refine ⟨998173529578646653060009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1330898039438195537413345 998173529578646653060009)
                    ·
                      refine ⟨748630147183984989795007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 998173529578646653060009 748630147183984989795007)
                      ·
                        rfl

theorem cell23_1457952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_1457952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457952 prefixEnd_1457952 := by exact prefixLift 1457952
  have htrace : WordTrace (prefixWord ++ tailWord_1457952) baseStart_1457952 baseEnd_1457952 := by
    simpa [prefixWord, tailWord_1457952, baseEnd_1457952] using wordTrace_append hprefix tailTrace_1457952
  have hstable : (prefixWord ++ tailWord_1457952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457952).length < 2 ^ (prefixWord ++ tailWord_1457952).sum := by decide
  have hdescent : baseEnd_1457952 < baseStart_1457952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457961 : List Nat := [1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 8]
def baseStart_1457961 : Nat := 118140960795 + 1457961 * 2 ^ 59
def prefixEnd_1457961 : Nat := 4983230072969 + 3 ^ 40 * 1457961 * 2
def baseEnd_1457961 : Nat := 748634768509875454582465

theorem tailTrace_1457961 : CollatzResearch.WordTrace tailWord_1457961 prefixEnd_1457961 748634768509875454582465 := by
  unfold tailWord_1457961
  simp only [CollatzResearch.WordTrace]
  refine ⟨53176206271063771760013737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35450804180709181173342491 53176206271063771760013737)
  ·
    refine ⟨39882154703297828820010303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53176206271063771760013737 39882154703297828820010303)
    ·
      refine ⟨59823232054946743230015455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39882154703297828820010303 59823232054946743230015455)
      ·
        refine ⟨89734848082420114845023183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59823232054946743230015455 89734848082420114845023183)
        ·
          refine ⟨134602272123630172267534775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89734848082420114845023183 134602272123630172267534775)
          ·
            refine ⟨201903408185445258401302163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134602272123630172267534775 201903408185445258401302163)
            ·
              refine ⟨302855112278167887601953245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201903408185445258401302163 302855112278167887601953245)
              ·
                refine ⟨113570667104312957850732467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 302855112278167887601953245 113570667104312957850732467)
                ·
                  refine ⟨170356000656469436776098701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 113570667104312957850732467 170356000656469436776098701)
                  ·
                    refine ⟨63883500246176038791037013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 170356000656469436776098701 63883500246176038791037013)
                    ·
                      refine ⟨748634768509875454582465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 63883500246176038791037013 748634768509875454582465)
                      ·
                        rfl

theorem cell23_1457961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_1457961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457961 prefixEnd_1457961 := by exact prefixLift 1457961
  have htrace : WordTrace (prefixWord ++ tailWord_1457961) baseStart_1457961 baseEnd_1457961 := by
    simpa [prefixWord, tailWord_1457961, baseEnd_1457961] using wordTrace_append hprefix tailTrace_1457961
  have hstable : (prefixWord ++ tailWord_1457961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457961).length < 2 ^ (prefixWord ++ tailWord_1457961).sum := by decide
  have hdescent : baseEnd_1457961 < baseStart_1457961 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1457992 : List Nat := [2, 1, 3, 1, 1, 6, 1, 3, 5]
def baseStart_1457992 : Nat := 118140960795 + 1457992 * 2 ^ 59
def prefixEnd_1457992 : Nat := 4983230072969 + 3 ^ 40 * 1457992 * 2
def baseEnd_1457992 : Nat := 83183409601129425921647

theorem tailTrace_1457992 : CollatzResearch.WordTrace tailWord_1457992 prefixEnd_1457992 83183409601129425921647 := by
  unfold tailWord_1457992
  simp only [CollatzResearch.WordTrace]
  refine ⟨26588668466975732027196115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35451557955967642702928153 26588668466975732027196115)
  ·
    refine ⟨39883002700463598040794173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26588668466975732027196115 39883002700463598040794173)
    ·
      refine ⟨14956126012673849265297815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39883002700463598040794173 14956126012673849265297815)
      ·
        refine ⟨22434189019010773897946723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14956126012673849265297815 22434189019010773897946723)
        ·
          refine ⟨33651283528516160846920085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22434189019010773897946723 33651283528516160846920085)
          ·
            refine ⟨1577403915399195039699379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33651283528516160846920085 1577403915399195039699379)
            ·
              refine ⟨2366105873098792559549069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1577403915399195039699379 2366105873098792559549069)
              ·
                refine ⟨887289702412047209830901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2366105873098792559549069 887289702412047209830901)
                ·
                  refine ⟨83183409601129425921647, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 887289702412047209830901 83183409601129425921647)
                  ·
                    rfl

theorem cell23_1457992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 6, 1, 3, 5].length) (baseStart_1457992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1457992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1457992 prefixEnd_1457992 := by exact prefixLift 1457992
  have htrace : WordTrace (prefixWord ++ tailWord_1457992) baseStart_1457992 baseEnd_1457992 := by
    simpa [prefixWord, tailWord_1457992, baseEnd_1457992] using wordTrace_append hprefix tailTrace_1457992
  have hstable : (prefixWord ++ tailWord_1457992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1457992).length < 2 ^ (prefixWord ++ tailWord_1457992).sum := by decide
  have hdescent : baseEnd_1457992 < baseStart_1457992 := by decide
  rcases family_descends (prefixWord ++ tailWord_1457992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458005 : List Nat := [1, 3, 2, 2, 2, 3, 1, 2, 2, 5]
def baseStart_1458005 : Nat := 118140960795 + 1458005 * 2 ^ 59
def prefixEnd_1458005 : Nat := 4983230072969 + 3 ^ 40 * 1458005 * 2
def baseEnd_1458005 : Nat := 249552453886224427477421

theorem tailTrace_1458005 : CollatzResearch.WordTrace tailWord_1458005 prefixEnd_1458005 249552453886224427477421 := by
  unfold tailWord_1458005
  simp only [CollatzResearch.WordTrace]
  refine ⟨53177811082904367274615469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35451874055269578183076979 53177811082904367274615469)
  ·
    refine ⟨19941679156089137727980801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53177811082904367274615469 19941679156089137727980801)
    ·
      refine ⟨14956259367066853295985601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19941679156089137727980801 14956259367066853295985601)
      ·
        refine ⟨11217194525300139971989201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14956259367066853295985601 11217194525300139971989201)
        ·
          refine ⟨8412895893975104978991901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11217194525300139971989201 8412895893975104978991901)
          ·
            refine ⟨3154835960240664367121963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8412895893975104978991901 3154835960240664367121963)
            ·
              refine ⟨4732253940360996550682945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3154835960240664367121963 4732253940360996550682945)
              ·
                refine ⟨3549190455270747413012209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4732253940360996550682945 3549190455270747413012209)
                ·
                  refine ⟨2661892841453060559759157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3549190455270747413012209 2661892841453060559759157)
                  ·
                    refine ⟨249552453886224427477421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2661892841453060559759157 249552453886224427477421)
                    ·
                      rfl

theorem cell23_1458005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 1, 2, 2, 5].length) (baseStart_1458005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458005 prefixEnd_1458005 := by exact prefixLift 1458005
  have htrace : WordTrace (prefixWord ++ tailWord_1458005) baseStart_1458005 baseEnd_1458005 := by
    simpa [prefixWord, tailWord_1458005, baseEnd_1458005] using wordTrace_append hprefix tailTrace_1458005
  have hstable : (prefixWord ++ tailWord_1458005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458005).length < 2 ^ (prefixWord ++ tailWord_1458005).sum := by decide
  have hdescent : baseEnd_1458005 < baseStart_1458005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458025 : List Nat := [1, 2, 1, 1, 1, 3, 1, 5, 2, 4, 2]
def baseStart_1458025 : Nat := 118140960795 + 1458025 * 2 ^ 59
def prefixEnd_1458025 : Nat := 4983230072969 + 3 ^ 40 * 1458025 * 2
def baseEnd_1458025 : Nat := 748667631271763204182171

theorem tailTrace_1458025 : CollatzResearch.WordTrace tailWord_1458025 prefixEnd_1458025 748667631271763204182171 := by
  unfold tailWord_1458025
  simp only [CollatzResearch.WordTrace]
  refine ⟨53178540542831910690343529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35452360361887940460229019 53178540542831910690343529)
  ·
    refine ⟨39883905407123933017757647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53178540542831910690343529 39883905407123933017757647)
    ·
      refine ⟨59825858110685899526636471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39883905407123933017757647 59825858110685899526636471)
      ·
        refine ⟨89738787166028849289954707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59825858110685899526636471 89738787166028849289954707)
        ·
          refine ⟨134608180749043273934932061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89738787166028849289954707 134608180749043273934932061)
          ·
            refine ⟨50478067780891227725599523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 134608180749043273934932061 50478067780891227725599523)
            ·
              refine ⟨75717101671336841588399285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50478067780891227725599523 75717101671336841588399285)
              ·
                refine ⟨7098478281687828898912433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 75717101671336841588399285 7098478281687828898912433)
                ·
                  refine ⟨5323858711265871674184325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7098478281687828898912433 5323858711265871674184325)
                  ·
                    refine ⟨998223508362350938909561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5323858711265871674184325 998223508362350938909561)
                    ·
                      refine ⟨748667631271763204182171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 998223508362350938909561 748667631271763204182171)
                      ·
                        rfl

theorem cell23_1458025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 5, 2, 4, 2].length) (baseStart_1458025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458025 prefixEnd_1458025 := by exact prefixLift 1458025
  have htrace : WordTrace (prefixWord ++ tailWord_1458025) baseStart_1458025 baseEnd_1458025 := by
    simpa [prefixWord, tailWord_1458025, baseEnd_1458025] using wordTrace_append hprefix tailTrace_1458025
  have hstable : (prefixWord ++ tailWord_1458025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458025).length < 2 ^ (prefixWord ++ tailWord_1458025).sum := by decide
  have hdescent : baseEnd_1458025 < baseStart_1458025 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458095 : List Nat := [1, 1, 2, 1, 2, 2, 4, 4, 1, 5]
def baseStart_1458095 : Nat := 118140960795 + 1458095 * 2 ^ 59
def prefixEnd_1458095 : Nat := 4983230072969 + 3 ^ 40 * 1458095 * 2
def baseEnd_1458095 : Nat := 249567858305859310102283

theorem tailTrace_1458095 : CollatzResearch.WordTrace tailWord_1458095 prefixEnd_1458095 249567858305859310102283 := by
  unfold tailWord_1458095
  simp only [CollatzResearch.WordTrace]
  refine ⟨53181093652578312645391739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35454062435052208430261159 53181093652578312645391739)
  ·
    refine ⟨79771640478867468968087609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53181093652578312645391739 79771640478867468968087609)
    ·
      refine ⟨59828730359150601726065707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79771640478867468968087609 59828730359150601726065707)
      ·
        refine ⟨89743095538725902589098561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59828730359150601726065707 89743095538725902589098561)
        ·
          refine ⟨67307321654044426941823921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89743095538725902589098561 67307321654044426941823921)
          ·
            refine ⟨50480491240533320206367941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67307321654044426941823921 50480491240533320206367941)
            ·
              refine ⟨9465092107599997538693989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50480491240533320206367941 9465092107599997538693989)
              ·
                refine ⟨1774704770174999538505123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9465092107599997538693989 1774704770174999538505123)
                ·
                  refine ⟨2662057155262499307757685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1774704770174999538505123 2662057155262499307757685)
                  ·
                    refine ⟨249567858305859310102283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2662057155262499307757685 249567858305859310102283)
                    ·
                      rfl

theorem cell23_1458095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 4, 4, 1, 5].length) (baseStart_1458095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458095 prefixEnd_1458095 := by exact prefixLift 1458095
  have htrace : WordTrace (prefixWord ++ tailWord_1458095) baseStart_1458095 baseEnd_1458095 := by
    simpa [prefixWord, tailWord_1458095, baseEnd_1458095] using wordTrace_append hprefix tailTrace_1458095
  have hstable : (prefixWord ++ tailWord_1458095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458095).length < 2 ^ (prefixWord ++ tailWord_1458095).sum := by decide
  have hdescent : baseEnd_1458095 < baseStart_1458095 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458135 : List Nat := [1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 5]
def baseStart_1458135 : Nat := 118140960795 + 1458135 * 2 ^ 59
def prefixEnd_1458135 : Nat := 4983230072969 + 3 ^ 40 * 1458135 * 2
def baseEnd_1458135 : Nat := 748724114143757773806665

theorem tailTrace_1458135 : CollatzResearch.WordTrace tailWord_1458135 prefixEnd_1458135 748724114143757773806665 := by
  unfold tailWord_1458135
  simp only [CollatzResearch.WordTrace]
  refine ⟨53182552572433399476847859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35455035048288932984565239 53182552572433399476847859)
  ·
    refine ⟨79773828858650099215271789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53182552572433399476847859 79773828858650099215271789)
    ·
      refine ⟨29915185821993787205726921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79773828858650099215271789 29915185821993787205726921)
      ·
        refine ⟨22436389366495340404295191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29915185821993787205726921 22436389366495340404295191)
        ·
          refine ⟨33654584049743010606442787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22436389366495340404295191 33654584049743010606442787)
          ·
            refine ⟨50481876074614515909664181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33654584049743010606442787 50481876074614515909664181)
            ·
              refine ⟨4732675881995110866531017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50481876074614515909664181 4732675881995110866531017)
              ·
                refine ⟨3549506911496333149898263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4732675881995110866531017 3549506911496333149898263)
                ·
                  refine ⟨5324260367244499724847395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3549506911496333149898263 5324260367244499724847395)
                  ·
                    refine ⟨7986390550866749587271093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5324260367244499724847395 7986390550866749587271093)
                    ·
                      refine ⟨748724114143757773806665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7986390550866749587271093 748724114143757773806665)
                      ·
                        rfl

theorem cell23_1458135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 1, 1, 5].length) (baseStart_1458135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458135 prefixEnd_1458135 := by exact prefixLift 1458135
  have htrace : WordTrace (prefixWord ++ tailWord_1458135) baseStart_1458135 baseEnd_1458135 := by
    simpa [prefixWord, tailWord_1458135, baseEnd_1458135] using wordTrace_append hprefix tailTrace_1458135
  have hstable : (prefixWord ++ tailWord_1458135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458135).length < 2 ^ (prefixWord ++ tailWord_1458135).sum := by decide
  have hdescent : baseEnd_1458135 < baseStart_1458135 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458146 : List Nat := [3, 3, 3, 1, 2, 1, 2, 2, 1, 5]
def baseStart_1458146 : Nat := 118140960795 + 1458146 * 2 ^ 59
def prefixEnd_1458146 : Nat := 4983230072969 + 3 ^ 40 * 1458146 * 2
def baseEnd_1458146 : Nat := 249576587476985743589705

theorem tailTrace_1458146 : CollatzResearch.WordTrace tailWord_1458146 prefixEnd_1458146 249576587476985743589705 := by
  unfold tailWord_1458146
  simp only [CollatzResearch.WordTrace]
  refine ⟨13295738443848387088874573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35455302516929032236998861 13295738443848387088874573)
  ·
    refine ⟨4985901916443145158327965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13295738443848387088874573 4985901916443145158327965)
    ·
      refine ⟨1869713218666179434372987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4985901916443145158327965 1869713218666179434372987)
      ·
        refine ⟨2804569827999269151559481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1869713218666179434372987 2804569827999269151559481)
        ·
          refine ⟨2103427370999451863669611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2804569827999269151559481 2103427370999451863669611)
          ·
            refine ⟨3155141056499177795504417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2103427370999451863669611 3155141056499177795504417)
            ·
              refine ⟨2366355792374383346628313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3155141056499177795504417 2366355792374383346628313)
              ·
                refine ⟨1774766844280787509971235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2366355792374383346628313 1774766844280787509971235)
                ·
                  refine ⟨2662150266421181264956853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1774766844280787509971235 2662150266421181264956853)
                  ·
                    refine ⟨249576587476985743589705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2662150266421181264956853 249576587476985743589705)
                    ·
                      rfl

theorem cell23_1458146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 2, 2, 1, 5].length) (baseStart_1458146 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458146 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458146 prefixEnd_1458146 := by exact prefixLift 1458146
  have htrace : WordTrace (prefixWord ++ tailWord_1458146) baseStart_1458146 baseEnd_1458146 := by
    simpa [prefixWord, tailWord_1458146, baseEnd_1458146] using wordTrace_append hprefix tailTrace_1458146
  have hstable : (prefixWord ++ tailWord_1458146).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458146).length < 2 ^ (prefixWord ++ tailWord_1458146).sum := by decide
  have hdescent : baseEnd_1458146 < baseStart_1458146 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458192 : List Nat := [2, 1, 1, 1, 1, 1, 1, 5, 5, 3, 2]
def baseStart_1458192 : Nat := 118140960795 + 1458192 * 2 ^ 59
def prefixEnd_1458192 : Nat := 4983230072969 + 3 ^ 40 * 1458192 * 2
def baseEnd_1458192 : Nat := 748753382541064050793903

theorem tailTrace_1458192 : CollatzResearch.WordTrace tailWord_1458192 prefixEnd_1458192 748753382541064050793903 := by
  unfold tailWord_1458192
  simp only [CollatzResearch.WordTrace]
  refine ⟨26592315766613449105836415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35456421022151265474448553 26592315766613449105836415)
  ·
    refine ⟨39888473649920173658754623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26592315766613449105836415 39888473649920173658754623)
    ·
      refine ⟨59832710474880260488131935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39888473649920173658754623 59832710474880260488131935)
      ·
        refine ⟨89749065712320390732197903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59832710474880260488131935 89749065712320390732197903)
        ·
          refine ⟨134623598568480586098296855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89749065712320390732197903 134623598568480586098296855)
          ·
            refine ⟨201935397852720879147445283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134623598568480586098296855 201935397852720879147445283)
            ·
              refine ⟨302903096779081318721167925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201935397852720879147445283 302903096779081318721167925)
              ·
                refine ⟨28397165323038873630109493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 302903096779081318721167925 28397165323038873630109493)
                ·
                  refine ⟨2662234249034894402822765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28397165323038873630109493 2662234249034894402822765)
                  ·
                    refine ⟨998337843388085401058537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2662234249034894402822765 998337843388085401058537)
                    ·
                      refine ⟨748753382541064050793903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 998337843388085401058537 748753382541064050793903)
                      ·
                        rfl

theorem cell23_1458192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 5, 5, 3, 2].length) (baseStart_1458192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458192 prefixEnd_1458192 := by exact prefixLift 1458192
  have htrace : WordTrace (prefixWord ++ tailWord_1458192) baseStart_1458192 baseEnd_1458192 := by
    simpa [prefixWord, tailWord_1458192, baseEnd_1458192] using wordTrace_append hprefix tailTrace_1458192
  have hstable : (prefixWord ++ tailWord_1458192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458192).length < 2 ^ (prefixWord ++ tailWord_1458192).sum := by decide
  have hdescent : baseEnd_1458192 < baseStart_1458192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458216 : List Nat := [2, 1, 5, 3, 1, 1, 1, 2, 1, 3, 3]
def baseStart_1458216 : Nat := 118140960795 + 1458216 * 2 ^ 59
def prefixEnd_1458216 : Nat := 4983230072969 + 3 ^ 40 * 1458216 * 2
def baseEnd_1458216 : Nat := 748765706076771956893793

theorem tailTrace_1458216 : CollatzResearch.WordTrace tailWord_1458216 prefixEnd_1458216 748765706076771956893793 := by
  unfold tailWord_1458216
  simp only [CollatzResearch.WordTrace]
  refine ⟨26592753442569975155273251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35457004590093300207031001 26592753442569975155273251)
  ·
    refine ⟨39889130163854962732909877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26592753442569975155273251 39889130163854962732909877)
    ·
      refine ⟨3739605952861402756210301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 39889130163854962732909877 3739605952861402756210301)
      ·
        refine ⟨1402352232323026033578863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3739605952861402756210301 1402352232323026033578863)
        ·
          refine ⟨2103528348484539050368295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1402352232323026033578863 2103528348484539050368295)
          ·
            refine ⟨3155292522726808575552443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2103528348484539050368295 3155292522726808575552443)
            ·
              refine ⟨4732938784090212863328665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3155292522726808575552443 4732938784090212863328665)
              ·
                refine ⟨3549704088067659647496499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4732938784090212863328665 3549704088067659647496499)
                ·
                  refine ⟨5324556132101489471244749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3549704088067659647496499 5324556132101489471244749)
                  ·
                    refine ⟨1996708549538058551716781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5324556132101489471244749 1996708549538058551716781)
                    ·
                      refine ⟨748765706076771956893793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1996708549538058551716781 748765706076771956893793)
                      ·
                        rfl

theorem cell23_1458216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_1458216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458216 prefixEnd_1458216 := by exact prefixLift 1458216
  have htrace : WordTrace (prefixWord ++ tailWord_1458216) baseStart_1458216 baseEnd_1458216 := by
    simpa [prefixWord, tailWord_1458216, baseEnd_1458216] using wordTrace_append hprefix tailTrace_1458216
  have hstable : (prefixWord ++ tailWord_1458216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458216).length < 2 ^ (prefixWord ++ tailWord_1458216).sum := by decide
  have hdescent : baseEnd_1458216 < baseStart_1458216 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458235 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 4]
def baseStart_1458235 : Nat := 118140960795 + 1458235 * 2 ^ 59
def prefixEnd_1458235 : Nat := 4983230072969 + 3 ^ 40 * 1458235 * 2
def baseEnd_1458235 : Nat := 748775462209207382556205

theorem tailTrace_1458235 : CollatzResearch.WordTrace tailWord_1458235 prefixEnd_1458235 748775462209207382556205 := by
  unfold tailWord_1458235
  simp only [CollatzResearch.WordTrace]
  refine ⟨53186199872071116555488159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35457466581380744370325439 53186199872071116555488159)
  ·
    refine ⟨79779299808106674833232239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53186199872071116555488159 79779299808106674833232239)
    ·
      refine ⟨119668949712160012249848359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79779299808106674833232239 119668949712160012249848359)
      ·
        refine ⟨179503424568240018374772539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119668949712160012249848359 179503424568240018374772539)
        ·
          refine ⟨269255136852360027562158809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 179503424568240018374772539 269255136852360027562158809)
          ·
            refine ⟨201941352639270020671619107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 269255136852360027562158809 201941352639270020671619107)
            ·
              refine ⟨302912028958905031007428661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 201941352639270020671619107 302912028958905031007428661)
              ·
                refine ⟨28398002714897346656946437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 302912028958905031007428661 28398002714897346656946437)
                ·
                  refine ⟨5324625509043252498177457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28398002714897346656946437 5324625509043252498177457)
                  ·
                    refine ⟨3993469131782439373633093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5324625509043252498177457 3993469131782439373633093)
                    ·
                      refine ⟨748775462209207382556205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3993469131782439373633093 748775462209207382556205)
                      ·
                        rfl

theorem cell23_1458235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 4, 2, 4].length) (baseStart_1458235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458235 prefixEnd_1458235 := by exact prefixLift 1458235
  have htrace : WordTrace (prefixWord ++ tailWord_1458235) baseStart_1458235 baseEnd_1458235 := by
    simpa [prefixWord, tailWord_1458235, baseEnd_1458235] using wordTrace_append hprefix tailTrace_1458235
  have hstable : (prefixWord ++ tailWord_1458235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458235).length < 2 ^ (prefixWord ++ tailWord_1458235).sum := by decide
  have hdescent : baseEnd_1458235 < baseStart_1458235 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458239 : List Nat := [1, 1, 2, 2, 3, 1, 2, 3, 4, 2, 2]
def baseStart_1458239 : Nat := 118140960795 + 1458239 * 2 ^ 59
def prefixEnd_1458239 : Nat := 4983230072969 + 3 ^ 40 * 1458239 * 2
def baseEnd_1458239 : Nat := 748777516131825366906187

theorem tailTrace_1458239 : CollatzResearch.WordTrace tailWord_1458239 prefixEnd_1458239 748777516131825366906187 := by
  unfold tailWord_1458239
  simp only [CollatzResearch.WordTrace]
  refine ⟨53186345764056625238633771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35457563842704416825755847 53186345764056625238633771)
  ·
    refine ⟨79779518646084937857950657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53186345764056625238633771 79779518646084937857950657)
    ·
      refine ⟨59834638984563703393462993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79779518646084937857950657 59834638984563703393462993)
      ·
        refine ⟨44875979238422777545097245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59834638984563703393462993 44875979238422777545097245)
        ·
          refine ⟨16828492214408541579411467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44875979238422777545097245 16828492214408541579411467)
          ·
            refine ⟨25242738321612812369117201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16828492214408541579411467 25242738321612812369117201)
            ·
              refine ⟨18932053741209609276837901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25242738321612812369117201 18932053741209609276837901)
              ·
                refine ⟨7099520152953603478814213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18932053741209609276837901 7099520152953603478814213)
                ·
                  refine ⟨1331160028678800652277665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7099520152953603478814213 1331160028678800652277665)
                  ·
                    refine ⟨998370021509100489208249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1331160028678800652277665 998370021509100489208249)
                    ·
                      refine ⟨748777516131825366906187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 998370021509100489208249 748777516131825366906187)
                      ·
                        rfl

theorem cell23_1458239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 2, 3, 4, 2, 2].length) (baseStart_1458239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458239 prefixEnd_1458239 := by exact prefixLift 1458239
  have htrace : WordTrace (prefixWord ++ tailWord_1458239) baseStart_1458239 baseEnd_1458239 := by
    simpa [prefixWord, tailWord_1458239, baseEnd_1458239] using wordTrace_append hprefix tailTrace_1458239
  have hstable : (prefixWord ++ tailWord_1458239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458239).length < 2 ^ (prefixWord ++ tailWord_1458239).sum := by decide
  have hdescent : baseEnd_1458239 < baseStart_1458239 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458245 : List Nat := [1, 3, 1, 1, 1, 3, 1, 5, 7]
def baseStart_1458245 : Nat := 118140960795 + 1458245 * 2 ^ 59
def prefixEnd_1458245 : Nat := 4983230072969 + 3 ^ 40 * 1458245 * 2
def baseEnd_1458245 : Nat := 83197844112861371492351

theorem tailTrace_1458245 : CollatzResearch.WordTrace tailWord_1458245 prefixEnd_1458245 83197844112861371492351 := by
  unfold tailWord_1458245
  simp only [CollatzResearch.WordTrace]
  refine ⟨53186564602034888263352189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35457709734689925508901459 53186564602034888263352189)
  ·
    refine ⟨19944961725763083098757071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53186564602034888263352189 19944961725763083098757071)
    ·
      refine ⟨29917442588644624648135607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19944961725763083098757071 29917442588644624648135607)
      ·
        refine ⟨44876163882966936972203411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29917442588644624648135607 44876163882966936972203411)
        ·
          refine ⟨67314245824450405458305117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44876163882966936972203411 67314245824450405458305117)
          ·
            refine ⟨25242842184168902046864419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67314245824450405458305117 25242842184168902046864419)
            ·
              refine ⟨37864263276253353070296629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25242842184168902046864419 37864263276253353070296629)
              ·
                refine ⟨3549774682148751850340309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 37864263276253353070296629 3549774682148751850340309)
                ·
                  refine ⟨83197844112861371492351, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3549774682148751850340309 83197844112861371492351)
                  ·
                    rfl

theorem cell23_1458245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 7].length) (baseStart_1458245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458245 prefixEnd_1458245 := by exact prefixLift 1458245
  have htrace : WordTrace (prefixWord ++ tailWord_1458245) baseStart_1458245 baseEnd_1458245 := by
    simpa [prefixWord, tailWord_1458245, baseEnd_1458245] using wordTrace_append hprefix tailTrace_1458245
  have hstable : (prefixWord ++ tailWord_1458245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458245).length < 2 ^ (prefixWord ++ tailWord_1458245).sum := by decide
  have hdescent : baseEnd_1458245 < baseStart_1458245 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458279 : List Nat := [1, 1, 5, 1, 1, 2, 4, 3, 5]
def baseStart_1458279 : Nat := 118140960795 + 1458279 * 2 ^ 59
def prefixEnd_1458279 : Nat := 4983230072969 + 3 ^ 40 * 1458279 * 2
def baseEnd_1458279 : Nat := 83199783928667245600667

theorem tailTrace_1458279 : CollatzResearch.WordTrace tailWord_1458279 prefixEnd_1458279 83199783928667245600667 := by
  unfold tailWord_1458279
  simp only [CollatzResearch.WordTrace]
  refine ⟨53187804683911712070089891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35458536455941141380059927 53187804683911712070089891)
  ·
    refine ⟨79781707025867568105134837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53187804683911712070089891 79781707025867568105134837)
    ·
      refine ⟨7479535033675084509856391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79781707025867568105134837 7479535033675084509856391)
      ·
        refine ⟨11219302550512626764784587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7479535033675084509856391 11219302550512626764784587)
        ·
          refine ⟨16828953825768940147176881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11219302550512626764784587 16828953825768940147176881)
          ·
            refine ⟨12621715369326705110382661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16828953825768940147176881 12621715369326705110382661)
            ·
              refine ⟨2366571631748757208196749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12621715369326705110382661 2366571631748757208196749)
              ·
                refine ⟨887464361905783953073781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2366571631748757208196749 887464361905783953073781)
                ·
                  refine ⟨83199783928667245600667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 887464361905783953073781 83199783928667245600667)
                  ·
                    rfl

theorem cell23_1458279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 4, 3, 5].length) (baseStart_1458279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458279 prefixEnd_1458279 := by exact prefixLift 1458279
  have htrace : WordTrace (prefixWord ++ tailWord_1458279) baseStart_1458279 baseEnd_1458279 := by
    simpa [prefixWord, tailWord_1458279, baseEnd_1458279] using wordTrace_append hprefix tailTrace_1458279
  have hstable : (prefixWord ++ tailWord_1458279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458279).length < 2 ^ (prefixWord ++ tailWord_1458279).sum := by decide
  have hdescent : baseEnd_1458279 < baseStart_1458279 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458322 : List Nat := [3, 2, 3, 1, 1, 1, 1, 1, 2, 8]
def baseStart_1458322 : Nat := 118140960795 + 1458322 * 2 ^ 59
def prefixEnd_1458322 : Nat := 4983230072969 + 3 ^ 40 * 1458322 * 2
def baseEnd_1458322 : Nat := 249606711675382847389435

theorem tailTrace_1458322 : CollatzResearch.WordTrace tailWord_1458322 prefixEnd_1458322 249606711675382847389435 := by
  unfold tailWord_1458322
  simp only [CollatzResearch.WordTrace]
  refine ⟨13297343255688982603476305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35459582015170620275936813 13297343255688982603476305)
  ·
    refine ⟨9973007441766736952607229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13297343255688982603476305 9973007441766736952607229)
    ·
      refine ⟨3739877790662526357227711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9973007441766736952607229 3739877790662526357227711)
      ·
        refine ⟨5609816685993789535841567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3739877790662526357227711 5609816685993789535841567)
        ·
          refine ⟨8414725028990684303762351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5609816685993789535841567 8414725028990684303762351)
          ·
            refine ⟨12622087543486026455643527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8414725028990684303762351 12622087543486026455643527)
            ·
              refine ⟨18933131315229039683465291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12622087543486026455643527 18933131315229039683465291)
              ·
                refine ⟨28399696972843559525197937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18933131315229039683465291 28399696972843559525197937)
                ·
                  refine ⟨21299772729632669643898453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28399696972843559525197937 21299772729632669643898453)
                  ·
                    refine ⟨249606711675382847389435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21299772729632669643898453 249606711675382847389435)
                    ·
                      rfl

theorem cell23_1458322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 1, 2, 8].length) (baseStart_1458322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458322 prefixEnd_1458322 := by exact prefixLift 1458322
  have htrace : WordTrace (prefixWord ++ tailWord_1458322) baseStart_1458322 baseEnd_1458322 := by
    simpa [prefixWord, tailWord_1458322, baseEnd_1458322] using wordTrace_append hprefix tailTrace_1458322
  have hstable : (prefixWord ++ tailWord_1458322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458322).length < 2 ^ (prefixWord ++ tailWord_1458322).sum := by decide
  have hdescent : baseEnd_1458322 < baseStart_1458322 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458379 : List Nat := [1, 1, 1, 1, 3, 2, 4, 1, 5, 1, 3]
def baseStart_1458379 : Nat := 118140960795 + 1458379 * 2 ^ 59
def prefixEnd_1458379 : Nat := 4983230072969 + 3 ^ 40 * 1458379 * 2
def baseEnd_1458379 : Nat := 748849403423454819155543

theorem tailTrace_1458379 : CollatzResearch.WordTrace tailWord_1458379 prefixEnd_1458379 748849403423454819155543 := by
  unfold tailWord_1458379
  simp only [CollatzResearch.WordTrace]
  refine ⟨53191451983549429148730191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35460967989032952765820127 53191451983549429148730191)
  ·
    refine ⟨79787177975324143723095287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53191451983549429148730191 79787177975324143723095287)
    ·
      refine ⟨119680766962986215584642931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79787177975324143723095287 119680766962986215584642931)
      ·
        refine ⟨179521150444479323376964397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119680766962986215584642931 179521150444479323376964397)
        ·
          refine ⟨67320431416679746266361649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 179521150444479323376964397 67320431416679746266361649)
          ·
            refine ⟨50490323562509809699771237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67320431416679746266361649 50490323562509809699771237)
            ·
              refine ⟨9466935667970589318707107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50490323562509809699771237 9466935667970589318707107)
              ·
                refine ⟨14200403501955883978060661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9466935667970589318707107 14200403501955883978060661)
                ·
                  refine ⟨1331287828308364122943187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14200403501955883978060661 1331287828308364122943187)
                  ·
                    refine ⟨1996931742462546184414781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1331287828308364122943187 1996931742462546184414781)
                    ·
                      refine ⟨748849403423454819155543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1996931742462546184414781 748849403423454819155543)
                      ·
                        rfl

theorem cell23_1458379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 1, 5, 1, 3].length) (baseStart_1458379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458379 prefixEnd_1458379 := by exact prefixLift 1458379
  have htrace : WordTrace (prefixWord ++ tailWord_1458379) baseStart_1458379 baseEnd_1458379 := by
    simpa [prefixWord, tailWord_1458379, baseEnd_1458379] using wordTrace_append hprefix tailTrace_1458379
  have hstable : (prefixWord ++ tailWord_1458379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458379).length < 2 ^ (prefixWord ++ tailWord_1458379).sum := by decide
  have hdescent : baseEnd_1458379 < baseStart_1458379 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458412 : List Nat := [2, 2, 1, 1, 2, 3, 1, 2, 3, 6]
def baseStart_1458412 : Nat := 118140960795 + 1458412 * 2 ^ 59
def prefixEnd_1458412 : Nat := 4983230072969 + 3 ^ 40 * 1458412 * 2
def baseEnd_1458412 : Nat := 249622116095017730014297

theorem tailTrace_1458412 : CollatzResearch.WordTrace tailWord_1458412 prefixEnd_1458412 249622116095017730014297 := by
  unfold tailWord_1458412
  simp only [CollatzResearch.WordTrace]
  refine ⟨26596327796214937892340745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35461770394953250523120993 26596327796214937892340745)
  ·
    refine ⟨19947245847161203419255559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26596327796214937892340745 19947245847161203419255559)
    ·
      refine ⟨29920868770741805128883339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19947245847161203419255559 29920868770741805128883339)
      ·
        refine ⟨44881303156112707693325009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29920868770741805128883339 44881303156112707693325009)
        ·
          refine ⟨33660977367084530769993757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44881303156112707693325009 33660977367084530769993757)
          ·
            refine ⟨12622866512656699038747659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33660977367084530769993757 12622866512656699038747659)
            ·
              refine ⟨18934299768985048558121489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12622866512656699038747659 18934299768985048558121489)
              ·
                refine ⟨14200724826738786418591117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18934299768985048558121489 14200724826738786418591117)
                ·
                  refine ⟨5325271810027044906971669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14200724826738786418591117 5325271810027044906971669)
                  ·
                    refine ⟨249622116095017730014297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5325271810027044906971669 249622116095017730014297)
                    ·
                      rfl

theorem cell23_1458412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 6].length) (baseStart_1458412 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458412 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458412 prefixEnd_1458412 := by exact prefixLift 1458412
  have htrace : WordTrace (prefixWord ++ tailWord_1458412) baseStart_1458412 baseEnd_1458412 := by
    simpa [prefixWord, tailWord_1458412, baseEnd_1458412] using wordTrace_append hprefix tailTrace_1458412
  have hstable : (prefixWord ++ tailWord_1458412).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458412).length < 2 ^ (prefixWord ++ tailWord_1458412).sum := by decide
  have hdescent : baseEnd_1458412 < baseStart_1458412 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458432 : List Nat := [2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 6]
def baseStart_1458432 : Nat := 118140960795 + 1458432 * 2 ^ 59
def prefixEnd_1458432 : Nat := 4983230072969 + 3 ^ 40 * 1458432 * 2
def baseEnd_1458432 : Nat := 748876617898143111792799

theorem tailTrace_1458432 : CollatzResearch.WordTrace tailWord_1458432 prefixEnd_1458432 748876617898143111792799 := by
  unfold tailWord_1458432
  simp only [CollatzResearch.WordTrace]
  refine ⟨26596692526178709600204775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35462256701571612800273033 26596692526178709600204775)
  ·
    refine ⟨39895038789268064400307163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26596692526178709600204775 39895038789268064400307163)
    ·
      refine ⟨59842558183902096600460745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39895038789268064400307163 59842558183902096600460745)
      ·
        refine ⟨44881918637926572450345559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59842558183902096600460745 44881918637926572450345559)
        ·
          refine ⟨67322877956889858675518339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44881918637926572450345559 67322877956889858675518339)
          ·
            refine ⟨100984316935334788013277509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67322877956889858675518339 100984316935334788013277509)
            ·
              refine ⟨18934559425375272752489533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 100984316935334788013277509 18934559425375272752489533)
              ·
                refine ⟨7100459784515727282183575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18934559425375272752489533 7100459784515727282183575)
                ·
                  refine ⟨10650689676773590923275363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7100459784515727282183575 10650689676773590923275363)
                  ·
                    refine ⟨15976034515160386384913045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10650689676773590923275363 15976034515160386384913045)
                    ·
                      refine ⟨748876617898143111792799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15976034515160386384913045 748876617898143111792799)
                      ·
                        rfl

theorem cell23_1458432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 6].length) (baseStart_1458432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458432 prefixEnd_1458432 := by exact prefixLift 1458432
  have htrace : WordTrace (prefixWord ++ tailWord_1458432) baseStart_1458432 baseEnd_1458432 := by
    simpa [prefixWord, tailWord_1458432, baseEnd_1458432] using wordTrace_append hprefix tailTrace_1458432
  have hstable : (prefixWord ++ tailWord_1458432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458432).length < 2 ^ (prefixWord ++ tailWord_1458432).sum := by decide
  have hdescent : baseEnd_1458432 < baseStart_1458432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458442 : List Nat := [3, 1, 2, 2, 1, 1, 2, 11]
def baseStart_1458442 : Nat := 118140960795 + 1458442 * 2 ^ 59
def prefixEnd_1458442 : Nat := 4983230072969 + 3 ^ 40 * 1458442 * 2
def baseEnd_1458442 : Nat := 27736361211284743432139

theorem tailTrace_1458442 : CollatzResearch.WordTrace tailWord_1458442 prefixEnd_1458442 27736361211284743432139 := by
  unfold tailWord_1458442
  simp only [CollatzResearch.WordTrace]
  refine ⟨13298437445580297727068395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35462499854880793938849053 13298437445580297727068395)
  ·
    refine ⟨19947656168370446590602593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13298437445580297727068395 19947656168370446590602593)
    ·
      refine ⟨14960742126277834942951945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19947656168370446590602593 14960742126277834942951945)
      ·
        refine ⟨11220556594708376207213959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14960742126277834942951945 11220556594708376207213959)
        ·
          refine ⟨16830834892062564310820939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11220556594708376207213959 16830834892062564310820939)
          ·
            refine ⟨25246252338093846466231409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16830834892062564310820939 25246252338093846466231409)
            ·
              refine ⟨18934689253570384849673557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25246252338093846466231409 18934689253570384849673557)
              ·
                refine ⟨27736361211284743432139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 18934689253570384849673557 27736361211284743432139)
                ·
                  rfl

theorem cell23_1458442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 2, 11].length) (baseStart_1458442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458442 prefixEnd_1458442 := by exact prefixLift 1458442
  have htrace : WordTrace (prefixWord ++ tailWord_1458442) baseStart_1458442 baseEnd_1458442 := by
    simpa [prefixWord, tailWord_1458442, baseEnd_1458442] using wordTrace_append hprefix tailTrace_1458442
  have hstable : (prefixWord ++ tailWord_1458442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458442).length < 2 ^ (prefixWord ++ tailWord_1458442).sum := by decide
  have hdescent : baseEnd_1458442 < baseStart_1458442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458449 : List Nat := [1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 4]
def baseStart_1458449 : Nat := 118140960795 + 1458449 * 2 ^ 59
def prefixEnd_1458449 : Nat := 4983230072969 + 3 ^ 40 * 1458449 * 2
def baseEnd_1458449 : Nat := 748885347069269545280221

theorem tailTrace_1458449 : CollatzResearch.WordTrace tailWord_1458449 prefixEnd_1458449 748885347069269545280221 := by
  unfold tailWord_1458449
  simp only [CollatzResearch.WordTrace]
  refine ⟨53194005093295831103778401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35462670062197220735852267 53194005093295831103778401)
  ·
    refine ⟨39895503819971873327833801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53194005093295831103778401 39895503819971873327833801)
    ·
      refine ⟨29921627864978904995875351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39895503819971873327833801 29921627864978904995875351)
      ·
        refine ⟨44882441797468357493813027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29921627864978904995875351 44882441797468357493813027)
        ·
          refine ⟨67323662696202536240719541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44882441797468357493813027 67323662696202536240719541)
          ·
            refine ⟨6311593377768987772567457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67323662696202536240719541 6311593377768987772567457)
            ·
              refine ⟨4733695033326740829425593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6311593377768987772567457 4733695033326740829425593)
              ·
                refine ⟨3550271274995055622069195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4733695033326740829425593 3550271274995055622069195)
                ·
                  refine ⟨5325406912492583433103793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3550271274995055622069195 5325406912492583433103793)
                  ·
                    refine ⟨3994055184369437574827845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5325406912492583433103793 3994055184369437574827845)
                    ·
                      refine ⟨748885347069269545280221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3994055184369437574827845 748885347069269545280221)
                      ·
                        rfl

theorem cell23_1458449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 2, 4].length) (baseStart_1458449 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458449 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458449 prefixEnd_1458449 := by exact prefixLift 1458449
  have htrace : WordTrace (prefixWord ++ tailWord_1458449) baseStart_1458449 baseEnd_1458449 := by
    simpa [prefixWord, tailWord_1458449, baseEnd_1458449] using wordTrace_append hprefix tailTrace_1458449
  have hstable : (prefixWord ++ tailWord_1458449).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458449).length < 2 ^ (prefixWord ++ tailWord_1458449).sum := by decide
  have hdescent : baseEnd_1458449 < baseStart_1458449 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458456 : List Nat := [2, 1, 2, 3, 1, 2, 3, 3, 1, 2, 3]
def baseStart_1458456 : Nat := 118140960795 + 1458456 * 2 ^ 59
def prefixEnd_1458456 : Nat := 4983230072969 + 3 ^ 40 * 1458456 * 2
def baseEnd_1458456 : Nat := 748888941433851017892689

theorem tailTrace_1458456 : CollatzResearch.WordTrace tailWord_1458456 prefixEnd_1458456 748888941433851017892689 := by
  unfold tailWord_1458456
  simp only [CollatzResearch.WordTrace]
  refine ⟨26597130202135235649641611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35462840269513647532855481 26597130202135235649641611)
  ·
    refine ⟨39895695303202853474462417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26597130202135235649641611 39895695303202853474462417)
    ·
      refine ⟨29921771477402140105846813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39895695303202853474462417 29921771477402140105846813)
      ·
        refine ⟨11220664304025802539692555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29921771477402140105846813 11220664304025802539692555)
        ·
          refine ⟨16830996456038703809538833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11220664304025802539692555 16830996456038703809538833)
          ·
            refine ⟨12623247342029027857154125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16830996456038703809538833 12623247342029027857154125)
            ·
              refine ⟨4733717753260885446432797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12623247342029027857154125 4733717753260885446432797)
              ·
                refine ⟨1775144157472832042412299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4733717753260885446432797 1775144157472832042412299)
                ·
                  refine ⟨2662716236209248063618449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1775144157472832042412299 2662716236209248063618449)
                  ·
                    refine ⟨1997037177156936047713837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2662716236209248063618449 1997037177156936047713837)
                    ·
                      refine ⟨748888941433851017892689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1997037177156936047713837 748888941433851017892689)
                      ·
                        rfl

theorem cell23_1458456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_1458456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458456 prefixEnd_1458456 := by exact prefixLift 1458456
  have htrace : WordTrace (prefixWord ++ tailWord_1458456) baseStart_1458456 baseEnd_1458456 := by
    simpa [prefixWord, tailWord_1458456, baseEnd_1458456] using wordTrace_append hprefix tailTrace_1458456
  have hstable : (prefixWord ++ tailWord_1458456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458456).length < 2 ^ (prefixWord ++ tailWord_1458456).sum := by decide
  have hdescent : baseEnd_1458456 < baseStart_1458456 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458463 : List Nat := [1, 1, 2, 4, 3, 3, 1, 2, 2, 4]
def baseStart_1458463 : Nat := 118140960795 + 1458463 * 2 ^ 59
def prefixEnd_1458463 : Nat := 4983230072969 + 3 ^ 40 * 1458463 * 2
def baseEnd_1458463 : Nat := 249630845266144163501719

theorem tailTrace_1458463 : CollatzResearch.WordTrace tailWord_1458463 prefixEnd_1458463 249630845266144163501719 := by
  unfold tailWord_1458463
  simp only [CollatzResearch.WordTrace]
  refine ⟨53194515715245111494788043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35463010476830074329858695 53194515715245111494788043)
  ·
    refine ⟨79791773572867667242182065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53194515715245111494788043 79791773572867667242182065)
    ·
      refine ⟨59843830179650750431636549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79791773572867667242182065 59843830179650750431636549)
      ·
        refine ⟨11220718158684515705931853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59843830179650750431636549 11220718158684515705931853)
        ·
          refine ⟨4207769309506693389724445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11220718158684515705931853 4207769309506693389724445)
          ·
            refine ⟨1577913491065010021146667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4207769309506693389724445 1577913491065010021146667)
            ·
              refine ⟨2366870236597515031720001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1577913491065010021146667 2366870236597515031720001)
              ·
                refine ⟨1775152677448136273790001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2366870236597515031720001 1775152677448136273790001)
                ·
                  refine ⟨1331364508086102205342501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1775152677448136273790001 1331364508086102205342501)
                  ·
                    refine ⟨249630845266144163501719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1331364508086102205342501 249630845266144163501719)
                    ·
                      rfl

theorem cell23_1458463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 3, 1, 2, 2, 4].length) (baseStart_1458463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458463 prefixEnd_1458463 := by exact prefixLift 1458463
  have htrace : WordTrace (prefixWord ++ tailWord_1458463) baseStart_1458463 baseEnd_1458463 := by
    simpa [prefixWord, tailWord_1458463, baseEnd_1458463] using wordTrace_append hprefix tailTrace_1458463
  have hstable : (prefixWord ++ tailWord_1458463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458463).length < 2 ^ (prefixWord ++ tailWord_1458463).sum := by decide
  have hdescent : baseEnd_1458463 < baseStart_1458463 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458513 : List Nat := [1, 2, 2, 1, 4, 2, 2, 3, 1, 3, 2]
def baseStart_1458513 : Nat := 118140960795 + 1458513 * 2 ^ 59
def prefixEnd_1458513 : Nat := 4983230072969 + 3 ^ 40 * 1458513 * 2
def baseEnd_1458513 : Nat := 748918209831157294879927

theorem tailTrace_1458513 : CollatzResearch.WordTrace tailWord_1458513 prefixEnd_1458513 748918209831157294879927 := by
  unfold tailWord_1458513
  simp only [CollatzResearch.WordTrace]
  refine ⟨53196339365063970034108193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35464226243375980022738795 53196339365063970034108193)
  ·
    refine ⟨39897254523797977525581145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53196339365063970034108193 39897254523797977525581145)
    ·
      refine ⟨29922940892848483144185859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39897254523797977525581145 29922940892848483144185859)
      ·
        refine ⟨44884411339272724716278789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29922940892848483144185859 44884411339272724716278789)
        ·
          refine ⟨8415827126113635884302273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44884411339272724716278789 8415827126113635884302273)
          ·
            refine ⟨6311870344585226913226705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8415827126113635884302273 6311870344585226913226705)
            ·
              refine ⟨4733902758438920184920029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6311870344585226913226705 4733902758438920184920029)
              ·
                refine ⟨1775213534414595069345011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4733902758438920184920029 1775213534414595069345011)
                ·
                  refine ⟨2662820301621892604017517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1775213534414595069345011 2662820301621892604017517)
                  ·
                    refine ⟨998557613108209726506569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2662820301621892604017517 998557613108209726506569)
                    ·
                      refine ⟨748918209831157294879927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 998557613108209726506569 748918209831157294879927)
                      ·
                        rfl

theorem cell23_1458513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 3, 1, 3, 2].length) (baseStart_1458513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458513 prefixEnd_1458513 := by exact prefixLift 1458513
  have htrace : WordTrace (prefixWord ++ tailWord_1458513) baseStart_1458513 baseEnd_1458513 := by
    simpa [prefixWord, tailWord_1458513, baseEnd_1458513] using wordTrace_append hprefix tailTrace_1458513
  have hstable : (prefixWord ++ tailWord_1458513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458513).length < 2 ^ (prefixWord ++ tailWord_1458513).sum := by decide
  have hdescent : baseEnd_1458513 < baseStart_1458513 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458559 : List Nat := [1, 1, 2, 2, 1, 1, 2, 4, 1, 5, 3]
def baseStart_1458559 : Nat := 118140960795 + 1458559 * 2 ^ 59
def prefixEnd_1458559 : Nat := 4983230072969 + 3 ^ 40 * 1458559 * 2
def baseEnd_1458559 : Nat := 748941829941264114904715

theorem tailTrace_1458559 : CollatzResearch.WordTrace tailWord_1458559 prefixEnd_1458559 748941829941264114904715 := by
  unfold tailWord_1458559
  simp only [CollatzResearch.WordTrace]
  refine ⟨53198017122897319890282731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35465344748598213260188487 53198017122897319890282731)
  ·
    refine ⟨79797025684345979835424097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53198017122897319890282731 79797025684345979835424097)
    ·
      refine ⟨59847769263259484876568073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79797025684345979835424097 59847769263259484876568073)
      ·
        refine ⟨44885826947444613657426055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59847769263259484876568073 44885826947444613657426055)
        ·
          refine ⟨67328740421166920486139083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44885826947444613657426055 67328740421166920486139083)
          ·
            refine ⟨100993110631750380729208625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67328740421166920486139083 100993110631750380729208625)
            ·
              refine ⟨75744832973812785546906469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 100993110631750380729208625 75744832973812785546906469)
              ·
                refine ⟨14202156182589897290044963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75744832973812785546906469 14202156182589897290044963)
                ·
                  refine ⟨21303234273884845935067445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14202156182589897290044963 21303234273884845935067445)
                  ·
                    refine ⟨1997178213176704306412573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 21303234273884845935067445 1997178213176704306412573)
                    ·
                      refine ⟨748941829941264114904715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1997178213176704306412573 748941829941264114904715)
                      ·
                        rfl

theorem cell23_1458559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 4, 1, 5, 3].length) (baseStart_1458559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458559 prefixEnd_1458559 := by exact prefixLift 1458559
  have htrace : WordTrace (prefixWord ++ tailWord_1458559) baseStart_1458559 baseEnd_1458559 := by
    simpa [prefixWord, tailWord_1458559, baseEnd_1458559] using wordTrace_append hprefix tailTrace_1458559
  have hstable : (prefixWord ++ tailWord_1458559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458559).length < 2 ^ (prefixWord ++ tailWord_1458559).sum := by decide
  have hdescent : baseEnd_1458559 < baseStart_1458559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458583 : List Nat := [1, 1, 3, 3, 1, 1, 6, 2, 5]
def baseStart_1458583 : Nat := 118140960795 + 1458583 * 2 ^ 59
def prefixEnd_1458583 : Nat := 4983230072969 + 3 ^ 40 * 1458583 * 2
def baseEnd_1458583 : Nat := 83217128164108002333845

theorem tailTrace_1458583 : CollatzResearch.WordTrace tailWord_1458583 prefixEnd_1458583 83217128164108002333845 := by
  unfold tailWord_1458583
  simp only [CollatzResearch.WordTrace]
  refine ⟨53198892474810371989156403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35465928316540247992770935 53198892474810371989156403)
  ·
    refine ⟨79798338712215557983734605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53198892474810371989156403 79798338712215557983734605)
    ·
      refine ⟨29924377017080834243900477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79798338712215557983734605 29924377017080834243900477)
      ·
        refine ⟨11221641381405312841462679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29924377017080834243900477 11221641381405312841462679)
        ·
          refine ⟨16832462072107969262194019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11221641381405312841462679 16832462072107969262194019)
          ·
            refine ⟨25248693108161953893291029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16832462072107969262194019 25248693108161953893291029)
            ·
              refine ⟨1183532489445091588748017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25248693108161953893291029 1183532489445091588748017)
              ·
                refine ⟨887649367083818691561013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1183532489445091588748017 887649367083818691561013)
                ·
                  refine ⟨83217128164108002333845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 887649367083818691561013 83217128164108002333845)
                  ·
                    rfl

theorem cell23_1458583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 6, 2, 5].length) (baseStart_1458583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458583 prefixEnd_1458583 := by exact prefixLift 1458583
  have htrace : WordTrace (prefixWord ++ tailWord_1458583) baseStart_1458583 baseEnd_1458583 := by
    simpa [prefixWord, tailWord_1458583, baseEnd_1458583] using wordTrace_append hprefix tailTrace_1458583
  have hstable : (prefixWord ++ tailWord_1458583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458583).length < 2 ^ (prefixWord ++ tailWord_1458583).sum := by decide
  have hdescent : baseEnd_1458583 < baseStart_1458583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458616 : List Nat := [2, 1, 2, 1, 2, 2, 1, 1, 3, 6, 2]
def baseStart_1458616 : Nat := 118140960795 + 1458616 * 2 ^ 59
def prefixEnd_1458616 : Nat := 4983230072969 + 3 ^ 40 * 1458616 * 2
def baseEnd_1458616 : Nat := 748971098338570391891953

theorem tailTrace_1458616 : CollatzResearch.WordTrace tailWord_1458616 prefixEnd_1458616 748971098338570391891953 := by
  unfold tailWord_1458616
  simp only [CollatzResearch.WordTrace]
  refine ⟨26600048041845409312553851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35466730722460545750071801 26600048041845409312553851)
  ·
    refine ⟨39900072062768113968830777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26600048041845409312553851 39900072062768113968830777)
    ·
      refine ⟨29925054047076085476623083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39900072062768113968830777 29925054047076085476623083)
      ·
        refine ⟨44887581070614128214934625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29925054047076085476623083 44887581070614128214934625)
        ·
          refine ⟨33665685802960596161200969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44887581070614128214934625 33665685802960596161200969)
          ·
            refine ⟨25249264352220447120900727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33665685802960596161200969 25249264352220447120900727)
            ·
              refine ⟨37873896528330670681351091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25249264352220447120900727 37873896528330670681351091)
              ·
                refine ⟨56810844792496006022026637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 37873896528330670681351091 56810844792496006022026637)
                ·
                  refine ⟨21304066797186002258259989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 56810844792496006022026637 21304066797186002258259989)
                  ·
                    refine ⟨998628131118093855855937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21304066797186002258259989 998628131118093855855937)
                    ·
                      refine ⟨748971098338570391891953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 998628131118093855855937 748971098338570391891953)
                      ·
                        rfl

theorem cell23_1458616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 1, 3, 6, 2].length) (baseStart_1458616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458616 prefixEnd_1458616 := by exact prefixLift 1458616
  have htrace : WordTrace (prefixWord ++ tailWord_1458616) baseStart_1458616 baseEnd_1458616 := by
    simpa [prefixWord, tailWord_1458616, baseEnd_1458616] using wordTrace_append hprefix tailTrace_1458616
  have hstable : (prefixWord ++ tailWord_1458616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458616).length < 2 ^ (prefixWord ++ tailWord_1458616).sum := by decide
  have hdescent : baseEnd_1458616 < baseStart_1458616 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458629 : List Nat := [1, 3, 1, 1, 1, 1, 1, 1, 3, 6, 4]
def baseStart_1458629 : Nat := 118140960795 + 1458629 * 2 ^ 59
def prefixEnd_1458629 : Nat := 4983230072969 + 3 ^ 40 * 1458629 * 2
def baseEnd_1458629 : Nat := 748977773587078841029393

theorem tailTrace_1458629 : CollatzResearch.WordTrace tailWord_1458629 prefixEnd_1458629 748977773587078841029393 := by
  unfold tailWord_1458629
  simp only [CollatzResearch.WordTrace]
  refine ⟨53200570232643721845330941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35467046821762481230220627 53200570232643721845330941)
  ·
    refine ⟨19950213837241395691999103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53200570232643721845330941 19950213837241395691999103)
    ·
      refine ⟨29925320755862093537998655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19950213837241395691999103 29925320755862093537998655)
      ·
        refine ⟨44887981133793140306997983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29925320755862093537998655 44887981133793140306997983)
        ·
          refine ⟨67331971700689710460496975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44887981133793140306997983 67331971700689710460496975)
          ·
            refine ⟨100997957551034565690745463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67331971700689710460496975 100997957551034565690745463)
            ·
              refine ⟨151496936326551848536118195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 100997957551034565690745463 151496936326551848536118195)
              ·
                refine ⟨227245404489827772804177293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 151496936326551848536118195 227245404489827772804177293)
                ·
                  refine ⟨85217026683685414801566485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 227245404489827772804177293 85217026683685414801566485)
                  ·
                    refine ⟨3994548125797753818823429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85217026683685414801566485 3994548125797753818823429)
                    ·
                      refine ⟨748977773587078841029393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3994548125797753818823429 748977773587078841029393)
                      ·
                        rfl

theorem cell23_1458629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 3, 6, 4].length) (baseStart_1458629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458629 prefixEnd_1458629 := by exact prefixLift 1458629
  have htrace : WordTrace (prefixWord ++ tailWord_1458629) baseStart_1458629 baseEnd_1458629 := by
    simpa [prefixWord, tailWord_1458629, baseEnd_1458629] using wordTrace_append hprefix tailTrace_1458629
  have hstable : (prefixWord ++ tailWord_1458629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458629).length < 2 ^ (prefixWord ++ tailWord_1458629).sum := by decide
  have hdescent : baseEnd_1458629 < baseStart_1458629 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458679 : List Nat := [1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 7]
def baseStart_1458679 : Nat := 118140960795 + 1458679 * 2 ^ 59
def prefixEnd_1458679 : Nat := 4983230072969 + 3 ^ 40 * 1458679 * 2
def baseEnd_1458679 : Nat := 749003447619803645404163

theorem tailTrace_1458679 : CollatzResearch.WordTrace tailWord_1458679 prefixEnd_1458679 749003447619803645404163 := by
  unfold tailWord_1458679
  simp only [CollatzResearch.WordTrace]
  refine ⟨53202393882462580384651091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35468262588308386923100727 53202393882462580384651091)
  ·
    refine ⟨79803590823693870576976637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53202393882462580384651091 79803590823693870576976637)
    ·
      refine ⟨29926346558885201466366239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79803590823693870576976637 29926346558885201466366239)
      ·
        refine ⟨44889519838327802199549359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29926346558885201466366239 44889519838327802199549359)
        ·
          refine ⟨67334279757491703299324039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44889519838327802199549359 67334279757491703299324039)
          ·
            refine ⟨101001419636237554948986059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67334279757491703299324039 101001419636237554948986059)
            ·
              refine ⟨151502129454356332423479089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101001419636237554948986059 151502129454356332423479089)
              ·
                refine ⟨113626597090767249317609317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151502129454356332423479089 113626597090767249317609317)
                ·
                  refine ⟨21304986954518859247051747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113626597090767249317609317 21304986954518859247051747)
                  ·
                    refine ⟨31957480431778288870577621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21304986954518859247051747 31957480431778288870577621)
                    ·
                      refine ⟨749003447619803645404163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 31957480431778288870577621 749003447619803645404163)
                      ·
                        rfl

theorem cell23_1458679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 1, 7].length) (baseStart_1458679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458679 prefixEnd_1458679 := by exact prefixLift 1458679
  have htrace : WordTrace (prefixWord ++ tailWord_1458679) baseStart_1458679 baseEnd_1458679 := by
    simpa [prefixWord, tailWord_1458679, baseEnd_1458679] using wordTrace_append hprefix tailTrace_1458679
  have hstable : (prefixWord ++ tailWord_1458679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458679).length < 2 ^ (prefixWord ++ tailWord_1458679).sum := by decide
  have hdescent : baseEnd_1458679 < baseStart_1458679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458693 : List Nat := [1, 3, 1, 1, 2, 2, 3, 1, 4, 3, 2]
def baseStart_1458693 : Nat := 118140960795 + 1458693 * 2 ^ 59
def prefixEnd_1458693 : Nat := 4983230072969 + 3 ^ 40 * 1458693 * 2
def baseEnd_1458693 : Nat := 749010636348966590629099

theorem tailTrace_1458693 : CollatzResearch.WordTrace tailWord_1458693 prefixEnd_1458693 749010636348966590629099 := by
  unfold tailWord_1458693
  simp only [CollatzResearch.WordTrace]
  refine ⟨53202904504411860775660733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35468603002941240517107155 53202904504411860775660733)
  ·
    refine ⟨19951089189154447790872775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53202904504411860775660733 19951089189154447790872775)
    ·
      refine ⟨29926633783731671686309163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19951089189154447790872775 29926633783731671686309163)
      ·
        refine ⟨44889950675597507529463745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29926633783731671686309163 44889950675597507529463745)
        ·
          refine ⟨33667463006698130647097809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44889950675597507529463745 33667463006698130647097809)
          ·
            refine ⟨25250597255023597985323357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33667463006698130647097809 25250597255023597985323357)
            ·
              refine ⟨9468973970633849244496259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25250597255023597985323357 9468973970633849244496259)
              ·
                refine ⟨14203460955950773866744389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9468973970633849244496259 14203460955950773866744389)
                ·
                  refine ⟨2663148929240770100014573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14203460955950773866744389 2663148929240770100014573)
                  ·
                    refine ⟨998680848465288787505465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2663148929240770100014573 998680848465288787505465)
                    ·
                      refine ⟨749010636348966590629099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 998680848465288787505465 749010636348966590629099)
                      ·
                        rfl

theorem cell23_1458693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 3, 1, 4, 3, 2].length) (baseStart_1458693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458693 prefixEnd_1458693 := by exact prefixLift 1458693
  have htrace : WordTrace (prefixWord ++ tailWord_1458693) baseStart_1458693 baseEnd_1458693 := by
    simpa [prefixWord, tailWord_1458693, baseEnd_1458693] using wordTrace_append hprefix tailTrace_1458693
  have hstable : (prefixWord ++ tailWord_1458693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458693).length < 2 ^ (prefixWord ++ tailWord_1458693).sum := by decide
  have hdescent : baseEnd_1458693 < baseStart_1458693 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458694 : List Nat := [6, 2, 1, 1, 1, 1, 3, 1, 3, 4]
def baseStart_1458694 : Nat := 118140960795 + 1458694 * 2 ^ 59
def prefixEnd_1458694 : Nat := 4983230072969 + 3 ^ 40 * 1458694 * 2
def baseEnd_1458694 : Nat := 249670383276540362238865

theorem tailTrace_1458694 : CollatzResearch.WordTrace tailWord_1458694 prefixEnd_1458694 249670383276540362238865 := by
  unfold tailWord_1458694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1662591905544007435826473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 35468627318272158630964757 1662591905544007435826473)
  ·
    refine ⟨1246943929158005576869855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1662591905544007435826473 1246943929158005576869855)
    ·
      refine ⟨1870415893737008365304783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1246943929158005576869855 1870415893737008365304783)
      ·
        refine ⟨2805623840605512547957175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1870415893737008365304783 2805623840605512547957175)
        ·
          refine ⟨4208435760908268821935763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2805623840605512547957175 4208435760908268821935763)
          ·
            refine ⟨6312653641362403232903645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4208435760908268821935763 6312653641362403232903645)
            ·
              refine ⟨2367245115510901212338867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6312653641362403232903645 2367245115510901212338867)
              ·
                refine ⟨3550867673266351818508301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2367245115510901212338867 3550867673266351818508301)
                ·
                  refine ⟨1331575377474881931940613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3550867673266351818508301 1331575377474881931940613)
                  ·
                    refine ⟨249670383276540362238865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1331575377474881931940613 249670383276540362238865)
                    ·
                      rfl

theorem cell23_1458694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 3, 1, 3, 4].length) (baseStart_1458694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458694 prefixEnd_1458694 := by exact prefixLift 1458694
  have htrace : WordTrace (prefixWord ++ tailWord_1458694) baseStart_1458694 baseEnd_1458694 := by
    simpa [prefixWord, tailWord_1458694, baseEnd_1458694] using wordTrace_append hprefix tailTrace_1458694
  have hstable : (prefixWord ++ tailWord_1458694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458694).length < 2 ^ (prefixWord ++ tailWord_1458694).sum := by decide
  have hdescent : baseEnd_1458694 < baseStart_1458694 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458700 : List Nat := [2, 2, 1, 2, 4, 1, 3, 1, 3, 1, 3]
def baseStart_1458700 : Nat := 118140960795 + 1458700 * 2 ^ 59
def prefixEnd_1458700 : Nat := 4983230072969 + 3 ^ 40 * 1458700 * 2
def baseEnd_1458700 : Nat := 749014230713548063241567

theorem tailTrace_1458700 : CollatzResearch.WordTrace tailWord_1458700 prefixEnd_1458700 749014230713548063241567 := by
  unfold tailWord_1458700
  simp only [CollatzResearch.WordTrace]
  refine ⟨26601579907693250485582777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35468773210257667314110369 26601579907693250485582777)
  ·
    refine ⟨19951184930769937864187083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26601579907693250485582777 19951184930769937864187083)
    ·
      refine ⟨29926777396154906796280625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19951184930769937864187083 29926777396154906796280625)
      ·
        refine ⟨22445083047116180097210469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29926777396154906796280625 22445083047116180097210469)
        ·
          refine ⟨4208453071334283768226963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22445083047116180097210469 4208453071334283768226963)
          ·
            refine ⟨6312679607001425652340445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4208453071334283768226963 6312679607001425652340445)
            ·
              refine ⟨2367254852625534619627667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6312679607001425652340445 2367254852625534619627667)
              ·
                refine ⟨3550882278938301929441501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2367254852625534619627667 3550882278938301929441501)
                ·
                  refine ⟨1331580854601863223540563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3550882278938301929441501 1331580854601863223540563)
                  ·
                    refine ⟨1997371281902794835310845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1331580854601863223540563 1997371281902794835310845)
                    ·
                      refine ⟨749014230713548063241567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1997371281902794835310845 749014230713548063241567)
                      ·
                        rfl

theorem cell23_1458700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 3, 1, 3, 1, 3].length) (baseStart_1458700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458700 prefixEnd_1458700 := by exact prefixLift 1458700
  have htrace : WordTrace (prefixWord ++ tailWord_1458700) baseStart_1458700 baseEnd_1458700 := by
    simpa [prefixWord, tailWord_1458700, baseEnd_1458700] using wordTrace_append hprefix tailTrace_1458700
  have hstable : (prefixWord ++ tailWord_1458700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458700).length < 2 ^ (prefixWord ++ tailWord_1458700).sum := by decide
  have hdescent : baseEnd_1458700 < baseStart_1458700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458723 : List Nat := [1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 4]
def baseStart_1458723 : Nat := 118140960795 + 1458723 * 2 ^ 59
def prefixEnd_1458723 : Nat := 4983230072969 + 3 ^ 40 * 1458723 * 2
def baseEnd_1458723 : Nat := 749026040768601473253961

theorem tailTrace_1458723 : CollatzResearch.WordTrace tailWord_1458723 prefixEnd_1458723 749026040768601473253961 := by
  unfold tailWord_1458723
  simp only [CollatzResearch.WordTrace]
  refine ⟨53203998694303175899252823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35469332462868783932835215 53203998694303175899252823)
  ·
    refine ⟨79805998041454763848879235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53203998694303175899252823 79805998041454763848879235)
    ·
      refine ⟨119708997062182145773318853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79805998041454763848879235 119708997062182145773318853)
      ·
        refine ⟨22445436949159152332497285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119708997062182145773318853 22445436949159152332497285)
        ·
          refine ⟨4208519427967341062343241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22445436949159152332497285 4208519427967341062343241)
          ·
            refine ⟨3156389570975505796757431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4208519427967341062343241 3156389570975505796757431)
            ·
              refine ⟨4734584356463258695136147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3156389570975505796757431 4734584356463258695136147)
              ·
                refine ⟨7101876534694888042704221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4734584356463258695136147 7101876534694888042704221)
                ·
                  refine ⟨2663203700510583016014083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7101876534694888042704221 2663203700510583016014083)
                  ·
                    refine ⟨3994805550765874524021125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2663203700510583016014083 3994805550765874524021125)
                    ·
                      refine ⟨749026040768601473253961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3994805550765874524021125 749026040768601473253961)
                      ·
                        rfl

theorem cell23_1458723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 2, 1, 1, 3, 1, 4].length) (baseStart_1458723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458723 prefixEnd_1458723 := by exact prefixLift 1458723
  have htrace : WordTrace (prefixWord ++ tailWord_1458723) baseStart_1458723 baseEnd_1458723 := by
    simpa [prefixWord, tailWord_1458723, baseEnd_1458723] using wordTrace_append hprefix tailTrace_1458723
  have hstable : (prefixWord ++ tailWord_1458723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458723).length < 2 ^ (prefixWord ++ tailWord_1458723).sum := by decide
  have hdescent : baseEnd_1458723 < baseStart_1458723 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458736 : List Nat := [2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 4]
def baseStart_1458736 : Nat := 118140960795 + 1458736 * 2 ^ 59
def prefixEnd_1458736 : Nat := 4983230072969 + 3 ^ 40 * 1458736 * 2
def baseEnd_1458736 : Nat := 749032716017109922391401

theorem tailTrace_1458736 : CollatzResearch.WordTrace tailWord_1458736 prefixEnd_1458736 749032716017109922391401 := by
  unfold tailWord_1458736
  simp only [CollatzResearch.WordTrace]
  refine ⟨26602236421628039559738031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35469648562170719412984041 26602236421628039559738031)
  ·
    refine ⟨39903354632442059339607047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26602236421628039559738031 39903354632442059339607047)
    ·
      refine ⟨59855031948663089009410571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39903354632442059339607047 59855031948663089009410571)
      ·
        refine ⟨89782547922994633514115857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59855031948663089009410571 89782547922994633514115857)
        ·
          refine ⟨67336910942245975135586893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89782547922994633514115857 67336910942245975135586893)
          ·
            refine ⟨25251341603342240675845085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67336910942245975135586893 25251341603342240675845085)
            ·
              refine ⟨9469253101253340253441907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25251341603342240675845085 9469253101253340253441907)
              ·
                refine ⟨14203879651880010380162861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9469253101253340253441907 14203879651880010380162861)
                ·
                  refine ⟨5326454869455003892561073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14203879651880010380162861 5326454869455003892561073)
                  ·
                    refine ⟨3994841152091252919420805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5326454869455003892561073 3994841152091252919420805)
                    ·
                      refine ⟨749032716017109922391401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3994841152091252919420805 749032716017109922391401)
                      ·
                        rfl

theorem cell23_1458736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 1, 3, 2, 4].length) (baseStart_1458736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458736 prefixEnd_1458736 := by exact prefixLift 1458736
  have htrace : WordTrace (prefixWord ++ tailWord_1458736) baseStart_1458736 baseEnd_1458736 := by
    simpa [prefixWord, tailWord_1458736, baseEnd_1458736] using wordTrace_append hprefix tailTrace_1458736
  have hstable : (prefixWord ++ tailWord_1458736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458736).length < 2 ^ (prefixWord ++ tailWord_1458736).sum := by decide
  have hdescent : baseEnd_1458736 < baseStart_1458736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458766 : List Nat := [4, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6]
def baseStart_1458766 : Nat := 118140960795 + 1458766 * 2 ^ 59
def prefixEnd_1458766 : Nat := 4983230072969 + 3 ^ 40 * 1458766 * 2
def baseEnd_1458766 : Nat := 749048120436744805016263

theorem tailTrace_1458766 : CollatzResearch.WordTrace tailWord_1458766 prefixEnd_1458766 749048120436744805016263 := by
  unfold tailWord_1458766
  simp only [CollatzResearch.WordTrace]
  refine ⟨6650695879143424280383519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35470378022098262828712101 6650695879143424280383519)
  ·
    refine ⟨9976043818715136420575279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6650695879143424280383519 9976043818715136420575279)
    ·
      refine ⟨14964065728072704630862919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9976043818715136420575279 14964065728072704630862919)
      ·
        refine ⟨22446098592109056946294379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14964065728072704630862919 22446098592109056946294379)
        ·
          refine ⟨33669147888163585419441569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22446098592109056946294379 33669147888163585419441569)
          ·
            refine ⟨25251860916122689064581177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33669147888163585419441569 25251860916122689064581177)
            ·
              refine ⟨18938895687092016798435883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25251860916122689064581177 18938895687092016798435883)
              ·
                refine ⟨28408343530638025197653825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18938895687092016798435883 28408343530638025197653825)
                ·
                  refine ⟨21306257647978518898240369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28408343530638025197653825 21306257647978518898240369)
                  ·
                    refine ⟨15979693235983889173680277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21306257647978518898240369 15979693235983889173680277)
                    ·
                      refine ⟨749048120436744805016263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 15979693235983889173680277 749048120436744805016263)
                      ·
                        rfl

theorem cell23_1458766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 1, 2, 2, 6].length) (baseStart_1458766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458766 prefixEnd_1458766 := by exact prefixLift 1458766
  have htrace : WordTrace (prefixWord ++ tailWord_1458766) baseStart_1458766 baseEnd_1458766 := by
    simpa [prefixWord, tailWord_1458766, baseEnd_1458766] using wordTrace_append hprefix tailTrace_1458766
  have hstable : (prefixWord ++ tailWord_1458766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458766).length < 2 ^ (prefixWord ++ tailWord_1458766).sum := by decide
  have hdescent : baseEnd_1458766 < baseStart_1458766 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458773 : List Nat := [1, 3, 2, 2, 1, 1, 3, 3, 1, 3, 3]
def baseStart_1458773 : Nat := 118140960795 + 1458773 * 2 ^ 59
def prefixEnd_1458773 : Nat := 4983230072969 + 3 ^ 40 * 1458773 * 2
def baseEnd_1458773 : Nat := 749051714801326277628731

theorem tailTrace_1458773 : CollatzResearch.WordTrace tailWord_1458773 prefixEnd_1458773 749051714801326277628731 := by
  unfold tailWord_1458773
  simp only [CollatzResearch.WordTrace]
  refine ⟨53205822344122034438572973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35470548229414689625715315 53205822344122034438572973)
  ·
    refine ⟨19952183379045762914464865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53205822344122034438572973 19952183379045762914464865)
    ·
      refine ⟨14964137534284322185848649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19952183379045762914464865 14964137534284322185848649)
      ·
        refine ⟨11223103150713241639386487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14964137534284322185848649 11223103150713241639386487)
        ·
          refine ⟨16834654726069862459079731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11223103150713241639386487 16834654726069862459079731)
          ·
            refine ⟨25251982089104793688619597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16834654726069862459079731 25251982089104793688619597)
            ·
              refine ⟨9469493283414297633232349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25251982089104793688619597 9469493283414297633232349)
              ·
                refine ⟨3551059981280361612462131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9469493283414297633232349 3551059981280361612462131)
                ·
                  refine ⟨5326589971920542418693197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3551059981280361612462131 5326589971920542418693197)
                  ·
                    refine ⟨1997471239470203407009949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5326589971920542418693197 1997471239470203407009949)
                    ·
                      refine ⟨749051714801326277628731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1997471239470203407009949 749051714801326277628731)
                      ·
                        rfl

theorem cell23_1458773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 3, 3, 1, 3, 3].length) (baseStart_1458773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458773 prefixEnd_1458773 := by exact prefixLift 1458773
  have htrace : WordTrace (prefixWord ++ tailWord_1458773) baseStart_1458773 baseEnd_1458773 := by
    simpa [prefixWord, tailWord_1458773, baseEnd_1458773] using wordTrace_append hprefix tailTrace_1458773
  have hstable : (prefixWord ++ tailWord_1458773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458773).length < 2 ^ (prefixWord ++ tailWord_1458773).sum := by decide
  have hdescent : baseEnd_1458773 < baseStart_1458773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458780 : List Nat := [2, 2, 4, 1, 3, 1, 3, 7]
def baseStart_1458780 : Nat := 118140960795 + 1458780 * 2 ^ 59
def prefixEnd_1458780 : Nat := 4983230072969 + 3 ^ 40 * 1458780 * 2
def baseEnd_1458780 : Nat := 27742789228366953712637

theorem tailTrace_1458780 : CollatzResearch.WordTrace tailWord_1458780 prefixEnd_1458780 27742789228366953712637 := by
  unfold tailWord_1458780
  simp only [CollatzResearch.WordTrace]
  refine ⟨26603038827548337317038897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35470718436731116422718529 26603038827548337317038897)
  ·
    refine ⟨19952279120661252987779173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26603038827548337317038897 19952279120661252987779173)
    ·
      refine ⟨3741052335123984935208595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19952279120661252987779173 3741052335123984935208595)
      ·
        refine ⟨5611578502685977402812893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3741052335123984935208595 5611578502685977402812893)
        ·
          refine ⟨2104341938507241526054835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5611578502685977402812893 2104341938507241526054835)
          ·
            refine ⟨3156512907760862289082253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2104341938507241526054835 3156512907760862289082253)
            ·
              refine ⟨1183692340410323358405845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3156512907760862289082253 1183692340410323358405845)
              ·
                refine ⟨27742789228366953712637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1183692340410323358405845 27742789228366953712637)
                ·
                  rfl

theorem cell23_1458780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 3, 1, 3, 7].length) (baseStart_1458780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458780 prefixEnd_1458780 := by exact prefixLift 1458780
  have htrace : WordTrace (prefixWord ++ tailWord_1458780) baseStart_1458780 baseEnd_1458780 := by
    simpa [prefixWord, tailWord_1458780, baseEnd_1458780] using wordTrace_append hprefix tailTrace_1458780
  have hstable : (prefixWord ++ tailWord_1458780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458780).length < 2 ^ (prefixWord ++ tailWord_1458780).sum := by decide
  have hdescent : baseEnd_1458780 < baseStart_1458780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458818 : List Nat := [3, 4, 3, 1, 1, 1, 3, 1, 2, 4]
def baseStart_1458818 : Nat := 118140960795 + 1458818 * 2 ^ 59
def prefixEnd_1458818 : Nat := 4983230072969 + 3 ^ 40 * 1458818 * 2
def baseEnd_1458818 : Nat := 249691607143592867188675

theorem tailTrace_1458818 : CollatzResearch.WordTrace tailWord_1458818 prefixEnd_1458818 249691607143592867188675 := by
  unfold tailWord_1458818
  simp only [CollatzResearch.WordTrace]
  refine ⟨13301865907239751780990277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35471642419306004749307405 13301865907239751780990277)
  ·
    refine ⟨2494099857607453458935677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13301865907239751780990277 2494099857607453458935677)
    ·
      refine ⟨935287446602795047100879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2494099857607453458935677 935287446602795047100879)
      ·
        refine ⟨1402931169904192570651319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 935287446602795047100879 1402931169904192570651319)
        ·
          refine ⟨2104396754856288855976979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1402931169904192570651319 2104396754856288855976979)
          ·
            refine ⟨3156595132284433283965469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2104396754856288855976979 3156595132284433283965469)
            ·
              refine ⟨1183723174606662481487051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3156595132284433283965469 1183723174606662481487051)
              ·
                refine ⟨1775584761909993722230577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1183723174606662481487051 1775584761909993722230577)
                ·
                  refine ⟨1331688571432495291672933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1775584761909993722230577 1331688571432495291672933)
                  ·
                    refine ⟨249691607143592867188675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1331688571432495291672933 249691607143592867188675)
                    ·
                      rfl

theorem cell23_1458818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_1458818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458818 prefixEnd_1458818 := by exact prefixLift 1458818
  have htrace : WordTrace (prefixWord ++ tailWord_1458818) baseStart_1458818 baseEnd_1458818 := by
    simpa [prefixWord, tailWord_1458818, baseEnd_1458818] using wordTrace_append hprefix tailTrace_1458818
  have hstable : (prefixWord ++ tailWord_1458818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458818).length < 2 ^ (prefixWord ++ tailWord_1458818).sum := by decide
  have hdescent : baseEnd_1458818 < baseStart_1458818 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458834 : List Nat := [3, 2, 3, 1, 2, 2, 2, 2, 1, 3, 2]
def baseStart_1458834 : Nat := 118140960795 + 1458834 * 2 ^ 59
def prefixEnd_1458834 : Nat := 4983230072969 + 3 ^ 40 * 1458834 * 2
def baseEnd_1458834 : Nat := 749083037121250538965951

theorem tailTrace_1458834 : CollatzResearch.WordTrace tailWord_1458834 prefixEnd_1458834 749083037121250538965951 := by
  unfold tailWord_1458834
  simp only [CollatzResearch.WordTrace]
  refine ⟨13302011799225260464135889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35472031464600694571029037 13302011799225260464135889)
  ·
    refine ⟨9976508849418945348101917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13302011799225260464135889 9976508849418945348101917)
    ·
      refine ⟨3741190818532104505538219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9976508849418945348101917 3741190818532104505538219)
      ·
        refine ⟨5611786227798156758307329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3741190818532104505538219 5611786227798156758307329)
        ·
          refine ⟨4208839670848617568730497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5611786227798156758307329 4208839670848617568730497)
          ·
            refine ⟨3156629753136463176547873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4208839670848617568730497 3156629753136463176547873)
            ·
              refine ⟨2367472314852347382410905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3156629753136463176547873 2367472314852347382410905)
              ·
                refine ⟨1775604236139260536808179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2367472314852347382410905 1775604236139260536808179)
                ·
                  refine ⟨2663406354208890805212269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1775604236139260536808179 2663406354208890805212269)
                  ·
                    refine ⟨998777382828334051954601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2663406354208890805212269 998777382828334051954601)
                    ·
                      refine ⟨749083037121250538965951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 998777382828334051954601 749083037121250538965951)
                      ·
                        rfl

theorem cell23_1458834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 2, 2, 1, 3, 2].length) (baseStart_1458834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458834 prefixEnd_1458834 := by exact prefixLift 1458834
  have htrace : WordTrace (prefixWord ++ tailWord_1458834) baseStart_1458834 baseEnd_1458834 := by
    simpa [prefixWord, tailWord_1458834, baseEnd_1458834] using wordTrace_append hprefix tailTrace_1458834
  have hstable : (prefixWord ++ tailWord_1458834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458834).length < 2 ^ (prefixWord ++ tailWord_1458834).sum := by decide
  have hdescent : baseEnd_1458834 < baseStart_1458834 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458923 : List Nat := [1, 1, 1, 1, 2, 4, 1, 2, 3, 4, 3]
def baseStart_1458923 : Nat := 118140960795 + 1458923 * 2 ^ 59
def prefixEnd_1458923 : Nat := 4983230072969 + 3 ^ 40 * 1458923 * 2
def baseEnd_1458923 : Nat := 749128736899500690753041

theorem tailTrace_1458923 : CollatzResearch.WordTrace tailWord_1458923 prefixEnd_1458923 749128736899500690753041 := by
  unfold tailWord_1458923
  simp only [CollatzResearch.WordTrace]
  refine ⟨53211293293578610056533423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35474195529052406704355615 53211293293578610056533423)
  ·
    refine ⟨79816939940367915084800135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53211293293578610056533423 79816939940367915084800135)
    ·
      refine ⟨119725409910551872627200203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79816939940367915084800135 119725409910551872627200203)
      ·
        refine ⟨179588114865827808940800305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119725409910551872627200203 179588114865827808940800305)
        ·
          refine ⟨134691086149370856705600229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 179588114865827808940800305 134691086149370856705600229)
          ·
            refine ⟨25254578653007035632300043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134691086149370856705600229 25254578653007035632300043)
            ·
              refine ⟨37881867979510553448450065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25254578653007035632300043 37881867979510553448450065)
              ·
                refine ⟨28411400984632915086337549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37881867979510553448450065 28411400984632915086337549)
                ·
                  refine ⟨10654275369237343157376581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28411400984632915086337549 10654275369237343157376581)
                  ·
                    refine ⟨1997676631732001842008109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10654275369237343157376581 1997676631732001842008109)
                    ·
                      refine ⟨749128736899500690753041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1997676631732001842008109 749128736899500690753041)
                      ·
                        rfl

theorem cell23_1458923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 1, 2, 3, 4, 3].length) (baseStart_1458923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458923 prefixEnd_1458923 := by exact prefixLift 1458923
  have htrace : WordTrace (prefixWord ++ tailWord_1458923) baseStart_1458923 baseEnd_1458923 := by
    simpa [prefixWord, tailWord_1458923, baseEnd_1458923] using wordTrace_append hprefix tailTrace_1458923
  have hstable : (prefixWord ++ tailWord_1458923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458923).length < 2 ^ (prefixWord ++ tailWord_1458923).sum := by decide
  have hdescent : baseEnd_1458923 < baseStart_1458923 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1458997 : List Nat := [1, 3, 3, 1, 3, 1, 1, 2, 1, 5, 2]
def baseStart_1458997 : Nat := 118140960795 + 1458997 * 2 ^ 59
def prefixEnd_1458997 : Nat := 4983230072969 + 3 ^ 40 * 1458997 * 2
def baseEnd_1458997 : Nat := 749166734467933401227701

theorem tailTrace_1458997 : CollatzResearch.WordTrace tailWord_1458997 prefixEnd_1458997 749166734467933401227701 := by
  unfold tailWord_1458997
  simp only [CollatzResearch.WordTrace]
  refine ⟨53213992295310520694727245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35475994863540347129818163 53213992295310520694727245)
  ·
    refine ⟨19955247110741445260522717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53213992295310520694727245 19955247110741445260522717)
    ·
      refine ⟨7483217666528041972696019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19955247110741445260522717 7483217666528041972696019)
      ·
        refine ⟨11224826499792062959044029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7483217666528041972696019 11224826499792062959044029)
        ·
          refine ⟨4209309937422023609641511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11224826499792062959044029 4209309937422023609641511)
          ·
            refine ⟨6313964906133035414462267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4209309937422023609641511 6313964906133035414462267)
            ·
              refine ⟨9470947359199553121693401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6313964906133035414462267 9470947359199553121693401)
              ·
                refine ⟨7103210519399664841270051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9470947359199553121693401 7103210519399664841270051)
                ·
                  refine ⟨10654815779099497261905077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7103210519399664841270051 10654815779099497261905077)
                  ·
                    refine ⟨998888979290577868303601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10654815779099497261905077 998888979290577868303601)
                    ·
                      refine ⟨749166734467933401227701, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 998888979290577868303601 749166734467933401227701)
                      ·
                        rfl

theorem cell23_1458997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_1458997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1458997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1458997 prefixEnd_1458997 := by exact prefixLift 1458997
  have htrace : WordTrace (prefixWord ++ tailWord_1458997) baseStart_1458997 baseEnd_1458997 := by
    simpa [prefixWord, tailWord_1458997, baseEnd_1458997] using wordTrace_append hprefix tailTrace_1458997
  have hstable : (prefixWord ++ tailWord_1458997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1458997).length < 2 ^ (prefixWord ++ tailWord_1458997).sum := by decide
  have hdescent : baseEnd_1458997 < baseStart_1458997 := by decide
  rcases family_descends (prefixWord ++ tailWord_1458997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459007 : List Nat := [1, 1, 2, 2, 5, 2, 2, 2, 1, 5]
def baseStart_1459007 : Nat := 118140960795 + 1459007 * 2 ^ 59
def prefixEnd_1459007 : Nat := 4983230072969 + 3 ^ 40 * 1459007 * 2
def baseEnd_1459007 : Nat := 249723956424826120700885

theorem tailTrace_1459007 : CollatzResearch.WordTrace tailWord_1459007 prefixEnd_1459007 249723956424826120700885 := by
  unfold tailWord_1459007
  simp only [CollatzResearch.WordTrace]
  refine ⟨53214357025274292402591275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35476238016849528268394183 53214357025274292402591275)
  ·
    refine ⟨79821535537911438603886913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53214357025274292402591275 79821535537911438603886913)
    ·
      refine ⟨59866151653433578952915185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79821535537911438603886913 59866151653433578952915185)
      ·
        refine ⟨44899613740075184214686389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59866151653433578952915185 44899613740075184214686389)
        ·
          refine ⟨4209338788132048520126849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 44899613740075184214686389 4209338788132048520126849)
          ·
            refine ⟨3157004091099036390095137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4209338788132048520126849 3157004091099036390095137)
            ·
              refine ⟨2367753068324277292571353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3157004091099036390095137 2367753068324277292571353)
              ·
                refine ⟨1775814801243207969428515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2367753068324277292571353 1775814801243207969428515)
                ·
                  refine ⟨2663722201864811954142773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1775814801243207969428515 2663722201864811954142773)
                  ·
                    refine ⟨249723956424826120700885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2663722201864811954142773 249723956424826120700885)
                    ·
                      rfl

theorem cell23_1459007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 2, 2, 1, 5].length) (baseStart_1459007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459007 prefixEnd_1459007 := by exact prefixLift 1459007
  have htrace : WordTrace (prefixWord ++ tailWord_1459007) baseStart_1459007 baseEnd_1459007 := by
    simpa [prefixWord, tailWord_1459007, baseEnd_1459007] using wordTrace_append hprefix tailTrace_1459007
  have hstable : (prefixWord ++ tailWord_1459007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459007).length < 2 ^ (prefixWord ++ tailWord_1459007).sum := by decide
  have hdescent : baseEnd_1459007 < baseStart_1459007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459027 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 5, 2, 2]
def baseStart_1459027 : Nat := 118140960795 + 1459027 * 2 ^ 59
def prefixEnd_1459027 : Nat := 4983230072969 + 3 ^ 40 * 1459027 * 2
def baseEnd_1459027 : Nat := 749182138887568283852563

theorem tailTrace_1459027 : CollatzResearch.WordTrace tailWord_1459027 prefixEnd_1459027 749182138887568283852563 := by
  unfold tailWord_1459027
  simp only [CollatzResearch.WordTrace]
  refine ⟨53215086485201835818319335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35476724323467890545546223 53215086485201835818319335)
  ·
    refine ⟨79822629727802753727479003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53215086485201835818319335 79822629727802753727479003)
    ·
      refine ⟨119733944591704130591218505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79822629727802753727479003 119733944591704130591218505)
      ·
        refine ⟨89800458443778097943413879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119733944591704130591218505 89800458443778097943413879)
        ·
          refine ⟨134700687665667146915120819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89800458443778097943413879 134700687665667146915120819)
          ·
            refine ⟨202051031498500720372681229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134700687665667146915120819 202051031498500720372681229)
            ·
              refine ⟨75769136811937770139755461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202051031498500720372681229 75769136811937770139755461)
              ·
                refine ⟨14206713152238331901204149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75769136811937770139755461 14206713152238331901204149)
                ·
                  refine ⟨1331879358022343615737889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14206713152238331901204149 1331879358022343615737889)
                  ·
                    refine ⟨998909518516757711803417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1331879358022343615737889 998909518516757711803417)
                    ·
                      refine ⟨749182138887568283852563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 998909518516757711803417 749182138887568283852563)
                      ·
                        rfl

theorem cell23_1459027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 5, 2, 2].length) (baseStart_1459027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459027 prefixEnd_1459027 := by exact prefixLift 1459027
  have htrace : WordTrace (prefixWord ++ tailWord_1459027) baseStart_1459027 baseEnd_1459027 := by
    simpa [prefixWord, tailWord_1459027, baseEnd_1459027] using wordTrace_append hprefix tailTrace_1459027
  have hstable : (prefixWord ++ tailWord_1459027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459027).length < 2 ^ (prefixWord ++ tailWord_1459027).sum := by decide
  have hdescent : baseEnd_1459027 < baseStart_1459027 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459033 : List Nat := [1, 2, 1, 2, 2, 4, 11]
def baseStart_1459033 : Nat := 118140960795 + 1459033 * 2 ^ 59
def prefixEnd_1459033 : Nat := 4983230072969 + 3 ^ 40 * 1459033 * 2
def baseEnd_1459033 : Nat := 9249200244092534078735

theorem tailTrace_1459033 : CollatzResearch.WordTrace tailWord_1459033 prefixEnd_1459033 9249200244092534078735 := by
  unfold tailWord_1459033
  simp only [CollatzResearch.WordTrace]
  refine ⟨53215305323180098843037753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35476870215453399228691835 53215305323180098843037753)
  ·
    refine ⟨39911478992385074132278315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53215305323180098843037753 39911478992385074132278315)
    ·
      refine ⟨59867218488577611198417473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39911478992385074132278315 59867218488577611198417473)
      ·
        refine ⟨44900413866433208398813105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59867218488577611198417473 44900413866433208398813105)
        ·
          refine ⟨33675310399824906299109829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44900413866433208398813105 33675310399824906299109829)
          ·
            refine ⟨6314120699967169931083093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33675310399824906299109829 6314120699967169931083093)
            ·
              refine ⟨9249200244092534078735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 6314120699967169931083093 9249200244092534078735)
              ·
                rfl

theorem cell23_1459033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 11].length) (baseStart_1459033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459033 prefixEnd_1459033 := by exact prefixLift 1459033
  have htrace : WordTrace (prefixWord ++ tailWord_1459033) baseStart_1459033 baseEnd_1459033 := by
    simpa [prefixWord, tailWord_1459033, baseEnd_1459033] using wordTrace_append hprefix tailTrace_1459033
  have hstable : (prefixWord ++ tailWord_1459033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459033).length < 2 ^ (prefixWord ++ tailWord_1459033).sum := by decide
  have hdescent : baseEnd_1459033 < baseStart_1459033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459077 : List Nat := [1, 3, 1, 1, 3, 4, 1, 2, 1, 3, 3]
def baseStart_1459077 : Nat := 118140960795 + 1459077 * 2 ^ 59
def prefixEnd_1459077 : Nat := 4983230072969 + 3 ^ 40 * 1459077 * 2
def baseEnd_1459077 : Nat := 749207812920293088227333

theorem tailTrace_1459077 : CollatzResearch.WordTrace tailWord_1459077 prefixEnd_1459077 749207812920293088227333 := by
  unfold tailWord_1459077
  simp only [CollatzResearch.WordTrace]
  refine ⟨53216910135020694357639485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35477940090013796238426323 53216910135020694357639485)
  ·
    refine ⟨19956341300632760384114807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53216910135020694357639485 19956341300632760384114807)
    ·
      refine ⟨29934511950949140576172211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19956341300632760384114807 29934511950949140576172211)
      ·
        refine ⟨44901767926423710864258317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29934511950949140576172211 44901767926423710864258317)
        ·
          refine ⟨16838162972408891574096869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44901767926423710864258317 16838162972408891574096869)
          ·
            refine ⟨3157155557326667170143163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16838162972408891574096869 3157155557326667170143163)
            ·
              refine ⟨4735733335990000755214745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3157155557326667170143163 4735733335990000755214745)
              ·
                refine ⟨3551800001992500566411059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4735733335990000755214745 3551800001992500566411059)
                ·
                  refine ⟨5327700002988750849616589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3551800001992500566411059 5327700002988750849616589)
                  ·
                    refine ⟨1997887501120781568606221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5327700002988750849616589 1997887501120781568606221)
                    ·
                      refine ⟨749207812920293088227333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1997887501120781568606221 749207812920293088227333)
                      ·
                        rfl

theorem cell23_1459077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 4, 1, 2, 1, 3, 3].length) (baseStart_1459077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459077 prefixEnd_1459077 := by exact prefixLift 1459077
  have htrace : WordTrace (prefixWord ++ tailWord_1459077) baseStart_1459077 baseEnd_1459077 := by
    simpa [prefixWord, tailWord_1459077, baseEnd_1459077] using wordTrace_append hprefix tailTrace_1459077
  have hstable : (prefixWord ++ tailWord_1459077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459077).length < 2 ^ (prefixWord ++ tailWord_1459077).sum := by decide
  have hdescent : baseEnd_1459077 < baseStart_1459077 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459130 : List Nat := [3, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4]
def baseStart_1459130 : Nat := 118140960795 + 1459130 * 2 ^ 59
def prefixEnd_1459130 : Nat := 4983230072969 + 3 ^ 40 * 1459130 * 2
def baseEnd_1459130 : Nat := 749235027394981380864589

theorem tailTrace_1459130 : CollatzResearch.WordTrace tailWord_1459130 prefixEnd_1459130 749235027394981380864589 := by
  unfold tailWord_1459130
  simp only [CollatzResearch.WordTrace]
  refine ⟨13304710800957171102329711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35479228802552456272879229 13304710800957171102329711)
  ·
    refine ⟨19957066201435756653494567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13304710800957171102329711 19957066201435756653494567)
    ·
      refine ⟨29935599302153634980241851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19957066201435756653494567 29935599302153634980241851)
      ·
        refine ⟨44903398953230452470362777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29935599302153634980241851 44903398953230452470362777)
        ·
          refine ⟨33677549214922839352772083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44903398953230452470362777 33677549214922839352772083)
          ·
            refine ⟨50516323822384259029158125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33677549214922839352772083 50516323822384259029158125)
            ·
              refine ⟨18943621433394097135934297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50516323822384259029158125 18943621433394097135934297)
              ·
                refine ⟨14207716075045572851950723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18943621433394097135934297 14207716075045572851950723)
                ·
                  refine ⟨21311574112568359277926085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14207716075045572851950723 21311574112568359277926085)
                  ·
                    refine ⟨3995920146106567364611141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21311574112568359277926085 3995920146106567364611141)
                    ·
                      refine ⟨749235027394981380864589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3995920146106567364611141 749235027394981380864589)
                      ·
                        rfl

theorem cell23_1459130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 2, 1, 4, 4].length) (baseStart_1459130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459130 prefixEnd_1459130 := by exact prefixLift 1459130
  have htrace : WordTrace (prefixWord ++ tailWord_1459130) baseStart_1459130 baseEnd_1459130 := by
    simpa [prefixWord, tailWord_1459130, baseEnd_1459130] using wordTrace_append hprefix tailTrace_1459130
  have hstable : (prefixWord ++ tailWord_1459130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459130).length < 2 ^ (prefixWord ++ tailWord_1459130).sum := by decide
  have hdescent : baseEnd_1459130 < baseStart_1459130 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459134 : List Nat := [4, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2]
def baseStart_1459134 : Nat := 118140960795 + 1459134 * 2 ^ 59
def prefixEnd_1459134 : Nat := 4983230072969 + 3 ^ 40 * 1459134 * 2
def baseEnd_1459134 : Nat := 749237081317599365214571

theorem tailTrace_1459134 : CollatzResearch.WordTrace tailWord_1459134 prefixEnd_1459134 749237081317599365214571 := by
  unfold tailWord_1459134
  simp only [CollatzResearch.WordTrace]
  refine ⟨6652373636976774136558057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35479326063876128728309637 6652373636976774136558057)
  ·
    refine ⟨4989280227732580602418543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6652373636976774136558057 4989280227732580602418543)
    ·
      refine ⟨7483920341598870903627815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4989280227732580602418543 7483920341598870903627815)
      ·
        refine ⟨11225880512398306355441723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7483920341598870903627815 11225880512398306355441723)
        ·
          refine ⟨16838820768597459533162585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11225880512398306355441723 16838820768597459533162585)
          ·
            refine ⟨12629115576448094649871939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16838820768597459533162585 12629115576448094649871939)
            ·
              refine ⟨18943673364672141974807909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12629115576448094649871939 18943673364672141974807909)
              ·
                refine ⟨3551938755876026620276483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18943673364672141974807909 3551938755876026620276483)
                ·
                  refine ⟨5327908133814039930414725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3551938755876026620276483 5327908133814039930414725)
                  ·
                    refine ⟨998982775090132486952761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5327908133814039930414725 998982775090132486952761)
                    ·
                      refine ⟨749237081317599365214571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 998982775090132486952761 749237081317599365214571)
                      ·
                        rfl

theorem cell23_1459134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 1, 4, 2].length) (baseStart_1459134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459134 prefixEnd_1459134 := by exact prefixLift 1459134
  have htrace : WordTrace (prefixWord ++ tailWord_1459134) baseStart_1459134 baseEnd_1459134 := by
    simpa [prefixWord, tailWord_1459134, baseEnd_1459134] using wordTrace_append hprefix tailTrace_1459134
  have hstable : (prefixWord ++ tailWord_1459134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459134).length < 2 ^ (prefixWord ++ tailWord_1459134).sum := by decide
  have hdescent : baseEnd_1459134 < baseStart_1459134 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459151 : List Nat := [1, 1, 2, 1, 1, 6, 3, 2, 2, 2, 2]
def baseStart_1459151 : Nat := 118140960795 + 1459151 * 2 ^ 59
def prefixEnd_1459151 : Nat := 4983230072969 + 3 ^ 40 * 1459151 * 2
def baseEnd_1459151 : Nat := 749245810488725798701993

theorem tailTrace_1459151 : CollatzResearch.WordTrace tailWord_1459151 prefixEnd_1459151 749245810488725798701993 := by
  unfold tailWord_1459151
  simp only [CollatzResearch.WordTrace]
  refine ⟨53219609136752604995833307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35479739424501736663888871 53219609136752604995833307)
  ·
    refine ⟨79829413705128907493749961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53219609136752604995833307 79829413705128907493749961)
    ·
      refine ⟨59872060278846680620312471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79829413705128907493749961 59872060278846680620312471)
      ·
        refine ⟨89808090418270020930468707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59872060278846680620312471 89808090418270020930468707)
        ·
          refine ⟨134712135627405031395703061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89808090418270020930468707 134712135627405031395703061)
          ·
            refine ⟨6314631357534610846673581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 134712135627405031395703061 6314631357534610846673581)
            ·
              refine ⟨2367986759075479067502593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6314631357534610846673581 2367986759075479067502593)
              ·
                refine ⟨1775990069306609300626945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2367986759075479067502593 1775990069306609300626945)
                ·
                  refine ⟨1331992551979956975470209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1775990069306609300626945 1331992551979956975470209)
                  ·
                    refine ⟨998994413984967731602657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1331992551979956975470209 998994413984967731602657)
                    ·
                      refine ⟨749245810488725798701993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 998994413984967731602657 749245810488725798701993)
                      ·
                        rfl

theorem cell23_1459151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 2, 2, 2, 2].length) (baseStart_1459151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459151 prefixEnd_1459151 := by exact prefixLift 1459151
  have htrace : WordTrace (prefixWord ++ tailWord_1459151) baseStart_1459151 baseEnd_1459151 := by
    simpa [prefixWord, tailWord_1459151, baseEnd_1459151] using wordTrace_append hprefix tailTrace_1459151
  have hstable : (prefixWord ++ tailWord_1459151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459151).length < 2 ^ (prefixWord ++ tailWord_1459151).sum := by decide
  have hdescent : baseEnd_1459151 < baseStart_1459151 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459180 : List Nat := [2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 5]
def baseStart_1459180 : Nat := 118140960795 + 1459180 * 2 ^ 59
def prefixEnd_1459180 : Nat := 4983230072969 + 3 ^ 40 * 1459180 * 2
def baseEnd_1459180 : Nat := 749260701427706185239359

theorem tailTrace_1459180 : CollatzResearch.WordTrace tailWord_1459180 prefixEnd_1459180 749260701427706185239359 := by
  unfold tailWord_1459180
  simp only [CollatzResearch.WordTrace]
  refine ⟨26610333426823771474319497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35480444569098361965759329 26610333426823771474319497)
  ·
    refine ⟨19957750070117828605739623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26610333426823771474319497 19957750070117828605739623)
    ·
      refine ⟨29936625105176742908609435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19957750070117828605739623 29936625105176742908609435)
      ·
        refine ⟨44904937657765114362914153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29936625105176742908609435 44904937657765114362914153)
        ·
          refine ⟨33678703243323835772185615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44904937657765114362914153 33678703243323835772185615)
          ·
            refine ⟨50518054864985753658278423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33678703243323835772185615 50518054864985753658278423)
            ·
              refine ⟨75777082297478630487417635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50518054864985753658278423 75777082297478630487417635)
              ·
                refine ⟨113665623446217945731126453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75777082297478630487417635 113665623446217945731126453)
                ·
                  refine ⟨10656152198082932412293105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 113665623446217945731126453 10656152198082932412293105)
                  ·
                    refine ⟨7992114148562199309219829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10656152198082932412293105 7992114148562199309219829)
                    ·
                      refine ⟨749260701427706185239359, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7992114148562199309219829 749260701427706185239359)
                      ·
                        rfl

theorem cell23_1459180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 5].length) (baseStart_1459180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459180 prefixEnd_1459180 := by exact prefixLift 1459180
  have htrace : WordTrace (prefixWord ++ tailWord_1459180) baseStart_1459180 baseEnd_1459180 := by
    simpa [prefixWord, tailWord_1459180, baseEnd_1459180] using wordTrace_append hprefix tailTrace_1459180
  have hstable : (prefixWord ++ tailWord_1459180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459180).length < 2 ^ (prefixWord ++ tailWord_1459180).sum := by decide
  have hdescent : baseEnd_1459180 < baseStart_1459180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459244 : List Nat := [2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 3]
def baseStart_1459244 : Nat := 118140960795 + 1459244 * 2 ^ 59
def prefixEnd_1459244 : Nat := 4983230072969 + 3 ^ 40 * 1459244 * 2
def baseEnd_1459244 : Nat := 749293564189593934839065

theorem tailTrace_1459244 : CollatzResearch.WordTrace tailWord_1459244 prefixEnd_1459244 749293564189593934839065 := by
  unfold tailWord_1459244
  simp only [CollatzResearch.WordTrace]
  refine ⟨26611500562707840939484393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35482000750277121252645857 26611500562707840939484393)
  ·
    refine ⟨19958625422030880704613295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26611500562707840939484393 19958625422030880704613295)
    ·
      refine ⟨29937938133046321056919943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19958625422030880704613295 29937938133046321056919943)
      ·
        refine ⟨44906907199569481585379915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29937938133046321056919943 44906907199569481585379915)
        ·
          refine ⟨67360360799354222378069873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44906907199569481585379915 67360360799354222378069873)
          ·
            refine ⟨50520270599515666783552405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67360360799354222378069873 50520270599515666783552405)
            ·
              refine ⟨2368137684352296880479019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 50520270599515666783552405 2368137684352296880479019)
              ·
                refine ⟨3552206526528445320718529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2368137684352296880479019 3552206526528445320718529)
                ·
                  refine ⟨2664154894896333990538897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3552206526528445320718529 2664154894896333990538897)
                  ·
                    refine ⟨1998116171172250492904173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2664154894896333990538897 1998116171172250492904173)
                    ·
                      refine ⟨749293564189593934839065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1998116171172250492904173 749293564189593934839065)
                      ·
                        rfl

theorem cell23_1459244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 2, 3].length) (baseStart_1459244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459244 prefixEnd_1459244 := by exact prefixLift 1459244
  have htrace : WordTrace (prefixWord ++ tailWord_1459244) baseStart_1459244 baseEnd_1459244 := by
    simpa [prefixWord, tailWord_1459244, baseEnd_1459244] using wordTrace_append hprefix tailTrace_1459244
  have hstable : (prefixWord ++ tailWord_1459244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459244).length < 2 ^ (prefixWord ++ tailWord_1459244).sum := by decide
  have hdescent : baseEnd_1459244 < baseStart_1459244 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459308 : List Nat := [2, 2, 1, 1, 3, 2, 4, 3, 1, 1, 3]
def baseStart_1459308 : Nat := 118140960795 + 1459308 * 2 ^ 59
def prefixEnd_1459308 : Nat := 4983230072969 + 3 ^ 40 * 1459308 * 2
def baseEnd_1459308 : Nat := 749326426951481684438771

theorem tailTrace_1459308 : CollatzResearch.WordTrace tailWord_1459308 prefixEnd_1459308 749326426951481684438771 := by
  unfold tailWord_1459308
  simp only [CollatzResearch.WordTrace]
  refine ⟨26612667698591910404649289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35483556931455880539532385 26612667698591910404649289)
  ·
    refine ⟨19959500773943932803486967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26612667698591910404649289 19959500773943932803486967)
    ·
      refine ⟨29939251160915899205230451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19959500773943932803486967 29939251160915899205230451)
      ·
        refine ⟨44908876741373848807845677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29939251160915899205230451 44908876741373848807845677)
        ·
          refine ⟨16840828778015193302942129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 44908876741373848807845677 16840828778015193302942129)
          ·
            refine ⟨12630621583511394977206597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16840828778015193302942129 12630621583511394977206597)
            ·
              refine ⟨2368241546908386558226237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12630621583511394977206597 2368241546908386558226237)
              ·
                refine ⟨888090580090644959334839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2368241546908386558226237 888090580090644959334839)
                ·
                  refine ⟨1332135870135967439002259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 888090580090644959334839 1332135870135967439002259)
                  ·
                    refine ⟨1998203805203951158503389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1332135870135967439002259 1998203805203951158503389)
                    ·
                      refine ⟨749326426951481684438771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1998203805203951158503389 749326426951481684438771)
                      ·
                        rfl

theorem cell23_1459308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 3, 1, 1, 3].length) (baseStart_1459308 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459308 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459308 prefixEnd_1459308 := by exact prefixLift 1459308
  have htrace : WordTrace (prefixWord ++ tailWord_1459308) baseStart_1459308 baseEnd_1459308 := by
    simpa [prefixWord, tailWord_1459308, baseEnd_1459308] using wordTrace_append hprefix tailTrace_1459308
  have hstable : (prefixWord ++ tailWord_1459308).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459308).length < 2 ^ (prefixWord ++ tailWord_1459308).sum := by decide
  have hdescent : baseEnd_1459308 < baseStart_1459308 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459324 : List Nat := [2, 2, 2, 1, 1, 3, 3, 1, 4, 4]
def baseStart_1459324 : Nat := 118140960795 + 1459324 * 2 ^ 59
def prefixEnd_1459324 : Nat := 4983230072969 + 3 ^ 40 * 1459324 * 2
def baseEnd_1459324 : Nat := 249778214213984540612899

theorem tailTrace_1459324 : CollatzResearch.WordTrace tailWord_1459324 prefixEnd_1459324 249778214213984540612899 := by
  unfold tailWord_1459324
  simp only [CollatzResearch.WordTrace]
  refine ⟨26612959482562927770940513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35483945976750570361254017 26612959482562927770940513)
  ·
    refine ⟨19959719611922195828205385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26612959482562927770940513 19959719611922195828205385)
    ·
      refine ⟨14969789708941646871154039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19959719611922195828205385 14969789708941646871154039)
      ·
        refine ⟨22454684563412470306731059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14969789708941646871154039 22454684563412470306731059)
        ·
          refine ⟨33682026845118705460096589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22454684563412470306731059 33682026845118705460096589)
          ·
            refine ⟨12630760066919514547536221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33682026845118705460096589 12630760066919514547536221)
            ·
              refine ⟨4736535025094817955326083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12630760066919514547536221 4736535025094817955326083)
              ·
                refine ⟨7104802537642226932989125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4736535025094817955326083 7104802537642226932989125)
                ·
                  refine ⟨1332150475807917549935461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7104802537642226932989125 1332150475807917549935461)
                  ·
                    refine ⟨249778214213984540612899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1332150475807917549935461 249778214213984540612899)
                    ·
                      rfl

theorem cell23_1459324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 3, 1, 4, 4].length) (baseStart_1459324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459324 prefixEnd_1459324 := by exact prefixLift 1459324
  have htrace : WordTrace (prefixWord ++ tailWord_1459324) baseStart_1459324 baseEnd_1459324 := by
    simpa [prefixWord, tailWord_1459324, baseEnd_1459324] using wordTrace_append hprefix tailTrace_1459324
  have hstable : (prefixWord ++ tailWord_1459324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459324).length < 2 ^ (prefixWord ++ tailWord_1459324).sum := by decide
  have hdescent : baseEnd_1459324 < baseStart_1459324 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459351 : List Nat := [1, 1, 3, 3, 3, 1, 1, 4, 1, 2, 3]
def baseStart_1459351 : Nat := 118140960795 + 1459351 * 2 ^ 59
def prefixEnd_1459351 : Nat := 4983230072969 + 3 ^ 40 * 1459351 * 2
def baseEnd_1459351 : Nat := 749348506619625016201073

theorem tailTrace_1459351 : CollatzResearch.WordTrace tailWord_1459351 prefixEnd_1459351 749348506619625016201073 := by
  unfold tailWord_1459351
  simp only [CollatzResearch.WordTrace]
  refine ⟨53226903736028039153113907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35484602490685359435409271 53226903736028039153113907)
  ·
    refine ⟨79840355604042058729670861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53226903736028039153113907 79840355604042058729670861)
    ·
      refine ⟨29940133351515772023626573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 79840355604042058729670861 29940133351515772023626573)
      ·
        refine ⟨11227550006818414508859965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29940133351515772023626573 11227550006818414508859965)
        ·
          refine ⟨4210331252556905440822487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11227550006818414508859965 4210331252556905440822487)
          ·
            refine ⟨6315496878835358161233731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4210331252556905440822487 6315496878835358161233731)
            ·
              refine ⟨9473245318253037241850597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6315496878835358161233731 9473245318253037241850597)
              ·
                refine ⟨1776233497172444482846987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9473245318253037241850597 1776233497172444482846987)
                ·
                  refine ⟨2664350245758666724270481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1776233497172444482846987 2664350245758666724270481)
                  ·
                    refine ⟨1998262684319000043202861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2664350245758666724270481 1998262684319000043202861)
                    ·
                      refine ⟨749348506619625016201073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1998262684319000043202861 749348506619625016201073)
                      ·
                        rfl

theorem cell23_1459351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_1459351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459351 prefixEnd_1459351 := by exact prefixLift 1459351
  have htrace : WordTrace (prefixWord ++ tailWord_1459351) baseStart_1459351 baseEnd_1459351 := by
    simpa [prefixWord, tailWord_1459351, baseEnd_1459351] using wordTrace_append hprefix tailTrace_1459351
  have hstable : (prefixWord ++ tailWord_1459351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459351).length < 2 ^ (prefixWord ++ tailWord_1459351).sum := by decide
  have hdescent : baseEnd_1459351 < baseStart_1459351 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459354 : List Nat := [3, 1, 1, 5, 1, 2, 1, 9]
def baseStart_1459354 : Nat := 118140960795 + 1459354 * 2 ^ 59
def prefixEnd_1459354 : Nat := 4983230072969 + 3 ^ 40 * 1459354 * 2
def baseEnd_1459354 : Nat := 27753705446725500165317

theorem tailTrace_1459354 : CollatzResearch.WordTrace tailWord_1459354 prefixEnd_1459354 27753705446725500165317 := by
  unfold tailWord_1459354
  simp only [CollatzResearch.WordTrace]
  refine ⟨13306753288754292666368279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35484675436678113776982077 13306753288754292666368279)
  ·
    refine ⟨19960129933131438999552419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13306753288754292666368279 19960129933131438999552419)
    ·
      refine ⟨29940194899697158499328629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19960129933131438999552419 29940194899697158499328629)
      ·
        refine ⟨2806893271846608609312059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29940194899697158499328629 2806893271846608609312059)
        ·
          refine ⟨4210339907769912913968089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2806893271846608609312059 4210339907769912913968089)
          ·
            refine ⟨3157754930827434685476067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4210339907769912913968089 3157754930827434685476067)
            ·
              refine ⟨4736632396241152028214101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3157754930827434685476067 4736632396241152028214101)
              ·
                refine ⟨27753705446725500165317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4736632396241152028214101 27753705446725500165317)
                ·
                  rfl

theorem cell23_1459354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 1, 2, 1, 9].length) (baseStart_1459354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459354 prefixEnd_1459354 := by exact prefixLift 1459354
  have htrace : WordTrace (prefixWord ++ tailWord_1459354) baseStart_1459354 baseEnd_1459354 := by
    simpa [prefixWord, tailWord_1459354, baseEnd_1459354] using wordTrace_append hprefix tailTrace_1459354
  have hstable : (prefixWord ++ tailWord_1459354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459354).length < 2 ^ (prefixWord ++ tailWord_1459354).sum := by decide
  have hdescent : baseEnd_1459354 < baseStart_1459354 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459365 : List Nat := [1, 3, 1, 2, 1, 4, 3, 3, 1, 2, 2]
def baseStart_1459365 : Nat := 118140960795 + 1459365 * 2 ^ 59
def prefixEnd_1459365 : Nat := 4983230072969 + 3 ^ 40 * 1459365 * 2
def baseEnd_1459365 : Nat := 749355695348787961426009

theorem tailTrace_1459365 : CollatzResearch.WordTrace tailWord_1459365 prefixEnd_1459365 749355695348787961426009 := by
  unfold tailWord_1459365
  simp only [CollatzResearch.WordTrace]
  refine ⟨53227414357977319544123549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35484942905318213029415699 53227414357977319544123549)
  ·
    refine ⟨19960280384241494829046331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53227414357977319544123549 19960280384241494829046331)
    ·
      refine ⟨29940420576362242243569497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19960280384241494829046331 29940420576362242243569497)
      ·
        refine ⟨22455315432271681682677123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29940420576362242243569497 22455315432271681682677123)
        ·
          refine ⟨33682973148407522524015685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22455315432271681682677123 33682973148407522524015685)
          ·
            refine ⟨6315557465326410473252941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33682973148407522524015685 6315557465326410473252941)
            ·
              refine ⟨2368334049497403927469853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6315557465326410473252941 2368334049497403927469853)
              ·
                refine ⟨888125268561526472801195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2368334049497403927469853 888125268561526472801195)
                ·
                  refine ⟨1332187902842289709201793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 888125268561526472801195 1332187902842289709201793)
                  ·
                    refine ⟨999140927131717281901345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1332187902842289709201793 999140927131717281901345)
                    ·
                      refine ⟨749355695348787961426009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 999140927131717281901345 749355695348787961426009)
                      ·
                        rfl

theorem cell23_1459365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 3, 1, 2, 2].length) (baseStart_1459365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459365 prefixEnd_1459365 := by exact prefixLift 1459365
  have htrace : WordTrace (prefixWord ++ tailWord_1459365) baseStart_1459365 baseEnd_1459365 := by
    simpa [prefixWord, tailWord_1459365, baseEnd_1459365] using wordTrace_append hprefix tailTrace_1459365
  have hstable : (prefixWord ++ tailWord_1459365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459365).length < 2 ^ (prefixWord ++ tailWord_1459365).sum := by decide
  have hdescent : baseEnd_1459365 < baseStart_1459365 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459397 : List Nat := [1, 3, 1, 1, 1, 1, 3, 3, 1, 8]
def baseStart_1459397 : Nat := 118140960795 + 1459397 * 2 ^ 59
def prefixEnd_1459397 : Nat := 4983230072969 + 3 ^ 40 * 1459397 * 2
def baseEnd_1459397 : Nat := 249790708909910612075287

theorem tailTrace_1459397 : CollatzResearch.WordTrace tailWord_1459397 prefixEnd_1459397 249790708909910612075287 := by
  unfold tailWord_1459397
  simp only [CollatzResearch.WordTrace]
  refine ⟨53228581493861389009288445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35485720995907592672858963 53228581493861389009288445)
  ·
    refine ⟨19960718060198020878483167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53228581493861389009288445 19960718060198020878483167)
    ·
      refine ⟨29941077090297031317724751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19960718060198020878483167 29941077090297031317724751)
      ·
        refine ⟨44911615635445546976587127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29941077090297031317724751 44911615635445546976587127)
        ·
          refine ⟨67367423453168320464880691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44911615635445546976587127 67367423453168320464880691)
          ·
            refine ⟨101051135179752480697321037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67367423453168320464880691 101051135179752480697321037)
            ·
              refine ⟨37894175692407180261495389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101051135179752480697321037 37894175692407180261495389)
              ·
                refine ⟨14210315884652692598060771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37894175692407180261495389 14210315884652692598060771)
                ·
                  refine ⟨21315473826979038897091157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14210315884652692598060771 21315473826979038897091157)
                  ·
                    refine ⟨249790708909910612075287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21315473826979038897091157 249790708909910612075287)
                    ·
                      rfl

theorem cell23_1459397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 3, 1, 8].length) (baseStart_1459397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459397 prefixEnd_1459397 := by exact prefixLift 1459397
  have htrace : WordTrace (prefixWord ++ tailWord_1459397) baseStart_1459397 baseEnd_1459397 := by
    simpa [prefixWord, tailWord_1459397, baseEnd_1459397] using wordTrace_append hprefix tailTrace_1459397
  have hstable : (prefixWord ++ tailWord_1459397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459397).length < 2 ^ (prefixWord ++ tailWord_1459397).sum := by decide
  have hdescent : baseEnd_1459397 < baseStart_1459397 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459424 : List Nat := [2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 5]
def baseStart_1459424 : Nat := 118140960795 + 1459424 * 2 ^ 59
def prefixEnd_1459424 : Nat := 4983230072969 + 3 ^ 40 * 1459424 * 2
def baseEnd_1459424 : Nat := 749385990707403230588237

theorem tailTrace_1459424 : CollatzResearch.WordTrace tailWord_1459424 prefixEnd_1459424 749385990707403230588237 := by
  unfold tailWord_1459424
  simp only [CollatzResearch.WordTrace]
  refine ⟨26614783132381786310260663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35486377509842381747014217 26614783132381786310260663)
  ·
    refine ⟨39922174698572679465390995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26614783132381786310260663 39922174698572679465390995)
    ·
      refine ⟨59883262047859019198086493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39922174698572679465390995 59883262047859019198086493)
      ·
        refine ⟨22456223267947132199282435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59883262047859019198086493 22456223267947132199282435)
        ·
          refine ⟨33684334901920698298923653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22456223267947132199282435 33684334901920698298923653)
          ·
            refine ⟨6315812794110130931048185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33684334901920698298923653 6315812794110130931048185)
            ·
              refine ⟨4736859595582598198286139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6315812794110130931048185 4736859595582598198286139)
              ·
                refine ⟨7105289393373897297429209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4736859595582598198286139 7105289393373897297429209)
                ·
                  refine ⟨5328967045030422973071907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7105289393373897297429209 5328967045030422973071907)
                  ·
                    refine ⟨7993450567545634459607861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5328967045030422973071907 7993450567545634459607861)
                    ·
                      refine ⟨749385990707403230588237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7993450567545634459607861 749385990707403230588237)
                      ·
                        rfl

theorem cell23_1459424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 5].length) (baseStart_1459424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459424 prefixEnd_1459424 := by exact prefixLift 1459424
  have htrace : WordTrace (prefixWord ++ tailWord_1459424) baseStart_1459424 baseEnd_1459424 := by
    simpa [prefixWord, tailWord_1459424, baseEnd_1459424] using wordTrace_append hprefix tailTrace_1459424
  have hstable : (prefixWord ++ tailWord_1459424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459424).length < 2 ^ (prefixWord ++ tailWord_1459424).sum := by decide
  have hdescent : baseEnd_1459424 < baseStart_1459424 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459425 : List Nat := [1, 2, 3, 1, 3, 3, 3, 1, 1, 3, 2]
def baseStart_1459425 : Nat := 118140960795 + 1459425 * 2 ^ 59
def prefixEnd_1459425 : Nat := 4983230072969 + 3 ^ 40 * 1459425 * 2
def baseEnd_1459425 : Nat := 749386504188057726675733

theorem tailTrace_1459425 : CollatzResearch.WordTrace tailWord_1459425 prefixEnd_1459425 749386504188057726675733 := by
  unfold tailWord_1459425
  simp only [CollatzResearch.WordTrace]
  refine ⟨53229602737759949791307729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35486401825173299860871819 53229602737759949791307729)
  ·
    refine ⟨39922202053319962343480797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53229602737759949791307729 39922202053319962343480797)
    ·
      refine ⟨14970825769994985878805299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39922202053319962343480797 14970825769994985878805299)
      ·
        refine ⟨22456238654992478818207949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14970825769994985878805299 22456238654992478818207949)
        ·
          refine ⟨8421089495622179556827981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22456238654992478818207949 8421089495622179556827981)
          ·
            refine ⟨3157908560858317333810493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8421089495622179556827981 3157908560858317333810493)
            ·
              refine ⟨1184215710321869000178935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3157908560858317333810493 1184215710321869000178935)
              ·
                refine ⟨1776323565482803500268403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1184215710321869000178935 1776323565482803500268403)
                ·
                  refine ⟨2664485348224205250402605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1776323565482803500268403 2664485348224205250402605)
                  ·
                    refine ⟨999182005584076968900977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2664485348224205250402605 999182005584076968900977)
                    ·
                      refine ⟨749386504188057726675733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 999182005584076968900977 749386504188057726675733)
                      ·
                        rfl

theorem cell23_1459425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 3, 1, 1, 3, 2].length) (baseStart_1459425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459425 prefixEnd_1459425 := by exact prefixLift 1459425
  have htrace : WordTrace (prefixWord ++ tailWord_1459425) baseStart_1459425 baseEnd_1459425 := by
    simpa [prefixWord, tailWord_1459425, baseEnd_1459425] using wordTrace_append hprefix tailTrace_1459425
  have hstable : (prefixWord ++ tailWord_1459425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459425).length < 2 ^ (prefixWord ++ tailWord_1459425).sum := by decide
  have hdescent : baseEnd_1459425 < baseStart_1459425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459438 : List Nat := [4, 1, 2, 1, 1, 1, 2, 3, 4, 2, 2]
def baseStart_1459438 : Nat := 118140960795 + 1459438 * 2 ^ 59
def prefixEnd_1459438 : Nat := 4983230072969 + 3 ^ 40 * 1459438 * 2
def baseEnd_1459438 : Nat := 749393179436566175813173

theorem tailTrace_1459438 : CollatzResearch.WordTrace tailWord_1459438 prefixEnd_1459438 749393179436566175813173 := by
  unfold tailWord_1459438
  simp only [CollatzResearch.WordTrace]
  refine ⟨6653759610839106626441371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35486717924475235341020645 6653759610839106626441371)
  ·
    refine ⟨9980639416258659939662057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6653759610839106626441371 9980639416258659939662057)
    ·
      refine ⟨7485479562193994954746543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9980639416258659939662057 7485479562193994954746543)
      ·
        refine ⟨11228219343290992432119815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7485479562193994954746543 11228219343290992432119815)
        ·
          refine ⟨16842329014936488648179723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11228219343290992432119815 16842329014936488648179723)
          ·
            refine ⟨25263493522404732972269585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16842329014936488648179723 25263493522404732972269585)
            ·
              refine ⟨18947620141803549729202189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25263493522404732972269585 18947620141803549729202189)
              ·
                refine ⟨7105357553176331148450821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18947620141803549729202189 7105357553176331148450821)
                ·
                  refine ⟨1332254541220562090334529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7105357553176331148450821 1332254541220562090334529)
                  ·
                    refine ⟨999190905915421567750897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1332254541220562090334529 999190905915421567750897)
                    ·
                      refine ⟨749393179436566175813173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 999190905915421567750897 749393179436566175813173)
                      ·
                        rfl

theorem cell23_1459438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 2, 3, 4, 2, 2].length) (baseStart_1459438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459438 prefixEnd_1459438 := by exact prefixLift 1459438
  have htrace : WordTrace (prefixWord ++ tailWord_1459438) baseStart_1459438 baseEnd_1459438 := by
    simpa [prefixWord, tailWord_1459438, baseEnd_1459438] using wordTrace_append hprefix tailTrace_1459438
  have hstable : (prefixWord ++ tailWord_1459438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459438).length < 2 ^ (prefixWord ++ tailWord_1459438).sum := by decide
  have hdescent : baseEnd_1459438 < baseStart_1459438 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459484 : List Nat := [2, 2, 3, 1, 1, 1, 2, 1, 3, 2, 5]
def baseStart_1459484 : Nat := 118140960795 + 1459484 * 2 ^ 59
def prefixEnd_1459484 : Nat := 4983230072969 + 3 ^ 40 * 1459484 * 2
def baseEnd_1459484 : Nat := 749416799546672995837961

theorem tailTrace_1459484 : CollatzResearch.WordTrace tailWord_1459484 prefixEnd_1459484 749416799546672995837961 := by
  unfold tailWord_1459484
  simp only [CollatzResearch.WordTrace]
  refine ⟨26615877322273101433852753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35487836429697468578470337 26615877322273101433852753)
  ·
    refine ⟨19961907991704826075389565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26615877322273101433852753 19961907991704826075389565)
    ·
      refine ⟨7485715496889309778271087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19961907991704826075389565 7485715496889309778271087)
      ·
        refine ⟨11228573245333964667406631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7485715496889309778271087 11228573245333964667406631)
        ·
          refine ⟨16842859868000947001109947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11228573245333964667406631 16842859868000947001109947)
          ·
            refine ⟨25264289802001420501664921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16842859868000947001109947 25264289802001420501664921)
            ·
              refine ⟨18948217351501065376248691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25264289802001420501664921 18948217351501065376248691)
              ·
                refine ⟨28422326027251598064373037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18948217351501065376248691 28422326027251598064373037)
                ·
                  refine ⟨10658372260219349274139889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28422326027251598064373037 10658372260219349274139889)
                  ·
                    refine ⟨7993779195164511955604917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10658372260219349274139889 7993779195164511955604917)
                    ·
                      refine ⟨749416799546672995837961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7993779195164511955604917 749416799546672995837961)
                      ·
                        rfl

theorem cell23_1459484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 1, 3, 2, 5].length) (baseStart_1459484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459484 prefixEnd_1459484 := by exact prefixLift 1459484
  have htrace : WordTrace (prefixWord ++ tailWord_1459484) baseStart_1459484 baseEnd_1459484 := by
    simpa [prefixWord, tailWord_1459484, baseEnd_1459484] using wordTrace_append hprefix tailTrace_1459484
  have hstable : (prefixWord ++ tailWord_1459484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459484).length < 2 ^ (prefixWord ++ tailWord_1459484).sum := by decide
  have hdescent : baseEnd_1459484 < baseStart_1459484 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459534 : List Nat := [4, 1, 1, 1, 1, 1, 3, 1, 10]
def baseStart_1459534 : Nat := 118140960795 + 1459534 * 2 ^ 59
def prefixEnd_1459534 : Nat := 4983230072969 + 3 ^ 40 * 1459534 * 2
def baseEnd_1459534 : Nat := 83271385953266422245859

theorem tailTrace_1459534 : CollatzResearch.WordTrace tailWord_1459534 prefixEnd_1459534 83271385953266422245859 := by
  unfold tailWord_1459534
  simp only [CollatzResearch.WordTrace]
  refine ⟨6654197286795632675878207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35489052196243374271350437 6654197286795632675878207)
  ·
    refine ⟨9981295930193449013817311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6654197286795632675878207 9981295930193449013817311)
    ·
      refine ⟨14971943895290173520725967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9981295930193449013817311 14971943895290173520725967)
      ·
        refine ⟨22457915842935260281088951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14971943895290173520725967 22457915842935260281088951)
        ·
          refine ⟨33686873764402890421633427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22457915842935260281088951 33686873764402890421633427)
          ·
            refine ⟨50530310646604335632450141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33686873764402890421633427 50530310646604335632450141)
            ·
              refine ⟨18948866492476625862168803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50530310646604335632450141 18948866492476625862168803)
              ·
                refine ⟨28423299738714938793253205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18948866492476625862168803 28423299738714938793253205)
                ·
                  refine ⟨83271385953266422245859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 28423299738714938793253205 83271385953266422245859)
                  ·
                    rfl

theorem cell23_1459534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 1, 10].length) (baseStart_1459534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459534 prefixEnd_1459534 := by exact prefixLift 1459534
  have htrace : WordTrace (prefixWord ++ tailWord_1459534) baseStart_1459534 baseEnd_1459534 := by
    simpa [prefixWord, tailWord_1459534, baseEnd_1459534] using wordTrace_append hprefix tailTrace_1459534
  have hstable : (prefixWord ++ tailWord_1459534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459534).length < 2 ^ (prefixWord ++ tailWord_1459534).sum := by decide
  have hdescent : baseEnd_1459534 < baseStart_1459534 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459581 : List Nat := [1, 4, 1, 1, 2, 2, 3, 1, 3, 5]
def baseStart_1459581 : Nat := 118140960795 + 1459581 * 2 ^ 59
def prefixEnd_1459581 : Nat := 4983230072969 + 3 ^ 40 * 1459581 * 2
def baseEnd_1459581 : Nat := 249822202390053038775005

theorem tailTrace_1459581 : CollatzResearch.WordTrace tailWord_1459581 prefixEnd_1459581 249822202390053038775005 := by
  unfold tailWord_1459581
  simp only [CollatzResearch.WordTrace]
  refine ⟨53235292525194788433986597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35490195016796525622657731 53235292525194788433986597)
  ·
    refine ⟨9981617348474022831372487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53235292525194788433986597 9981617348474022831372487)
    ·
      refine ⟨14972426022711034247058731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9981617348474022831372487 14972426022711034247058731)
      ·
        refine ⟨22458639034066551370588097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14972426022711034247058731 22458639034066551370588097)
        ·
          refine ⟨16843979275549913527941073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22458639034066551370588097 16843979275549913527941073)
          ·
            refine ⟨12632984456662435145955805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16843979275549913527941073 12632984456662435145955805)
            ·
              refine ⟨4737369171248413179733427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12632984456662435145955805 4737369171248413179733427)
              ·
                refine ⟨7106053756872619769600141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4737369171248413179733427 7106053756872619769600141)
                ·
                  refine ⟨2664770158827232413600053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7106053756872619769600141 2664770158827232413600053)
                  ·
                    refine ⟨249822202390053038775005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2664770158827232413600053 249822202390053038775005)
                    ·
                      rfl

theorem cell23_1459581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 3, 1, 3, 5].length) (baseStart_1459581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459581 prefixEnd_1459581 := by exact prefixLift 1459581
  have htrace : WordTrace (prefixWord ++ tailWord_1459581) baseStart_1459581 baseEnd_1459581 := by
    simpa [prefixWord, tailWord_1459581, baseEnd_1459581] using wordTrace_append hprefix tailTrace_1459581
  have hstable : (prefixWord ++ tailWord_1459581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459581).length < 2 ^ (prefixWord ++ tailWord_1459581).sum := by decide
  have hdescent : baseEnd_1459581 < baseStart_1459581 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459595 : List Nat := [1, 1, 1, 1, 4, 3, 2, 5, 1, 1, 3]
def baseStart_1459595 : Nat := 118140960795 + 1459595 * 2 ^ 59
def prefixEnd_1459595 : Nat := 4983230072969 + 3 ^ 40 * 1459595 * 2
def baseEnd_1459595 : Nat := 749473795899322061549951

theorem tailTrace_1459595 : CollatzResearch.WordTrace tailWord_1459595 prefixEnd_1459595 749473795899322061549951 := by
  unfold tailWord_1459595
  simp only [CollatzResearch.WordTrace]
  refine ⟨53235803147144068824996239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35490535431429379216664159 53235803147144068824996239)
  ·
    refine ⟨79853704720716103237494359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53235803147144068824996239 79853704720716103237494359)
    ·
      refine ⟨119780557081074154856241539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79853704720716103237494359 119780557081074154856241539)
      ·
        refine ⟨179670835621611232284362309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 119780557081074154856241539 179670835621611232284362309)
        ·
          refine ⟨33688281679052106053317933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 179670835621611232284362309 33688281679052106053317933)
          ·
            refine ⟨12633105629644539769994225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33688281679052106053317933 12633105629644539769994225)
            ·
              refine ⟨9474829222233404827495669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12633105629644539769994225 9474829222233404827495669)
              ·
                refine ⟨888265239584381702577719, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9474829222233404827495669 888265239584381702577719)
                ·
                  refine ⟨1332397859376572553866579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 888265239584381702577719 1332397859376572553866579)
                  ·
                    refine ⟨1998596789064858830799869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1332397859376572553866579 1998596789064858830799869)
                    ·
                      refine ⟨749473795899322061549951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1998596789064858830799869 749473795899322061549951)
                      ·
                        rfl

theorem cell23_1459595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 5, 1, 1, 3].length) (baseStart_1459595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459595 prefixEnd_1459595 := by exact prefixLift 1459595
  have htrace : WordTrace (prefixWord ++ tailWord_1459595) baseStart_1459595 baseEnd_1459595 := by
    simpa [prefixWord, tailWord_1459595, baseEnd_1459595] using wordTrace_append hprefix tailTrace_1459595
  have hstable : (prefixWord ++ tailWord_1459595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459595).length < 2 ^ (prefixWord ++ tailWord_1459595).sum := by decide
  have hdescent : baseEnd_1459595 < baseStart_1459595 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459618 : List Nat := [3, 3, 1, 2, 1, 2, 1, 2, 3, 1, 4]
def baseStart_1459618 : Nat := 118140960795 + 1459618 * 2 ^ 59
def prefixEnd_1459618 : Nat := 4983230072969 + 3 ^ 40 * 1459618 * 2
def baseEnd_1459618 : Nat := 749485605954375471562345

theorem tailTrace_1459618 : CollatzResearch.WordTrace tailWord_1459618 prefixEnd_1459618 749485605954375471562345 := by
  unfold tailWord_1459618
  simp only [CollatzResearch.WordTrace]
  refine ⟨13309160506515185938270877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35491094684040495835389005 13309160506515185938270877)
  ·
    refine ⟨4990935189943194726851579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13309160506515185938270877 4990935189943194726851579)
    ·
      refine ⟨7486402784914792090277369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4990935189943194726851579 7486402784914792090277369)
      ·
        refine ⟨5614802088686094067708027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7486402784914792090277369 5614802088686094067708027)
        ·
          refine ⟨8422203133029141101562041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5614802088686094067708027 8422203133029141101562041)
          ·
            refine ⟨6316652349771855826171531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8422203133029141101562041 6316652349771855826171531)
            ·
              refine ⟨9474978524657783739257297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6316652349771855826171531 9474978524657783739257297)
              ·
                refine ⟨7106233893493337804442973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9474978524657783739257297 7106233893493337804442973)
                ·
                  refine ⟨2664837710060001676666115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7106233893493337804442973 2664837710060001676666115)
                  ·
                    refine ⟨3997256565090002514999173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2664837710060001676666115 3997256565090002514999173)
                    ·
                      refine ⟨749485605954375471562345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3997256565090002514999173 749485605954375471562345)
                      ·
                        rfl

theorem cell23_1459618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_1459618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459618 prefixEnd_1459618 := by exact prefixLift 1459618
  have htrace : WordTrace (prefixWord ++ tailWord_1459618) baseStart_1459618 baseEnd_1459618 := by
    simpa [prefixWord, tailWord_1459618, baseEnd_1459618] using wordTrace_append hprefix tailTrace_1459618
  have hstable : (prefixWord ++ tailWord_1459618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459618).length < 2 ^ (prefixWord ++ tailWord_1459618).sum := by decide
  have hdescent : baseEnd_1459618 < baseStart_1459618 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459628 : List Nat := [2, 2, 1, 1, 1, 1, 6, 3, 2, 4]
def baseStart_1459628 : Nat := 118140960795 + 1459628 * 2 ^ 59
def prefixEnd_1459628 : Nat := 4983230072969 + 3 ^ 40 * 1459628 * 2
def baseEnd_1459628 : Nat := 249830246920306810812433

theorem tailTrace_1459628 : CollatzResearch.WordTrace tailWord_1459628 prefixEnd_1459628 249830246920306810812433 := by
  unfold tailWord_1459628
  simp only [CollatzResearch.WordTrace]
  refine ⟨26618503378012257730473769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35491337837349676973965025 26618503378012257730473769)
  ·
    refine ⟨19963877533509193297855327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26618503378012257730473769 19963877533509193297855327)
    ·
      refine ⟨29945816300263789946782991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19963877533509193297855327 29945816300263789946782991)
      ·
        refine ⟨44918724450395684920174487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29945816300263789946782991 44918724450395684920174487)
        ·
          refine ⟨67378086675593527380261731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44918724450395684920174487 67378086675593527380261731)
          ·
            refine ⟨101067130013390291070392597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67378086675593527380261731 101067130013390291070392597)
            ·
              refine ⟨4737521719377669893924653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 101067130013390291070392597 4737521719377669893924653)
              ·
                refine ⟨1776570644766626210221745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4737521719377669893924653 1776570644766626210221745)
                ·
                  refine ⟨1332427983574969657666309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1776570644766626210221745 1332427983574969657666309)
                  ·
                    refine ⟨249830246920306810812433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1332427983574969657666309 249830246920306810812433)
                    ·
                      rfl

theorem cell23_1459628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 2, 4].length) (baseStart_1459628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459628 prefixEnd_1459628 := by exact prefixLift 1459628
  have htrace : WordTrace (prefixWord ++ tailWord_1459628) baseStart_1459628 baseEnd_1459628 := by
    simpa [prefixWord, tailWord_1459628, baseEnd_1459628] using wordTrace_append hprefix tailTrace_1459628
  have hstable : (prefixWord ++ tailWord_1459628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459628).length < 2 ^ (prefixWord ++ tailWord_1459628).sum := by decide
  have hdescent : baseEnd_1459628 < baseStart_1459628 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459652 : List Nat := [2, 3, 3, 2, 1, 1, 4, 1, 1, 1, 4]
def baseStart_1459652 : Nat := 118140960795 + 1459652 * 2 ^ 59
def prefixEnd_1459652 : Nat := 4983230072969 + 3 ^ 40 * 1459652 * 2
def baseEnd_1459652 : Nat := 749503064296628338537189

theorem tailTrace_1459652 : CollatzResearch.WordTrace tailWord_1459652 prefixEnd_1459652 749503064296628338537189 := by
  unfold tailWord_1459652
  simp only [CollatzResearch.WordTrace]
  refine ⟨26618941053968783779910605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35491921405291711706547473 26618941053968783779910605)
  ·
    refine ⟨9982102895238293917466477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26618941053968783779910605 9982102895238293917466477)
    ·
      refine ⟨3743288585714360219049929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9982102895238293917466477 3743288585714360219049929)
      ·
        refine ⟨2807466439285770164287447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3743288585714360219049929 2807466439285770164287447)
        ·
          refine ⟨4211199658928655246431171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2807466439285770164287447 4211199658928655246431171)
          ·
            refine ⟨6316799488392982869646757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4211199658928655246431171 6316799488392982869646757)
            ·
              refine ⟨1184399904073684288058767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6316799488392982869646757 1184399904073684288058767)
              ·
                refine ⟨1776599856110526432088151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1184399904073684288058767 1776599856110526432088151)
                ·
                  refine ⟨2664899784165789648132227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1776599856110526432088151 2664899784165789648132227)
                  ·
                    refine ⟨3997349676248684472198341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2664899784165789648132227 3997349676248684472198341)
                    ·
                      refine ⟨749503064296628338537189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3997349676248684472198341 749503064296628338537189)
                      ·
                        rfl

theorem cell23_1459652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 4, 1, 1, 1, 4].length) (baseStart_1459652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459652 prefixEnd_1459652 := by exact prefixLift 1459652
  have htrace : WordTrace (prefixWord ++ tailWord_1459652) baseStart_1459652 baseEnd_1459652 := by
    simpa [prefixWord, tailWord_1459652, baseEnd_1459652] using wordTrace_append hprefix tailTrace_1459652
  have hstable : (prefixWord ++ tailWord_1459652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459652).length < 2 ^ (prefixWord ++ tailWord_1459652).sum := by decide
  have hdescent : baseEnd_1459652 < baseStart_1459652 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459685 : List Nat := [1, 3, 1, 5, 1, 1, 3, 1, 1, 3, 3]
def baseStart_1459685 : Nat := 118140960795 + 1459685 * 2 ^ 59
def prefixEnd_1459685 : Nat := 4983230072969 + 3 ^ 40 * 1459685 * 2
def baseEnd_1459685 : Nat := 749520009158226709424537

theorem tailTrace_1459685 : CollatzResearch.WordTrace tailWord_1459685 prefixEnd_1459685 749520009158226709424537 := by
  unfold tailWord_1459685
  simp only [CollatzResearch.WordTrace]
  refine ⟨53239085716818014195772509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35492723811212009463848339 53239085716818014195772509)
  ·
    refine ⟨19964657143806755323414691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53239085716818014195772509 19964657143806755323414691)
    ·
      refine ⟨29946985715710132985122037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19964657143806755323414691 29946985715710132985122037)
      ·
        refine ⟨2807529910847824967355191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29946985715710132985122037 2807529910847824967355191)
        ·
          refine ⟨4211294866271737451032787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2807529910847824967355191 4211294866271737451032787)
          ·
            refine ⟨6316942299407606176549181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4211294866271737451032787 6316942299407606176549181)
            ·
              refine ⟨2368853362277852316205943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6316942299407606176549181 2368853362277852316205943)
              ·
                refine ⟨3553280043416778474308915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2368853362277852316205943 3553280043416778474308915)
                ·
                  refine ⟨5329920065125167711463373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3553280043416778474308915 5329920065125167711463373)
                  ·
                    refine ⟨1998720024421937891798765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5329920065125167711463373 1998720024421937891798765)
                    ·
                      refine ⟨749520009158226709424537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1998720024421937891798765 749520009158226709424537)
                      ·
                        rfl

theorem cell23_1459685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_1459685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459685 prefixEnd_1459685 := by exact prefixLift 1459685
  have htrace : WordTrace (prefixWord ++ tailWord_1459685) baseStart_1459685 baseEnd_1459685 := by
    simpa [prefixWord, tailWord_1459685, baseEnd_1459685] using wordTrace_append hprefix tailTrace_1459685
  have hstable : (prefixWord ++ tailWord_1459685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459685).length < 2 ^ (prefixWord ++ tailWord_1459685).sum := by decide
  have hdescent : baseEnd_1459685 < baseStart_1459685 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459695 : List Nat := [1, 1, 2, 1, 4, 1, 3, 4, 1, 3, 2]
def baseStart_1459695 : Nat := 118140960795 + 1459695 * 2 ^ 59
def prefixEnd_1459695 : Nat := 4983230072969 + 3 ^ 40 * 1459695 * 2
def baseEnd_1459695 : Nat := 749525143964771670299491

theorem tailTrace_1459695 : CollatzResearch.WordTrace tailWord_1459695 prefixEnd_1459695 749525143964771670299491 := by
  unfold tailWord_1459695
  simp only [CollatzResearch.WordTrace]
  refine ⟨53239450446781785903636539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35492966964521190602424359 53239450446781785903636539)
  ·
    refine ⟨79859175670172678855454809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53239450446781785903636539 79859175670172678855454809)
    ·
      refine ⟨59894381752629509141591107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79859175670172678855454809 59894381752629509141591107)
      ·
        refine ⟨89841572628944263712386661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59894381752629509141591107 89841572628944263712386661)
        ·
          refine ⟨16845294867927049446072499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89841572628944263712386661 16845294867927049446072499)
          ·
            refine ⟨25267942301890574169108749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16845294867927049446072499 25267942301890574169108749)
            ·
              refine ⟨9475478363208965313415781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25267942301890574169108749 9475478363208965313415781)
              ·
                refine ⟨1776652193101680996265459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9475478363208965313415781 1776652193101680996265459)
                ·
                  refine ⟨2664978289652521494398189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1776652193101680996265459 2664978289652521494398189)
                  ·
                    refine ⟨999366858619695560399321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2664978289652521494398189 999366858619695560399321)
                    ·
                      refine ⟨749525143964771670299491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 999366858619695560399321 749525143964771670299491)
                      ·
                        rfl

theorem cell23_1459695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 4, 1, 3, 2].length) (baseStart_1459695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459695 prefixEnd_1459695 := by exact prefixLift 1459695
  have htrace : WordTrace (prefixWord ++ tailWord_1459695) baseStart_1459695 baseEnd_1459695 := by
    simpa [prefixWord, tailWord_1459695, baseEnd_1459695] using wordTrace_append hprefix tailTrace_1459695
  have hstable : (prefixWord ++ tailWord_1459695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459695).length < 2 ^ (prefixWord ++ tailWord_1459695).sum := by decide
  have hdescent : baseEnd_1459695 < baseStart_1459695 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459698 : List Nat := [3, 2, 1, 4, 1, 1, 1, 1, 2, 2, 5]
def baseStart_1459698 : Nat := 118140960795 + 1459698 * 2 ^ 59
def prefixEnd_1459698 : Nat := 4983230072969 + 3 ^ 40 * 1459698 * 2
def baseEnd_1459698 : Nat := 749526684406735158561977

theorem tailTrace_1459698 : CollatzResearch.WordTrace tailWord_1459698 prefixEnd_1459698 749526684406735158561977 := by
  unfold tailWord_1459698
  simp only [CollatzResearch.WordTrace]
  refine ⟨13309889966442729353998937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35493039910513944943997165 13309889966442729353998937)
  ·
    refine ⟨9982417474832047015499203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13309889966442729353998937 9982417474832047015499203)
    ·
      refine ⟨14973626212248070523248805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9982417474832047015499203 14973626212248070523248805)
      ·
        refine ⟨2807554914796513223109151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14973626212248070523248805 2807554914796513223109151)
        ·
          refine ⟨4211332372194769834663727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2807554914796513223109151 4211332372194769834663727)
          ·
            refine ⟨6316998558292154751995591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4211332372194769834663727 6316998558292154751995591)
            ·
              refine ⟨9475497837438232127993387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6316998558292154751995591 9475497837438232127993387)
              ·
                refine ⟨14213246756157348191990081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9475497837438232127993387 14213246756157348191990081)
                ·
                  refine ⟨10659935067118011143992561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14213246756157348191990081 10659935067118011143992561)
                  ·
                    refine ⟨7994951300338508357994421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10659935067118011143992561 7994951300338508357994421)
                    ·
                      refine ⟨749526684406735158561977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7994951300338508357994421 749526684406735158561977)
                      ·
                        rfl

theorem cell23_1459698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_1459698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459698 prefixEnd_1459698 := by exact prefixLift 1459698
  have htrace : WordTrace (prefixWord ++ tailWord_1459698) baseStart_1459698 baseEnd_1459698 := by
    simpa [prefixWord, tailWord_1459698, baseEnd_1459698] using wordTrace_append hprefix tailTrace_1459698
  have hstable : (prefixWord ++ tailWord_1459698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459698).length < 2 ^ (prefixWord ++ tailWord_1459698).sum := by decide
  have hdescent : baseEnd_1459698 < baseStart_1459698 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459736 : List Nat := [2, 1, 2, 3, 5, 1, 2, 1, 2, 1, 3]
def baseStart_1459736 : Nat := 118140960795 + 1459736 * 2 ^ 59
def prefixEnd_1459736 : Nat := 4983230072969 + 3 ^ 40 * 1459736 * 2
def baseEnd_1459736 : Nat := 749546196671606009886803

theorem tailTrace_1459736 : CollatzResearch.WordTrace tailWord_1459736 prefixEnd_1459736 749546196671606009886803 := by
  unfold tailWord_1459736
  simp only [CollatzResearch.WordTrace]
  refine ⟨26620472919816624952939531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35493963893088833270586041 26620472919816624952939531)
  ·
    refine ⟨39930709379724937429409297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26620472919816624952939531 39930709379724937429409297)
    ·
      refine ⟨29948032034793703072056973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39930709379724937429409297 29948032034793703072056973)
      ·
        refine ⟨11230512013047638652021365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29948032034793703072056973 11230512013047638652021365)
        ·
          refine ⟨1052860501223216123627003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11230512013047638652021365 1052860501223216123627003)
          ·
            refine ⟨1579290751834824185440505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1052860501223216123627003 1579290751834824185440505)
            ·
              refine ⟨1184468063876118139080379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1579290751834824185440505 1184468063876118139080379)
              ·
                refine ⟨1776702095814177208620569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1184468063876118139080379 1776702095814177208620569)
                ·
                  refine ⟨1332526571860632906465427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1776702095814177208620569 1332526571860632906465427)
                  ·
                    refine ⟨1998789857790949359698141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1332526571860632906465427 1998789857790949359698141)
                    ·
                      refine ⟨749546196671606009886803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1998789857790949359698141 749546196671606009886803)
                      ·
                        rfl

theorem cell23_1459736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 5, 1, 2, 1, 2, 1, 3].length) (baseStart_1459736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459736 prefixEnd_1459736 := by exact prefixLift 1459736
  have htrace : WordTrace (prefixWord ++ tailWord_1459736) baseStart_1459736 baseEnd_1459736 := by
    simpa [prefixWord, tailWord_1459736, baseEnd_1459736] using wordTrace_append hprefix tailTrace_1459736
  have hstable : (prefixWord ++ tailWord_1459736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459736).length < 2 ^ (prefixWord ++ tailWord_1459736).sum := by decide
  have hdescent : baseEnd_1459736 < baseStart_1459736 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459788 : List Nat := [2, 2, 1, 3, 1, 3, 2, 1, 1, 2, 5]
def baseStart_1459788 : Nat := 118140960795 + 1459788 * 2 ^ 59
def prefixEnd_1459788 : Nat := 4983230072969 + 3 ^ 40 * 1459788 * 2
def baseEnd_1459788 : Nat := 749572897665639806436563

theorem tailTrace_1459788 : CollatzResearch.WordTrace tailWord_1459788 prefixEnd_1459788 749572897665639806436563 := by
  unfold tailWord_1459788
  simp only [CollatzResearch.WordTrace]
  refine ⟨26621421217722431393386009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35495228290296575191181345 26621421217722431393386009)
  ·
    refine ⟨19966065913291823545039507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26621421217722431393386009 19966065913291823545039507)
    ·
      refine ⟨29949098869937735317559261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19966065913291823545039507 29949098869937735317559261)
      ·
        refine ⟨11230912076226650744084723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29949098869937735317559261 11230912076226650744084723)
        ·
          refine ⟨16846368114339976116127085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11230912076226650744084723 16846368114339976116127085)
          ·
            refine ⟨6317388042877491043547657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16846368114339976116127085 6317388042877491043547657)
            ·
              refine ⟨4738041032158118282660743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6317388042877491043547657 4738041032158118282660743)
              ·
                refine ⟨7107061548237177423991115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4738041032158118282660743 7107061548237177423991115)
                ·
                  refine ⟨10660592322355766135986673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7107061548237177423991115 10660592322355766135986673)
                  ·
                    refine ⟨7995444241766824601990005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10660592322355766135986673 7995444241766824601990005)
                    ·
                      refine ⟨749572897665639806436563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7995444241766824601990005 749572897665639806436563)
                      ·
                        rfl

theorem cell23_1459788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 2, 1, 1, 2, 5].length) (baseStart_1459788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459788 prefixEnd_1459788 := by exact prefixLift 1459788
  have htrace : WordTrace (prefixWord ++ tailWord_1459788) baseStart_1459788 baseEnd_1459788 := by
    simpa [prefixWord, tailWord_1459788, baseEnd_1459788] using wordTrace_append hprefix tailTrace_1459788
  have hstable : (prefixWord ++ tailWord_1459788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459788).length < 2 ^ (prefixWord ++ tailWord_1459788).sum := by decide
  have hdescent : baseEnd_1459788 < baseStart_1459788 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459791 : List Nat := [1, 1, 2, 1, 1, 2, 3, 2, 2, 8]
def baseStart_1459791 : Nat := 118140960795 + 1459791 * 2 ^ 59
def prefixEnd_1459791 : Nat := 4983230072969 + 3 ^ 40 * 1459791 * 2
def baseEnd_1459791 : Nat := 249858146035867764899683

theorem tailTrace_1459791 : CollatzResearch.WordTrace tailWord_1459791 prefixEnd_1459791 249858146035867764899683 := by
  unfold tailWord_1459791
  simp only [CollatzResearch.WordTrace]
  refine ⟨53242951854433994299131227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35495301236289329532754151 53242951854433994299131227)
  ·
    refine ⟨79864427781650991448696841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53242951854433994299131227 79864427781650991448696841)
    ·
      refine ⟨59898320836238243586522631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79864427781650991448696841 59898320836238243586522631)
      ·
        refine ⟨89847481254357365379783947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59898320836238243586522631 89847481254357365379783947)
        ·
          refine ⟨134771221881536048069675921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89847481254357365379783947 134771221881536048069675921)
          ·
            refine ⟨101078416411152036052256941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134771221881536048069675921 101078416411152036052256941)
            ·
              refine ⟨37904406154182013519596353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101078416411152036052256941 37904406154182013519596353)
              ·
                refine ⟨28428304615636510139697265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 37904406154182013519596353 28428304615636510139697265)
                ·
                  refine ⟨21321228461727382604772949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28428304615636510139697265 21321228461727382604772949)
                  ·
                    refine ⟨249858146035867764899683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 21321228461727382604772949 249858146035867764899683)
                    ·
                      rfl

theorem cell23_1459791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 2, 2, 8].length) (baseStart_1459791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459791 prefixEnd_1459791 := by exact prefixLift 1459791
  have htrace : WordTrace (prefixWord ++ tailWord_1459791) baseStart_1459791 baseEnd_1459791 := by
    simpa [prefixWord, tailWord_1459791, baseEnd_1459791] using wordTrace_append hprefix tailTrace_1459791
  have hstable : (prefixWord ++ tailWord_1459791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459791).length < 2 ^ (prefixWord ++ tailWord_1459791).sum := by decide
  have hdescent : baseEnd_1459791 < baseStart_1459791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459815 : List Nat := [1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 4]
def baseStart_1459815 : Nat := 118140960795 + 1459815 * 2 ^ 59
def prefixEnd_1459815 : Nat := 4983230072969 + 3 ^ 40 * 1459815 * 2
def baseEnd_1459815 : Nat := 749586761643311200798939

theorem tailTrace_1459815 : CollatzResearch.WordTrace tailWord_1459815 prefixEnd_1459815 749586761643311200798939 := by
  unfold tailWord_1459815
  simp only [CollatzResearch.WordTrace]
  refine ⟨53243827206347046398004899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35495884804231364265336599 53243827206347046398004899)
  ·
    refine ⟨79865740809520569597007349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53243827206347046398004899 79865740809520569597007349)
    ·
      refine ⟨7487413200892553399719439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 79865740809520569597007349 7487413200892553399719439)
      ·
        refine ⟨11231119801338830099579159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7487413200892553399719439 11231119801338830099579159)
        ·
          refine ⟨16846679702008245149368739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11231119801338830099579159 16846679702008245149368739)
          ·
            refine ⟨25270019553012367724053109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16846679702008245149368739 25270019553012367724053109)
            ·
              refine ⟨2369064333094909474129979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 25270019553012367724053109 2369064333094909474129979)
              ·
                refine ⟨3553596499642364211194969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2369064333094909474129979 3553596499642364211194969)
                ·
                  refine ⟨2665197374731773158396227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3553596499642364211194969 2665197374731773158396227)
                  ·
                    refine ⟨3997796062097659737594341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2665197374731773158396227 3997796062097659737594341)
                    ·
                      refine ⟨749586761643311200798939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3997796062097659737594341 749586761643311200798939)
                      ·
                        rfl

theorem cell23_1459815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 5, 1, 2, 1, 4].length) (baseStart_1459815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459815 prefixEnd_1459815 := by exact prefixLift 1459815
  have htrace : WordTrace (prefixWord ++ tailWord_1459815) baseStart_1459815 baseEnd_1459815 := by
    simpa [prefixWord, tailWord_1459815, baseEnd_1459815] using wordTrace_append hprefix tailTrace_1459815
  have hstable : (prefixWord ++ tailWord_1459815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459815).length < 2 ^ (prefixWord ++ tailWord_1459815).sum := by decide
  have hdescent : baseEnd_1459815 < baseStart_1459815 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459865 : List Nat := [1, 2, 1, 2, 1, 2, 2, 3, 5, 1, 3]
def baseStart_1459865 : Nat := 118140960795 + 1459865 * 2 ^ 59
def prefixEnd_1459865 : Nat := 4983230072969 + 3 ^ 40 * 1459865 * 2
def baseEnd_1459865 : Nat := 749612435676036005173709

theorem tailTrace_1459865 : CollatzResearch.WordTrace tailWord_1459865 prefixEnd_1459865 749612435676036005173709 := by
  unfold tailWord_1459865
  simp only [CollatzResearch.WordTrace]
  refine ⟨53245650856165904937325049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35497100570777269958216699 53245650856165904937325049)
  ·
    refine ⟨39934238142124428702993787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53245650856165904937325049 39934238142124428702993787)
    ·
      refine ⟨59901357213186643054490681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39934238142124428702993787 59901357213186643054490681)
      ·
        refine ⟨44926017909889982290868011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59901357213186643054490681 44926017909889982290868011)
        ·
          refine ⟨67389026864834973436302017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44926017909889982290868011 67389026864834973436302017)
          ·
            refine ⟨50541770148626230077226513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67389026864834973436302017 50541770148626230077226513)
            ·
              refine ⟨37906327611469672557919885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50541770148626230077226513 37906327611469672557919885)
              ·
                refine ⟨14214872854301127209219957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37906327611469672557919885 14214872854301127209219957)
                ·
                  refine ⟨1332644330090730675864371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14214872854301127209219957 1332644330090730675864371)
                  ·
                    refine ⟨1998966495136096013796557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1332644330090730675864371 1998966495136096013796557)
                    ·
                      refine ⟨749612435676036005173709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1998966495136096013796557 749612435676036005173709)
                      ·
                        rfl

theorem cell23_1459865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 2, 3, 5, 1, 3].length) (baseStart_1459865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459865 prefixEnd_1459865 := by exact prefixLift 1459865
  have htrace : WordTrace (prefixWord ++ tailWord_1459865) baseStart_1459865 baseEnd_1459865 := by
    simpa [prefixWord, tailWord_1459865, baseEnd_1459865] using wordTrace_append hprefix tailTrace_1459865
  have hstable : (prefixWord ++ tailWord_1459865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459865).length < 2 ^ (prefixWord ++ tailWord_1459865).sum := by decide
  have hdescent : baseEnd_1459865 < baseStart_1459865 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459875 : List Nat := [1, 1, 1, 4, 1, 1, 3, 3, 1, 5, 2]
def baseStart_1459875 : Nat := 118140960795 + 1459875 * 2 ^ 59
def prefixEnd_1459875 : Nat := 4983230072969 + 3 ^ 40 * 1459875 * 2
def baseEnd_1459875 : Nat := 749617570482580966048663

theorem tailTrace_1459875 : CollatzResearch.WordTrace tailWord_1459875 prefixEnd_1459875 749617570482580966048663 := by
  unfold tailWord_1459875
  simp only [CollatzResearch.WordTrace]
  refine ⟨53246015586129676645189079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35497343724086451096792719 53246015586129676645189079)
  ·
    refine ⟨79869023379194514967783619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53246015586129676645189079 79869023379194514967783619)
    ·
      refine ⟨119803535068791772451675429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79869023379194514967783619 119803535068791772451675429)
      ·
        refine ⟨22463162825398457334689143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119803535068791772451675429 22463162825398457334689143)
        ·
          refine ⟨33694744238097686002033715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22463162825398457334689143 33694744238097686002033715)
          ·
            refine ⟨50542116357146529003050573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33694744238097686002033715 50542116357146529003050573)
            ·
              refine ⟨18953293633929948376143965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50542116357146529003050573 18953293633929948376143965)
              ·
                refine ⟨7107485112723730641053987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18953293633929948376143965 7107485112723730641053987)
                ·
                  refine ⟨10661227669085595961580981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7107485112723730641053987 10661227669085595961580981)
                  ·
                    refine ⟨999490093976774621398217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10661227669085595961580981 999490093976774621398217)
                    ·
                      refine ⟨749617570482580966048663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 999490093976774621398217 749617570482580966048663)
                      ·
                        rfl

theorem cell23_1459875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 3, 1, 5, 2].length) (baseStart_1459875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459875 prefixEnd_1459875 := by exact prefixLift 1459875
  have htrace : WordTrace (prefixWord ++ tailWord_1459875) baseStart_1459875 baseEnd_1459875 := by
    simpa [prefixWord, tailWord_1459875, baseEnd_1459875] using wordTrace_append hprefix tailTrace_1459875
  have hstable : (prefixWord ++ tailWord_1459875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459875).length < 2 ^ (prefixWord ++ tailWord_1459875).sum := by decide
  have hdescent : baseEnd_1459875 < baseStart_1459875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459906 : List Nat := [3, 5, 1, 2, 1, 1, 1, 3, 6]
def baseStart_1459906 : Nat := 118140960795 + 1459906 * 2 ^ 59
def prefixEnd_1459906 : Nat := 4983230072969 + 3 ^ 40 * 1459906 * 2
def baseEnd_1459906 : Nat := 83292609820318927195669

theorem tailTrace_1459906 : CollatzResearch.WordTrace tailWord_1459906 prefixEnd_1459906 83292609820318927195669 := by
  unfold tailWord_1459906
  simp only [CollatzResearch.WordTrace]
  refine ⟨13311786562254342234891893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35498097499344912626378381 13311786562254342234891893)
  ·
    refine ⟨1247979990211344584521115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13311786562254342234891893 1247979990211344584521115)
    ·
      refine ⟨1871969985317016876781673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1247979990211344584521115 1871969985317016876781673)
      ·
        refine ⟨1403977488987762657586255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1871969985317016876781673 1403977488987762657586255)
        ·
          refine ⟨2105966233481643986379383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1403977488987762657586255 2105966233481643986379383)
          ·
            refine ⟨3158949350222465979569075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2105966233481643986379383 3158949350222465979569075)
            ·
              refine ⟨4738424025333698969353613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3158949350222465979569075 4738424025333698969353613)
              ·
                refine ⟨1776909009500137113507605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4738424025333698969353613 1776909009500137113507605)
                ·
                  refine ⟨83292609820318927195669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1776909009500137113507605 83292609820318927195669)
                  ·
                    rfl

theorem cell23_1459906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_1459906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459906 prefixEnd_1459906 := by exact prefixLift 1459906
  have htrace : WordTrace (prefixWord ++ tailWord_1459906) baseStart_1459906 baseEnd_1459906 := by
    simpa [prefixWord, tailWord_1459906, baseEnd_1459906] using wordTrace_append hprefix tailTrace_1459906
  have hstable : (prefixWord ++ tailWord_1459906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459906).length < 2 ^ (prefixWord ++ tailWord_1459906).sum := by decide
  have hdescent : baseEnd_1459906 < baseStart_1459906 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459922 : List Nat := [3, 2, 2, 2, 2, 2, 1, 1, 3, 1, 4]
def baseStart_1459922 : Nat := 118140960795 + 1459922 * 2 ^ 59
def prefixEnd_1459922 : Nat := 4983230072969 + 3 ^ 40 * 1459922 * 2
def baseEnd_1459922 : Nat := 749641704073342282160947

theorem tailTrace_1459922 : CollatzResearch.WordTrace tailWord_1459922 prefixEnd_1459922 749641704073342282160947 := by
  unfold tailWord_1459922
  simp only [CollatzResearch.WordTrace]
  refine ⟨13311932454239850918037505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35498486544639602448100013 13311932454239850918037505)
  ·
    refine ⟨9983949340679888188528129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13311932454239850918037505 9983949340679888188528129)
    ·
      refine ⟨7487962005509916141396097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9983949340679888188528129 7487962005509916141396097)
      ·
        refine ⟨5615971504132437106047073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7487962005509916141396097 5615971504132437106047073)
        ·
          refine ⟨4211978628099327829535305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5615971504132437106047073 4211978628099327829535305)
          ·
            refine ⟨3158983971074495872151479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4211978628099327829535305 3158983971074495872151479)
            ·
              refine ⟨4738475956611743808227219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3158983971074495872151479 4738475956611743808227219)
              ·
                refine ⟨7107713934917615712340829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4738475956611743808227219 7107713934917615712340829)
                ·
                  refine ⟨2665392725594105892127811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7107713934917615712340829 2665392725594105892127811)
                  ·
                    refine ⟨3998089088391158838191717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2665392725594105892127811 3998089088391158838191717)
                    ·
                      refine ⟨749641704073342282160947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3998089088391158838191717 749641704073342282160947)
                      ·
                        rfl

theorem cell23_1459922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 2, 1, 1, 3, 1, 4].length) (baseStart_1459922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459922 prefixEnd_1459922 := by exact prefixLift 1459922
  have htrace : WordTrace (prefixWord ++ tailWord_1459922) baseStart_1459922 baseEnd_1459922 := by
    simpa [prefixWord, tailWord_1459922, baseEnd_1459922] using wordTrace_append hprefix tailTrace_1459922
  have hstable : (prefixWord ++ tailWord_1459922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459922).length < 2 ^ (prefixWord ++ tailWord_1459922).sum := by decide
  have hdescent : baseEnd_1459922 < baseStart_1459922 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459928 : List Nat := [2, 1, 2, 2, 3, 1, 1, 11]
def baseStart_1459928 : Nat := 118140960795 + 1459928 * 2 ^ 59
def prefixEnd_1459928 : Nat := 4983230072969 + 3 ^ 40 * 1459928 * 2
def baseEnd_1459928 : Nat := 27764621665084046617997

theorem tailTrace_1459928 : CollatzResearch.WordTrace tailWord_1459928 prefixEnd_1459928 27764621665084046617997 := by
  unfold tailWord_1459928
  simp only [CollatzResearch.WordTrace]
  refine ⟨26623974327468833348434219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35498632436625111131245625 26623974327468833348434219)
  ·
    refine ⟨39935961491203250022651329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26623974327468833348434219 39935961491203250022651329)
    ·
      refine ⟨29951971118402437516988497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39935961491203250022651329 29951971118402437516988497)
      ·
        refine ⟨22463978338801828137741373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29951971118402437516988497 22463978338801828137741373)
        ·
          refine ⟨8423991877050685551653015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22463978338801828137741373 8423991877050685551653015)
          ·
            refine ⟨12635987815576028327479523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8423991877050685551653015 12635987815576028327479523)
            ·
              refine ⟨18953981723364042491219285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12635987815576028327479523 18953981723364042491219285)
              ·
                refine ⟨27764621665084046617997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 18953981723364042491219285 27764621665084046617997)
                ·
                  rfl

theorem cell23_1459928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 1, 11].length) (baseStart_1459928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459928 prefixEnd_1459928 := by exact prefixLift 1459928
  have htrace : WordTrace (prefixWord ++ tailWord_1459928) baseStart_1459928 baseEnd_1459928 := by
    simpa [prefixWord, tailWord_1459928, baseEnd_1459928] using wordTrace_append hprefix tailTrace_1459928
  have hstable : (prefixWord ++ tailWord_1459928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459928).length < 2 ^ (prefixWord ++ tailWord_1459928).sum := by decide
  have hdescent : baseEnd_1459928 < baseStart_1459928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459935 : List Nat := [1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 4]
def baseStart_1459935 : Nat := 118140960795 + 1459935 * 2 ^ 59
def prefixEnd_1459935 : Nat := 4983230072969 + 3 ^ 40 * 1459935 * 2
def baseEnd_1459935 : Nat := 749648379321850731298387

theorem tailTrace_1459935 : CollatzResearch.WordTrace tailWord_1459935 prefixEnd_1459935 749648379321850731298387 := by
  unfold tailWord_1459935
  simp only [CollatzResearch.WordTrace]
  refine ⟨53248203965912306892373259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35498802643941537928248839 53248203965912306892373259)
  ·
    refine ⟨79872305948868460338559889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53248203965912306892373259 79872305948868460338559889)
    ·
      refine ⟨59904229461651345253919917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79872305948868460338559889 59904229461651345253919917)
      ·
        refine ⟨22464086048119254470219969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59904229461651345253919917 22464086048119254470219969)
        ·
          refine ⟨16848064536089440852664977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22464086048119254470219969 16848064536089440852664977)
          ·
            refine ⟨12636048402067080639498733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16848064536089440852664977 12636048402067080639498733)
            ·
              refine ⟨4738518150775155239812025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12636048402067080639498733 4738518150775155239812025)
              ·
                refine ⟨3553888613081366429859019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4738518150775155239812025 3553888613081366429859019)
                ·
                  refine ⟨5330832919622049644788529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3553888613081366429859019 5330832919622049644788529)
                  ·
                    refine ⟨3998124689716537233591397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5330832919622049644788529 3998124689716537233591397)
                    ·
                      refine ⟨749648379321850731298387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3998124689716537233591397 749648379321850731298387)
                      ·
                        rfl

theorem cell23_1459935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 3, 2, 1, 2, 4].length) (baseStart_1459935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459935 prefixEnd_1459935 := by exact prefixLift 1459935
  have htrace : WordTrace (prefixWord ++ tailWord_1459935) baseStart_1459935 baseEnd_1459935 := by
    simpa [prefixWord, tailWord_1459935, baseEnd_1459935] using wordTrace_append hprefix tailTrace_1459935
  have hstable : (prefixWord ++ tailWord_1459935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459935).length < 2 ^ (prefixWord ++ tailWord_1459935).sum := by decide
  have hdescent : baseEnd_1459935 < baseStart_1459935 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459949 : List Nat := [1, 5, 1, 2, 1, 3, 2, 2, 2, 4]
def baseStart_1459949 : Nat := 118140960795 + 1459949 * 2 ^ 59
def prefixEnd_1459949 : Nat := 4983230072969 + 3 ^ 40 * 1459949 * 2
def baseEnd_1459949 : Nat := 249885189350337892174441

theorem tailTrace_1459949 : CollatzResearch.WordTrace tailWord_1459949 prefixEnd_1459949 249885189350337892174441 := by
  unfold tailWord_1459949
  simp only [CollatzResearch.WordTrace]
  refine ⟨53248714587861587283382901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35499143058574391522255267 53248714587861587283382901)
  ·
    refine ⟨4992066992612023807817147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53248714587861587283382901 4992066992612023807817147)
    ·
      refine ⟨7488100488918035711725721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4992066992612023807817147 7488100488918035711725721)
      ·
        refine ⟨5616075366688526783794291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7488100488918035711725721 5616075366688526783794291)
        ·
          refine ⟨8424113050032790175691437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5616075366688526783794291 8424113050032790175691437)
          ·
            refine ⟨3159042393762296315884289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8424113050032790175691437 3159042393762296315884289)
            ·
              refine ⟨2369281795321722236913217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3159042393762296315884289 2369281795321722236913217)
              ·
                refine ⟨1776961346491291677684913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2369281795321722236913217 1776961346491291677684913)
                ·
                  refine ⟨1332721009868468758263685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1776961346491291677684913 1332721009868468758263685)
                  ·
                    refine ⟨249885189350337892174441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1332721009868468758263685 249885189350337892174441)
                    ·
                      rfl

theorem cell23_1459949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 3, 2, 2, 2, 4].length) (baseStart_1459949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459949 prefixEnd_1459949 := by exact prefixLift 1459949
  have htrace : WordTrace (prefixWord ++ tailWord_1459949) baseStart_1459949 baseEnd_1459949 := by
    simpa [prefixWord, tailWord_1459949, baseEnd_1459949] using wordTrace_append hprefix tailTrace_1459949
  have hstable : (prefixWord ++ tailWord_1459949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459949).length < 2 ^ (prefixWord ++ tailWord_1459949).sum := by decide
  have hdescent : baseEnd_1459949 < baseStart_1459949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459972 : List Nat := [2, 3, 2, 2, 1, 2, 1, 3, 1, 3, 3]
def baseStart_1459972 : Nat := 118140960795 + 1459972 * 2 ^ 59
def prefixEnd_1459972 : Nat := 4983230072969 + 3 ^ 40 * 1459972 * 2
def baseEnd_1459972 : Nat := 749667378106067086535717

theorem tailTrace_1459972 : CollatzResearch.WordTrace tailWord_1459972 prefixEnd_1459972 749667378106067086535717 := by
  unfold tailWord_1459972
  simp only [CollatzResearch.WordTrace]
  refine ⟨26624776733389131105735085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35499702311185508140980113 26624776733389131105735085)
  ·
    refine ⟨9984291275020924164650657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26624776733389131105735085 9984291275020924164650657)
    ·
      refine ⟨7488218456265693123487993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9984291275020924164650657 7488218456265693123487993)
      ·
        refine ⟨5616163842199269842615995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7488218456265693123487993 5616163842199269842615995)
        ·
          refine ⟨8424245763298904763923993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5616163842199269842615995 8424245763298904763923993)
          ·
            refine ⟨6318184322474178572942995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8424245763298904763923993 6318184322474178572942995)
            ·
              refine ⟨9477276483711267859414493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6318184322474178572942995 9477276483711267859414493)
              ·
                refine ⟨3553978681391725447280435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9477276483711267859414493 3553978681391725447280435)
                ·
                  refine ⟨5330968022087588170920653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3553978681391725447280435 5330968022087588170920653)
                  ·
                    refine ⟨1999113008282845564095245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5330968022087588170920653 1999113008282845564095245)
                    ·
                      refine ⟨749667378106067086535717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1999113008282845564095245 749667378106067086535717)
                      ·
                        rfl

theorem cell23_1459972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_1459972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459972 prefixEnd_1459972 := by exact prefixLift 1459972
  have htrace : WordTrace (prefixWord ++ tailWord_1459972) baseStart_1459972 baseEnd_1459972 := by
    simpa [prefixWord, tailWord_1459972, baseEnd_1459972] using wordTrace_append hprefix tailTrace_1459972
  have hstable : (prefixWord ++ tailWord_1459972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459972).length < 2 ^ (prefixWord ++ tailWord_1459972).sum := by decide
  have hdescent : baseEnd_1459972 < baseStart_1459972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1459999 : List Nat := [1, 1, 2, 4, 2, 1, 3, 3, 1, 3, 2]
def baseStart_1459999 : Nat := 118140960795 + 1459999 * 2 ^ 59
def prefixEnd_1459999 : Nat := 4983230072969 + 3 ^ 40 * 1459999 * 2
def baseEnd_1459999 : Nat := 749681242083738480898093

theorem tailTrace_1459999 : CollatzResearch.WordTrace tailWord_1459999 prefixEnd_1459999 749681242083738480898093 := by
  unfold tailWord_1459999
  simp only [CollatzResearch.WordTrace]
  refine ⟨53250538237680445822703051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35500358825120297215135367 53250538237680445822703051)
  ·
    refine ⟨79875807356520668734054577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53250538237680445822703051 79875807356520668734054577)
    ·
      refine ⟨59906855517390501550540933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79875807356520668734054577 59906855517390501550540933)
      ·
        refine ⟨11232535409510719040726425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 59906855517390501550540933 11232535409510719040726425)
        ·
          refine ⟨8424401557133039280544819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11232535409510719040726425 8424401557133039280544819)
          ·
            refine ⟨12636602335699558920817229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8424401557133039280544819 12636602335699558920817229)
            ·
              refine ⟨4738725875887334595306461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12636602335699558920817229 4738725875887334595306461)
              ·
                refine ⟨1777022203457750473239923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4738725875887334595306461 1777022203457750473239923)
                ·
                  refine ⟨2665533305186625709859885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1777022203457750473239923 2665533305186625709859885)
                  ·
                    refine ⟨999574989444984641197457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2665533305186625709859885 999574989444984641197457)
                    ·
                      refine ⟨749681242083738480898093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 999574989444984641197457 749681242083738480898093)
                      ·
                        rfl

theorem cell23_1459999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 3, 1, 3, 2].length) (baseStart_1459999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1459999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1459999 prefixEnd_1459999 := by exact prefixLift 1459999
  have htrace : WordTrace (prefixWord ++ tailWord_1459999) baseStart_1459999 baseEnd_1459999 := by
    simpa [prefixWord, tailWord_1459999, baseEnd_1459999] using wordTrace_append hprefix tailTrace_1459999
  have hstable : (prefixWord ++ tailWord_1459999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1459999).length < 2 ^ (prefixWord ++ tailWord_1459999).sum := by decide
  have hdescent : baseEnd_1459999 < baseStart_1459999 := by decide
  rcases family_descends (prefixWord ++ tailWord_1459999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460005 : List Nat := [1, 3, 1, 2, 3, 2, 1, 2, 2, 6]
def baseStart_1460005 : Nat := 118140960795 + 1460005 * 2 ^ 59
def prefixEnd_1460005 : Nat := 4983230072969 + 3 ^ 40 * 1460005 * 2
def baseEnd_1460005 : Nat := 249894774322555152474355

theorem tailTrace_1460005 : CollatzResearch.WordTrace tailWord_1460005 prefixEnd_1460005 249894774322555152474355 := by
  unfold tailWord_1460005
  simp only [CollatzResearch.WordTrace]
  refine ⟨53250757075658708847421469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35500504717105805898280979 53250757075658708847421469)
  ·
    refine ⟨19969033903372015817783051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53250757075658708847421469 19969033903372015817783051)
    ·
      refine ⟨29953550855058023726674577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19969033903372015817783051 29953550855058023726674577)
      ·
        refine ⟨22465163141293517795005933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29953550855058023726674577 22465163141293517795005933)
        ·
          refine ⟨8424436177985069173127225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22465163141293517795005933 8424436177985069173127225)
          ·
            refine ⟨6318327133488801879845419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8424436177985069173127225 6318327133488801879845419)
            ·
              refine ⟨9477490700233202819768129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6318327133488801879845419 9477490700233202819768129)
              ·
                refine ⟨7108118025174902114826097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9477490700233202819768129 7108118025174902114826097)
                ·
                  refine ⟨5331088518881176586119573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7108118025174902114826097 5331088518881176586119573)
                  ·
                    refine ⟨249894774322555152474355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5331088518881176586119573 249894774322555152474355)
                    ·
                      rfl

theorem cell23_1460005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 2, 1, 2, 2, 6].length) (baseStart_1460005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460005 prefixEnd_1460005 := by exact prefixLift 1460005
  have htrace : WordTrace (prefixWord ++ tailWord_1460005) baseStart_1460005 baseEnd_1460005 := by
    simpa [prefixWord, tailWord_1460005, baseEnd_1460005] using wordTrace_append hprefix tailTrace_1460005
  have hstable : (prefixWord ++ tailWord_1460005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460005).length < 2 ^ (prefixWord ++ tailWord_1460005).sum := by decide
  have hdescent : baseEnd_1460005 < baseStart_1460005 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460035 : List Nat := [1, 1, 1, 3, 1, 5, 2, 2, 7]
def baseStart_1460035 : Nat := 118140960795 + 1460035 * 2 ^ 59
def prefixEnd_1460035 : Nat := 4983230072969 + 3 ^ 40 * 1460035 * 2
def baseEnd_1460035 : Nat := 83299969709700037783103

theorem tailTrace_1460035 : CollatzResearch.WordTrace tailWord_1460035 prefixEnd_1460035 83299969709700037783103 := by
  unfold tailWord_1460035
  simp only [CollatzResearch.WordTrace]
  refine ⟨53251851265550023971013559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35501234177033349314009039 53251851265550023971013559)
  ·
    refine ⟨79877776898325035956520339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53251851265550023971013559 79877776898325035956520339)
    ·
      refine ⟨119816665347487553934780509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79877776898325035956520339 119816665347487553934780509)
      ·
        refine ⟨44931249505307832725542691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 119816665347487553934780509 44931249505307832725542691)
        ·
          refine ⟨67396874257961749088314037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44931249505307832725542691 67396874257961749088314037)
          ·
            refine ⟨6318456961683913977029441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67396874257961749088314037 6318456961683913977029441)
            ·
              refine ⟨4738842721262935482772081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6318456961683913977029441 4738842721262935482772081)
              ·
                refine ⟨3554132040947201612079061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4738842721262935482772081 3554132040947201612079061)
                ·
                  refine ⟨83299969709700037783103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3554132040947201612079061 83299969709700037783103)
                  ·
                    rfl

theorem cell23_1460035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 2, 2, 7].length) (baseStart_1460035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460035 prefixEnd_1460035 := by exact prefixLift 1460035
  have htrace : WordTrace (prefixWord ++ tailWord_1460035) baseStart_1460035 baseEnd_1460035 := by
    simpa [prefixWord, tailWord_1460035, baseEnd_1460035] using wordTrace_append hprefix tailTrace_1460035
  have hstable : (prefixWord ++ tailWord_1460035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460035).length < 2 ^ (prefixWord ++ tailWord_1460035).sum := by decide
  have hdescent : baseEnd_1460035 < baseStart_1460035 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460115 : List Nat := [1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 4]
def baseStart_1460115 : Nat := 118140960795 + 1460115 * 2 ^ 59
def prefixEnd_1460115 : Nat := 4983230072969 + 3 ^ 40 * 1460115 * 2
def baseEnd_1460115 : Nat := 749740805839660027047559

theorem tailTrace_1460115 : CollatzResearch.WordTrace tailWord_1460115 prefixEnd_1460115 749740805839660027047559 := by
  unfold tailWord_1460115
  simp only [CollatzResearch.WordTrace]
  refine ⟨53254769105260197633925799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35503179403506798422617199 53254769105260197633925799)
  ·
    refine ⟨79882153657890296450888699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53254769105260197633925799 79882153657890296450888699)
    ·
      refine ⟨119823230486835444676333049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79882153657890296450888699 119823230486835444676333049)
      ·
        refine ⟨89867422865126583507249787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119823230486835444676333049 89867422865126583507249787)
        ·
          refine ⟨134801134297689875260874681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89867422865126583507249787 134801134297689875260874681)
          ·
            refine ⟨101100850723267406445656011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134801134297689875260874681 101100850723267406445656011)
            ·
              refine ⟨151651276084901109668484017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101100850723267406445656011 151651276084901109668484017)
              ·
                refine ⟨113738457063675832251363013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 151651276084901109668484017 113738457063675832251363013)
                ·
                  refine ⟨21325960699439218547130565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 113738457063675832251363013 21325960699439218547130565)
                  ·
                    refine ⟨3998617631144853477586981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21325960699439218547130565 3998617631144853477586981)
                    ·
                      refine ⟨749740805839660027047559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3998617631144853477586981 749740805839660027047559)
                      ·
                        rfl

theorem cell23_1460115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 2, 4, 4, 4].length) (baseStart_1460115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460115 prefixEnd_1460115 := by exact prefixLift 1460115
  have htrace : WordTrace (prefixWord ++ tailWord_1460115) baseStart_1460115 baseEnd_1460115 := by
    simpa [prefixWord, tailWord_1460115, baseEnd_1460115] using wordTrace_append hprefix tailTrace_1460115
  have hstable : (prefixWord ++ tailWord_1460115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460115).length < 2 ^ (prefixWord ++ tailWord_1460115).sum := by decide
  have hdescent : baseEnd_1460115 < baseStart_1460115 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460120 : List Nat := [2, 1, 2, 6, 2, 1, 2, 2, 5]
def baseStart_1460120 : Nat := 118140960795 + 1460120 * 2 ^ 59
def prefixEnd_1460120 : Nat := 4983230072969 + 3 ^ 40 * 1460120 * 2
def baseEnd_1460120 : Nat := 83304819249214723053893

theorem tailTrace_1460120 : CollatzResearch.WordTrace tailWord_1460120 prefixEnd_1460120 83304819249214723053893 := by
  unfold tailWord_1460120
  simp only [CollatzResearch.WordTrace]
  refine ⟨26627475735121041743928907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35503300980161388991905209 26627475735121041743928907)
  ·
    refine ⟨39941213602681562615893361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26627475735121041743928907 39941213602681562615893361)
    ·
      refine ⟨29955910202011171961920021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 39941213602681562615893361 29955910202011171961920021)
      ·
        refine ⟨1404183290719273685715001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 29955910202011171961920021 1404183290719273685715001)
        ·
          refine ⟨1053137468039455264286251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1404183290719273685715001 1053137468039455264286251)
          ·
            refine ⟨1579706202059182896429377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1053137468039455264286251 1579706202059182896429377)
            ·
              refine ⟨1184779651544387172322033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1579706202059182896429377 1184779651544387172322033)
              ·
                refine ⟨888584738658290379241525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1184779651544387172322033 888584738658290379241525)
                ·
                  refine ⟨83304819249214723053893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 888584738658290379241525 83304819249214723053893)
                  ·
                    rfl

theorem cell23_1460120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 1, 2, 2, 5].length) (baseStart_1460120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460120 prefixEnd_1460120 := by exact prefixLift 1460120
  have htrace : WordTrace (prefixWord ++ tailWord_1460120) baseStart_1460120 baseEnd_1460120 := by
    simpa [prefixWord, tailWord_1460120, baseEnd_1460120] using wordTrace_append hprefix tailTrace_1460120
  have hstable : (prefixWord ++ tailWord_1460120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460120).length < 2 ^ (prefixWord ++ tailWord_1460120).sum := by decide
  have hdescent : baseEnd_1460120 < baseStart_1460120 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460156 : List Nat := [2, 2, 2, 5, 1, 1, 1, 1, 1, 4, 3]
def baseStart_1460156 : Nat := 118140960795 + 1460156 * 2 ^ 59
def prefixEnd_1460156 : Nat := 4983230072969 + 3 ^ 40 * 1460156 * 2
def baseEnd_1460156 : Nat := 749761858546494366634871

theorem tailTrace_1460156 : CollatzResearch.WordTrace tailWord_1460156 prefixEnd_1460156 749761858546494366634871 := by
  unfold tailWord_1460156
  simp only [CollatzResearch.WordTrace]
  refine ⟨26628132249055830818084161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35504176332074441090778881 26628132249055830818084161)
  ·
    refine ⟨19971099186791873113563121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26628132249055830818084161 19971099186791873113563121)
    ·
      refine ⟨14978324390093904835172341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19971099186791873113563121 14978324390093904835172341)
      ·
        refine ⟨1404217911571303578297407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14978324390093904835172341 1404217911571303578297407)
        ·
          refine ⟨2106326867356955367446111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1404217911571303578297407 2106326867356955367446111)
          ·
            refine ⟨3159490301035433051169167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2106326867356955367446111 3159490301035433051169167)
            ·
              refine ⟨4739235451553149576753751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3159490301035433051169167 4739235451553149576753751)
              ·
                refine ⟨7108853177329724365130627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4739235451553149576753751 7108853177329724365130627)
                ·
                  refine ⟨10663279765994586547695941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7108853177329724365130627 10663279765994586547695941)
                  ·
                    refine ⟨1999364956123984977692989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 10663279765994586547695941 1999364956123984977692989)
                    ·
                      refine ⟨749761858546494366634871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1999364956123984977692989 749761858546494366634871)
                      ·
                        rfl

theorem cell23_1460156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 1, 1, 1, 4, 3].length) (baseStart_1460156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460156 prefixEnd_1460156 := by exact prefixLift 1460156
  have htrace : WordTrace (prefixWord ++ tailWord_1460156) baseStart_1460156 baseEnd_1460156 := by
    simpa [prefixWord, tailWord_1460156, baseEnd_1460156] using wordTrace_append hprefix tailTrace_1460156
  have hstable : (prefixWord ++ tailWord_1460156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460156).length < 2 ^ (prefixWord ++ tailWord_1460156).sum := by decide
  have hdescent : baseEnd_1460156 < baseStart_1460156 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460192 : List Nat := [2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 4]
def baseStart_1460192 : Nat := 118140960795 + 1460192 * 2 ^ 59
def prefixEnd_1460192 : Nat := 4983230072969 + 3 ^ 40 * 1460192 * 2
def baseEnd_1460192 : Nat := 749780343850056225784705

theorem tailTrace_1460192 : CollatzResearch.WordTrace tailWord_1460192 prefixEnd_1460192 749780343850056225784705 := by
  unfold tailWord_1460192
  simp only [CollatzResearch.WordTrace]
  refine ⟨26628788762990619892239415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35505051683987493189652553 26628788762990619892239415)
  ·
    refine ⟨39943183144485929838359123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26628788762990619892239415 39943183144485929838359123)
    ·
      refine ⟨59914774716728894757538685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39943183144485929838359123 59914774716728894757538685)
      ·
        refine ⟨22468040518773335534077007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 59914774716728894757538685 22468040518773335534077007)
        ·
          refine ⟨33702060778160003301115511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22468040518773335534077007 33702060778160003301115511)
          ·
            refine ⟨50553091167240004951673267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33702060778160003301115511 50553091167240004951673267)
            ·
              refine ⟨75829636750860007427509901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50553091167240004951673267 75829636750860007427509901)
              ·
                refine ⟨28436113781572502785316213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 75829636750860007427509901 28436113781572502785316213)
                ·
                  refine ⟨2665885667022422136123395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 28436113781572502785316213 2665885667022422136123395)
                  ·
                    refine ⟨3998828500533633204185093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2665885667022422136123395 3998828500533633204185093)
                    ·
                      refine ⟨749780343850056225784705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3998828500533633204185093 749780343850056225784705)
                      ·
                        rfl

theorem cell23_1460192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 5, 1, 4].length) (baseStart_1460192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460192 prefixEnd_1460192 := by exact prefixLift 1460192
  have htrace : WordTrace (prefixWord ++ tailWord_1460192) baseStart_1460192 baseEnd_1460192 := by
    simpa [prefixWord, tailWord_1460192, baseEnd_1460192] using wordTrace_append hprefix tailTrace_1460192
  have hstable : (prefixWord ++ tailWord_1460192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460192).length < 2 ^ (prefixWord ++ tailWord_1460192).sum := by decide
  have hdescent : baseEnd_1460192 < baseStart_1460192 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460206 : List Nat := [4, 1, 2, 1, 3, 2, 2, 2, 1, 5]
def baseStart_1460206 : Nat := 118140960795 + 1460206 * 2 ^ 59
def prefixEnd_1460206 : Nat := 4983230072969 + 3 ^ 40 * 1460206 * 2
def baseEnd_1460206 : Nat := 249929177526406390336547

theorem tailTrace_1460206 : CollatzResearch.WordTrace tailWord_1460206 prefixEnd_1460206 249929177526406390336547 := by
  unfold tailWord_1460206
  simp only [CollatzResearch.WordTrace]
  refine ⟨6657261018491315021936059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35505392098620346783658981 6657261018491315021936059)
  ·
    refine ⟨9985891527736972532904089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6657261018491315021936059 9985891527736972532904089)
    ·
      refine ⟨7489418645802729399678067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9985891527736972532904089 7489418645802729399678067)
      ·
        refine ⟨11234127968704094099517101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7489418645802729399678067 11234127968704094099517101)
        ·
          refine ⟨4212797988264035287318913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11234127968704094099517101 4212797988264035287318913)
          ·
            refine ⟨3159598491198026465489185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4212797988264035287318913 3159598491198026465489185)
            ·
              refine ⟨2369698868398519849116889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3159598491198026465489185 2369698868398519849116889)
              ·
                refine ⟨1777274151298889886837667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2369698868398519849116889 1777274151298889886837667)
                ·
                  refine ⟨2665911226948334830256501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1777274151298889886837667 2665911226948334830256501)
                  ·
                    refine ⟨249929177526406390336547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2665911226948334830256501 249929177526406390336547)
                    ·
                      rfl

theorem cell23_1460206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_1460206 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460206 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460206 prefixEnd_1460206 := by exact prefixLift 1460206
  have htrace : WordTrace (prefixWord ++ tailWord_1460206) baseStart_1460206 baseEnd_1460206 := by
    simpa [prefixWord, tailWord_1460206, baseEnd_1460206] using wordTrace_append hprefix tailTrace_1460206
  have hstable : (prefixWord ++ tailWord_1460206).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460206).length < 2 ^ (prefixWord ++ tailWord_1460206).sum := by decide
  have hdescent : baseEnd_1460206 < baseStart_1460206 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460229 : List Nat := [1, 3, 1, 1, 2, 5, 2, 1, 1, 1, 5]
def baseStart_1460229 : Nat := 118140960795 + 1460229 * 2 ^ 59
def prefixEnd_1460229 : Nat := 4983230072969 + 3 ^ 40 * 1460229 * 2
def baseEnd_1460229 : Nat := 749799342634272581022035

theorem tailTrace_1460229 : CollatzResearch.WordTrace tailWord_1460229 prefixEnd_1460229 749799342634272581022035 := by
  unfold tailWord_1460229
  simp only [CollatzResearch.WordTrace]
  refine ⟨53258927026847195103575741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35505951351231463402383827 53258927026847195103575741)
  ·
    refine ⟨19972097635067698163840903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53258927026847195103575741 19972097635067698163840903)
    ·
      refine ⟨29958146452601547245761355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19972097635067698163840903 29958146452601547245761355)
      ·
        refine ⟨44937219678902320868642033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29958146452601547245761355 44937219678902320868642033)
        ·
          refine ⟨33702914759176740651481525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44937219678902320868642033 33702914759176740651481525)
          ·
            refine ⟨3159648258672819436076393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33702914759176740651481525 3159648258672819436076393)
            ·
              refine ⟨2369736194004614577057295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3159648258672819436076393 2369736194004614577057295)
              ·
                refine ⟨3554604291006921865585943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2369736194004614577057295 3554604291006921865585943)
                ·
                  refine ⟨5331906436510382798378915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3554604291006921865585943 5331906436510382798378915)
                  ·
                    refine ⟨7997859654765574197568373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5331906436510382798378915 7997859654765574197568373)
                    ·
                      refine ⟨749799342634272581022035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 7997859654765574197568373 749799342634272581022035)
                      ·
                        rfl

theorem cell23_1460229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 1, 1, 5].length) (baseStart_1460229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460229 prefixEnd_1460229 := by exact prefixLift 1460229
  have htrace : WordTrace (prefixWord ++ tailWord_1460229) baseStart_1460229 baseEnd_1460229 := by
    simpa [prefixWord, tailWord_1460229, baseEnd_1460229] using wordTrace_append hprefix tailTrace_1460229
  have hstable : (prefixWord ++ tailWord_1460229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460229).length < 2 ^ (prefixWord ++ tailWord_1460229).sum := by decide
  have hdescent : baseEnd_1460229 < baseStart_1460229 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460243 : List Nat := [1, 1, 1, 2, 1, 4, 2, 6, 1, 2, 2]
def baseStart_1460243 : Nat := 118140960795 + 1460243 * 2 ^ 59
def prefixEnd_1460243 : Nat := 4983230072969 + 3 ^ 40 * 1460243 * 2
def baseEnd_1460243 : Nat := 749806531363435526246971

theorem tailTrace_1460243 : CollatzResearch.WordTrace tailWord_1460243 prefixEnd_1460243 749806531363435526246971 := by
  unfold tailWord_1460243
  simp only [CollatzResearch.WordTrace]
  refine ⟨53259437648796475494585383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35506291765864316996390255 53259437648796475494585383)
  ·
    refine ⟨79889156473194713241878075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53259437648796475494585383 79889156473194713241878075)
    ·
      refine ⟨119833734709792069862817113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79889156473194713241878075 119833734709792069862817113)
      ·
        refine ⟨89875301032344052397112835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119833734709792069862817113 89875301032344052397112835)
        ·
          refine ⟨134812951548516078595669253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89875301032344052397112835 134812951548516078595669253)
          ·
            refine ⟨25277428415346764736687985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 134812951548516078595669253 25277428415346764736687985)
            ·
              refine ⟨18958071311510073552515989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25277428415346764736687985 18958071311510073552515989)
              ·
                refine ⟨888659592727034697774187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18958071311510073552515989 888659592727034697774187)
                ·
                  refine ⟨1332989389090552046661281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 888659592727034697774187 1332989389090552046661281)
                  ·
                    refine ⟨999742041817914034995961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1332989389090552046661281 999742041817914034995961)
                    ·
                      refine ⟨749806531363435526246971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 999742041817914034995961 749806531363435526246971)
                      ·
                        rfl

theorem cell23_1460243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 6, 1, 2, 2].length) (baseStart_1460243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460243 prefixEnd_1460243 := by exact prefixLift 1460243
  have htrace : WordTrace (prefixWord ++ tailWord_1460243) baseStart_1460243 baseEnd_1460243 := by
    simpa [prefixWord, tailWord_1460243, baseEnd_1460243] using wordTrace_append hprefix tailTrace_1460243
  have hstable : (prefixWord ++ tailWord_1460243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460243).length < 2 ^ (prefixWord ++ tailWord_1460243).sum := by decide
  have hdescent : baseEnd_1460243 < baseStart_1460243 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460253 : List Nat := [1, 4, 2, 2, 2, 1, 4, 1, 2, 4]
def baseStart_1460253 : Nat := 118140960795 + 1460253 * 2 ^ 59
def prefixEnd_1460253 : Nat := 4983230072969 + 3 ^ 40 * 1460253 * 2
def baseEnd_1460253 : Nat := 249937222056660162373975

theorem tailTrace_1460253 : CollatzResearch.WordTrace tailWord_1460253 prefixEnd_1460253 249937222056660162373975 := by
  unfold tailWord_1460253
  simp only [CollatzResearch.WordTrace]
  refine ⟨53259802378760247202449413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35506534919173498134966275 53259802378760247202449413)
  ·
    refine ⟨9986212946017546350459265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53259802378760247202449413 9986212946017546350459265)
    ·
      refine ⟨7489659709513159762844449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9986212946017546350459265 7489659709513159762844449)
      ·
        refine ⟨5617244782134869822133337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7489659709513159762844449 5617244782134869822133337)
        ·
          refine ⟨4212933586601152366600003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5617244782134869822133337 4212933586601152366600003)
          ·
            refine ⟨6319400379901728549900005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4212933586601152366600003 6319400379901728549900005)
            ·
              refine ⟨1184887571231574103106251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6319400379901728549900005 1184887571231574103106251)
              ·
                refine ⟨1777331356847361154659377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1184887571231574103106251 1777331356847361154659377)
                ·
                  refine ⟨1332998517635520865994533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1777331356847361154659377 1332998517635520865994533)
                  ·
                    refine ⟨249937222056660162373975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1332998517635520865994533 249937222056660162373975)
                    ·
                      rfl

theorem cell23_1460253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 4, 1, 2, 4].length) (baseStart_1460253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460253 prefixEnd_1460253 := by exact prefixLift 1460253
  have htrace : WordTrace (prefixWord ++ tailWord_1460253) baseStart_1460253 baseEnd_1460253 := by
    simpa [prefixWord, tailWord_1460253, baseEnd_1460253] using wordTrace_append hprefix tailTrace_1460253
  have hstable : (prefixWord ++ tailWord_1460253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460253).length < 2 ^ (prefixWord ++ tailWord_1460253).sum := by decide
  have hdescent : baseEnd_1460253 < baseStart_1460253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460259 : List Nat := [1, 1, 1, 4, 3, 1, 2, 3, 1, 3, 3]
def baseStart_1460259 : Nat := 118140960795 + 1460259 * 2 ^ 59
def prefixEnd_1460259 : Nat := 4983230072969 + 3 ^ 40 * 1460259 * 2
def baseEnd_1460259 : Nat := 749814747053907463646897

theorem tailTrace_1460259 : CollatzResearch.WordTrace tailWord_1460259 prefixEnd_1460259 749814747053907463646897 := by
  unfold tailWord_1460259
  simp only [CollatzResearch.WordTrace]
  refine ⟨53260021216738510227167831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35506680811159006818111887 53260021216738510227167831)
  ·
    refine ⟨79890031825107765340751747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53260021216738510227167831 79890031825107765340751747)
    ·
      refine ⟨119835047737661648011127621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79890031825107765340751747 119835047737661648011127621)
      ·
        refine ⟨22469071450811559002086429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119835047737661648011127621 22469071450811559002086429)
        ·
          refine ⟨8425901794054334625782411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22469071450811559002086429 8425901794054334625782411)
          ·
            refine ⟨12638852691081501938673617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8425901794054334625782411 12638852691081501938673617)
            ·
              refine ⟨9479139518311126454005213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12638852691081501938673617 9479139518311126454005213)
              ·
                refine ⟨3554677319366672420251955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9479139518311126454005213 3554677319366672420251955)
                ·
                  refine ⟨5332015979050008630377933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3554677319366672420251955 5332015979050008630377933)
                  ·
                    refine ⟨1999505992143753236391725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5332015979050008630377933 1999505992143753236391725)
                    ·
                      refine ⟨749814747053907463646897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1999505992143753236391725 749814747053907463646897)
                      ·
                        rfl

theorem cell23_1460259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 2, 3, 1, 3, 3].length) (baseStart_1460259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460259 prefixEnd_1460259 := by exact prefixLift 1460259
  have htrace : WordTrace (prefixWord ++ tailWord_1460259) baseStart_1460259 baseEnd_1460259 := by
    simpa [prefixWord, tailWord_1460259, baseEnd_1460259] using wordTrace_append hprefix tailTrace_1460259
  have hstable : (prefixWord ++ tailWord_1460259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460259).length < 2 ^ (prefixWord ++ tailWord_1460259).sum := by decide
  have hdescent : baseEnd_1460259 < baseStart_1460259 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460260 : List Nat := [2, 3, 1, 4, 3, 1, 1, 2, 1, 1, 4]
def baseStart_1460260 : Nat := 118140960795 + 1460260 * 2 ^ 59
def prefixEnd_1460260 : Nat := 4983230072969 + 3 ^ 40 * 1460260 * 2
def baseEnd_1460260 : Nat := 749815260534561959734393

theorem tailTrace_1460260 : CollatzResearch.WordTrace tailWord_1460260 prefixEnd_1460260 749815260534561959734393 := by
  unfold tailWord_1460260
  simp only [CollatzResearch.WordTrace]
  refine ⟨26630028844867443698977117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35506705126489924931969489 26630028844867443698977117)
  ·
    refine ⟨9986260816825291387116419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26630028844867443698977117 9986260816825291387116419)
    ·
      refine ⟨14979391225237937080674629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9986260816825291387116419 14979391225237937080674629)
      ·
        refine ⟨2808635854732113202626493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14979391225237937080674629 2808635854732113202626493)
        ·
          refine ⟨1053238445524542450984935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2808635854732113202626493 1053238445524542450984935)
          ·
            refine ⟨1579857668286813676477403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1053238445524542450984935 1579857668286813676477403)
            ·
              refine ⟨2369786502430220514716105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1579857668286813676477403 2369786502430220514716105)
              ·
                refine ⟨1777339876822665386037079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2369786502430220514716105 1777339876822665386037079)
                ·
                  refine ⟨2666009815233998079055619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1777339876822665386037079 2666009815233998079055619)
                  ·
                    refine ⟨3999014722850997118583429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2666009815233998079055619 3999014722850997118583429)
                    ·
                      refine ⟨749815260534561959734393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3999014722850997118583429 749815260534561959734393)
                      ·
                        rfl

theorem cell23_1460260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_1460260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460260 prefixEnd_1460260 := by exact prefixLift 1460260
  have htrace : WordTrace (prefixWord ++ tailWord_1460260) baseStart_1460260 baseEnd_1460260 := by
    simpa [prefixWord, tailWord_1460260, baseEnd_1460260] using wordTrace_append hprefix tailTrace_1460260
  have hstable : (prefixWord ++ tailWord_1460260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460260).length < 2 ^ (prefixWord ++ tailWord_1460260).sum := by decide
  have hdescent : baseEnd_1460260 < baseStart_1460260 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460263 : List Nat := [1, 1, 7, 1, 2, 1, 1, 1, 3, 2, 3]
def baseStart_1460263 : Nat := 118140960795 + 1460263 * 2 ^ 59
def prefixEnd_1460263 : Nat := 4983230072969 + 3 ^ 40 * 1460263 * 2
def baseEnd_1460263 : Nat := 749816800976525447996879

theorem tailTrace_1460263 : CollatzResearch.WordTrace tailWord_1460263 prefixEnd_1460263 749816800976525447996879 := by
  unfold tailWord_1460263
  simp only [CollatzResearch.WordTrace]
  refine ⟨53260167108724018910313443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35506778072482679273542295 53260167108724018910313443)
  ·
    refine ⟨79890250663086028365470165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53260167108724018910313443 79890250663086028365470165)
    ·
      refine ⟨1872427749916078789815707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 79890250663086028365470165 1872427749916078789815707)
      ·
        refine ⟨2808641624874118184723561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1872427749916078789815707 2808641624874118184723561)
        ·
          refine ⟨2106481218655588638542671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2808641624874118184723561 2106481218655588638542671)
          ·
            refine ⟨3159721827983382957814007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2106481218655588638542671 3159721827983382957814007)
            ·
              refine ⟨4739582741975074436721011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3159721827983382957814007 4739582741975074436721011)
              ·
                refine ⟨7109374112962611655081517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4739582741975074436721011 7109374112962611655081517)
                ·
                  refine ⟨2666015292360979370655569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7109374112962611655081517 2666015292360979370655569)
                  ·
                    refine ⟨1999511469270734527991677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2666015292360979370655569 1999511469270734527991677)
                    ·
                      refine ⟨749816800976525447996879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1999511469270734527991677 749816800976525447996879)
                      ·
                        rfl

theorem cell23_1460263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_1460263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460263 prefixEnd_1460263 := by exact prefixLift 1460263
  have htrace : WordTrace (prefixWord ++ tailWord_1460263) baseStart_1460263 baseEnd_1460263 := by
    simpa [prefixWord, tailWord_1460263, baseEnd_1460263] using wordTrace_append hprefix tailTrace_1460263
  have hstable : (prefixWord ++ tailWord_1460263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460263).length < 2 ^ (prefixWord ++ tailWord_1460263).sum := by decide
  have hdescent : baseEnd_1460263 < baseStart_1460263 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460309 : List Nat := [1, 3, 2, 2, 1, 4, 1, 1, 2, 6]
def baseStart_1460309 : Nat := 118140960795 + 1460309 * 2 ^ 59
def prefixEnd_1460309 : Nat := 4983230072969 + 3 ^ 40 * 1460309 * 2
def baseEnd_1460309 : Nat := 249946807028877422673889

theorem tailTrace_1460309 : CollatzResearch.WordTrace tailWord_1460309 prefixEnd_1460309 249946807028877422673889 := by
  unfold tailWord_1460309
  simp only [CollatzResearch.WordTrace]
  refine ⟨53261844866557368766487981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35507896577704912510991987 53261844866557368766487981)
  ·
    refine ⟨19973191824959013287432993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53261844866557368766487981 19973191824959013287432993)
    ·
      refine ⟨14979893868719259965574745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19973191824959013287432993 14979893868719259965574745)
      ·
        refine ⟨11234920401539444974181059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14979893868719259965574745 11234920401539444974181059)
        ·
          refine ⟨16852380602309167461271589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11234920401539444974181059 16852380602309167461271589)
          ·
            refine ⟨3159821362932968898988423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16852380602309167461271589 3159821362932968898988423)
            ·
              refine ⟨4739732044399453348482635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3159821362932968898988423 4739732044399453348482635)
              ·
                refine ⟨7109598066599180022723953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4739732044399453348482635 7109598066599180022723953)
                ·
                  refine ⟨5332198549949385017042965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7109598066599180022723953 5332198549949385017042965)
                  ·
                    refine ⟨249946807028877422673889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5332198549949385017042965 249946807028877422673889)
                    ·
                      rfl

theorem cell23_1460309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 2, 6].length) (baseStart_1460309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460309 prefixEnd_1460309 := by exact prefixLift 1460309
  have htrace : WordTrace (prefixWord ++ tailWord_1460309) baseStart_1460309 baseEnd_1460309 := by
    simpa [prefixWord, tailWord_1460309, baseEnd_1460309] using wordTrace_append hprefix tailTrace_1460309
  have hstable : (prefixWord ++ tailWord_1460309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460309).length < 2 ^ (prefixWord ++ tailWord_1460309).sum := by decide
  have hdescent : baseEnd_1460309 < baseStart_1460309 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460310 : List Nat := [5, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_1460310 : Nat := 118140960795 + 1460310 * 2 ^ 59
def prefixEnd_1460310 : Nat := 4983230072969 + 3 ^ 40 * 1460310 * 2
def baseEnd_1460310 : Nat := 749840934567286764109163

theorem tailTrace_1460310 : CollatzResearch.WordTrace tailWord_1460310 prefixEnd_1460310 749840934567286764109163 := by
  unfold tailWord_1460310
  simp only [CollatzResearch.WordTrace]
  refine ⟨3328867583722109121079649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 35507920893035830624849589 3328867583722109121079649)
  ·
    refine ⟨2496650687791581840809737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3328867583722109121079649 2496650687791581840809737)
    ·
      refine ⟨1872488015843686380607303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2496650687791581840809737 1872488015843686380607303)
      ·
        refine ⟨2808732023765529570910955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1872488015843686380607303 2808732023765529570910955)
        ·
          refine ⟨4213098035648294356366433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2808732023765529570910955 4213098035648294356366433)
          ·
            refine ⟨3159823526736220767274825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4213098035648294356366433 3159823526736220767274825)
            ·
              refine ⟨2369867645052165575456119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3159823526736220767274825 2369867645052165575456119)
              ·
                refine ⟨3554801467578248363184179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2369867645052165575456119 3554801467578248363184179)
                ·
                  refine ⟨5332202201367372544776269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3554801467578248363184179 5332202201367372544776269)
                  ·
                    refine ⟨1999575825512764704291101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5332202201367372544776269 1999575825512764704291101)
                    ·
                      refine ⟨749840934567286764109163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1999575825512764704291101 749840934567286764109163)
                      ·
                        rfl

theorem cell23_1460310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_1460310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460310 prefixEnd_1460310 := by exact prefixLift 1460310
  have htrace : WordTrace (prefixWord ++ tailWord_1460310) baseStart_1460310 baseEnd_1460310 := by
    simpa [prefixWord, tailWord_1460310, baseEnd_1460310] using wordTrace_append hprefix tailTrace_1460310
  have hstable : (prefixWord ++ tailWord_1460310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460310).length < 2 ^ (prefixWord ++ tailWord_1460310).sum := by decide
  have hdescent : baseEnd_1460310 < baseStart_1460310 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460333 : List Nat := [1, 5, 1, 1, 2, 1, 2, 2, 4, 2, 2]
def baseStart_1460333 : Nat := 118140960795 + 1460333 * 2 ^ 59
def prefixEnd_1460333 : Nat := 4983230072969 + 3 ^ 40 * 1460333 * 2
def baseEnd_1460333 : Nat := 749852744622340174121557

theorem tailTrace_1460333 : CollatzResearch.WordTrace tailWord_1460333 prefixEnd_1460333 749852744622340174121557 := by
  unfold tailWord_1460333
  simp only [CollatzResearch.WordTrace]
  refine ⟨53262720218470420865361653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35508480145646947243574435 53262720218470420865361653)
  ·
    refine ⟨4993380020481601956127655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53262720218470420865361653 4993380020481601956127655)
    ·
      refine ⟨7490070030722402934191483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4993380020481601956127655 7490070030722402934191483)
      ·
        refine ⟨11235105046083604401287225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7490070030722402934191483 11235105046083604401287225)
        ·
          refine ⟨8426328784562703300965419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11235105046083604401287225 8426328784562703300965419)
          ·
            refine ⟨12639493176844054951448129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8426328784562703300965419 12639493176844054951448129)
            ·
              refine ⟨9479619882633041213586097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12639493176844054951448129 9479619882633041213586097)
              ·
                refine ⟨7109714911974780910189573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9479619882633041213586097 7109714911974780910189573)
                ·
                  refine ⟨1333071545995271420660545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7109714911974780910189573 1333071545995271420660545)
                  ·
                    refine ⟨999803659496453565495409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1333071545995271420660545 999803659496453565495409)
                    ·
                      refine ⟨749852744622340174121557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 999803659496453565495409 749852744622340174121557)
                      ·
                        rfl

theorem cell23_1460333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_1460333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460333 prefixEnd_1460333 := by exact prefixLift 1460333
  have htrace : WordTrace (prefixWord ++ tailWord_1460333) baseStart_1460333 baseEnd_1460333 := by
    simpa [prefixWord, tailWord_1460333, baseEnd_1460333] using wordTrace_append hprefix tailTrace_1460333
  have hstable : (prefixWord ++ tailWord_1460333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460333).length < 2 ^ (prefixWord ++ tailWord_1460333).sum := by decide
  have hdescent : baseEnd_1460333 < baseStart_1460333 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460356 : List Nat := [2, 3, 2, 1, 2, 1, 1, 6, 5]
def baseStart_1460356 : Nat := 118140960795 + 1460356 * 2 ^ 59
def prefixEnd_1460356 : Nat := 4983230072969 + 3 ^ 40 * 1460356 * 2
def baseEnd_1460356 : Nat := 83318283853043731570439

theorem tailTrace_1460356 : CollatzResearch.WordTrace tailWord_1460356 prefixEnd_1460356 83318283853043731570439 := by
  unfold tailWord_1460356
  simp only [CollatzResearch.WordTrace]
  refine ⟨26631779548693547896724461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35509039398258063862299281 26631779548693547896724461)
  ·
    refine ⟨9986917330760080461271673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26631779548693547896724461 9986917330760080461271673)
    ·
      refine ⟨7490187998070060345953755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9986917330760080461271673 7490187998070060345953755)
      ·
        refine ⟨11235281997105090518930633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7490187998070060345953755 11235281997105090518930633)
        ·
          refine ⟨8426461497828817889197975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11235281997105090518930633 8426461497828817889197975)
          ·
            refine ⟨12639692246743226833796963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8426461497828817889197975 12639692246743226833796963)
            ·
              refine ⟨18959538370114840250695445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12639692246743226833796963 18959538370114840250695445)
              ·
                refine ⟨888728361099133136751349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18959538370114840250695445 888728361099133136751349)
                ·
                  refine ⟨83318283853043731570439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 888728361099133136751349 83318283853043731570439)
                  ·
                    rfl

theorem cell23_1460356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 1, 1, 6, 5].length) (baseStart_1460356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460356 prefixEnd_1460356 := by exact prefixLift 1460356
  have htrace : WordTrace (prefixWord ++ tailWord_1460356) baseStart_1460356 baseEnd_1460356 := by
    simpa [prefixWord, tailWord_1460356, baseEnd_1460356] using wordTrace_append hprefix tailTrace_1460356
  have hstable : (prefixWord ++ tailWord_1460356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460356).length < 2 ^ (prefixWord ++ tailWord_1460356).sum := by decide
  have hdescent : baseEnd_1460356 < baseStart_1460356 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460386 : List Nat := [3, 3, 1, 3, 1, 1, 2, 1, 1, 7]
def baseStart_1460386 : Nat := 118140960795 + 1460386 * 2 ^ 59
def prefixEnd_1460386 : Nat := 4983230072969 + 3 ^ 40 * 1460386 * 2
def baseEnd_1460386 : Nat := 249959986365676155586271

theorem tailTrace_1460386 : CollatzResearch.WordTrace tailWord_1460386 prefixEnd_1460386 249959986365676155586271 := by
  unfold tailWord_1460386
  simp only [CollatzResearch.WordTrace]
  refine ⟨13316163321819602729260253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35509768858185607278027341 13316163321819602729260253)
  ·
    refine ⟨4993561245682351023472595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13316163321819602729260253 4993561245682351023472595)
    ·
      refine ⟨7490341868523526535208893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4993561245682351023472595 7490341868523526535208893)
      ·
        refine ⟨2808878200696322450703335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7490341868523526535208893 2808878200696322450703335)
        ·
          refine ⟨4213317301044483676055003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2808878200696322450703335 4213317301044483676055003)
          ·
            refine ⟨6319975951566725514082505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4213317301044483676055003 6319975951566725514082505)
            ·
              refine ⟨4739981963675044135561879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6319975951566725514082505 4739981963675044135561879)
              ·
                refine ⟨7109972945512566203342819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4739981963675044135561879 7109972945512566203342819)
                ·
                  refine ⟨10664959418268849305014229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7109972945512566203342819 10664959418268849305014229)
                  ·
                    refine ⟨249959986365676155586271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 10664959418268849305014229 249959986365676155586271)
                    ·
                      rfl

theorem cell23_1460386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 2, 1, 1, 7].length) (baseStart_1460386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460386 prefixEnd_1460386 := by exact prefixLift 1460386
  have htrace : WordTrace (prefixWord ++ tailWord_1460386) baseStart_1460386 baseEnd_1460386 := by
    simpa [prefixWord, tailWord_1460386, baseEnd_1460386] using wordTrace_append hprefix tailTrace_1460386
  have hstable : (prefixWord ++ tailWord_1460386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460386).length < 2 ^ (prefixWord ++ tailWord_1460386).sum := by decide
  have hdescent : baseEnd_1460386 < baseStart_1460386 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460389 : List Nat := [1, 3, 1, 2, 1, 3, 1, 3, 1, 3, 4]
def baseStart_1460389 : Nat := 118140960795 + 1460389 * 2 ^ 59
def prefixEnd_1460389 : Nat := 4983230072969 + 3 ^ 40 * 1460389 * 2
def baseEnd_1460389 : Nat := 749881499538991955021299

theorem tailTrace_1460389 : CollatzResearch.WordTrace tailWord_1460389 prefixEnd_1460389 749881499538991955021299 := by
  unfold tailWord_1460389
  simp only [CollatzResearch.WordTrace]
  refine ⟨53264762706267542429400221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35509841804178361619600147 53264762706267542429400221)
  ·
    refine ⟨19974286014850328411025083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53264762706267542429400221 19974286014850328411025083)
    ·
      refine ⟨29961429022275492616537625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19974286014850328411025083 29961429022275492616537625)
      ·
        refine ⟨22471071766706619462403219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29961429022275492616537625 22471071766706619462403219)
        ·
          refine ⟨33706607650059929193604829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22471071766706619462403219 33706607650059929193604829)
          ·
            refine ⟨12639977868772473447601811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33706607650059929193604829 12639977868772473447601811)
            ·
              refine ⟨18959966803158710171402717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12639977868772473447601811 18959966803158710171402717)
              ·
                refine ⟨7109987551184516314276019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18959966803158710171402717 7109987551184516314276019)
                ·
                  refine ⟨10664981326776774471414029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7109987551184516314276019 10664981326776774471414029)
                  ·
                    refine ⟨3999367997541290426780261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10664981326776774471414029 3999367997541290426780261)
                    ·
                      refine ⟨749881499538991955021299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3999367997541290426780261 749881499538991955021299)
                      ·
                        rfl

theorem cell23_1460389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 3, 1, 3, 4].length) (baseStart_1460389 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460389 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460389 prefixEnd_1460389 := by exact prefixLift 1460389
  have htrace : WordTrace (prefixWord ++ tailWord_1460389) baseStart_1460389 baseEnd_1460389 := by
    simpa [prefixWord, tailWord_1460389, baseEnd_1460389] using wordTrace_append hprefix tailTrace_1460389
  have hstable : (prefixWord ++ tailWord_1460389).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460389).length < 2 ^ (prefixWord ++ tailWord_1460389).sum := by decide
  have hdescent : baseEnd_1460389 < baseStart_1460389 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460426 : List Nat := [3, 1, 2, 1, 3, 1, 1, 2, 4, 2, 3]
def baseStart_1460426 : Nat := 118140960795 + 1460426 * 2 ^ 59
def prefixEnd_1460426 : Nat := 4983230072969 + 3 ^ 40 * 1460426 * 2
def baseEnd_1460426 : Nat := 749900498323208310258629

theorem tailTrace_1460426 : CollatzResearch.WordTrace tailWord_1460426 prefixEnd_1460426 749900498323208310258629 := by
  unfold tailWord_1460426
  simp only [CollatzResearch.WordTrace]
  refine ⟨13316528051783374437124283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35510741471422331832331421 13316528051783374437124283)
  ·
    refine ⟨19974792077675061655686425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13316528051783374437124283 19974792077675061655686425)
    ·
      refine ⟨14981094058256296241764819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19974792077675061655686425 14981094058256296241764819)
      ·
        refine ⟨22471641087384444362647229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14981094058256296241764819 22471641087384444362647229)
        ·
          refine ⟨8426865407769166635992711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22471641087384444362647229 8426865407769166635992711)
          ·
            refine ⟨12640298111653749953989067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8426865407769166635992711 12640298111653749953989067)
            ·
              refine ⟨18960447167480624930983601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12640298111653749953989067 18960447167480624930983601)
              ·
                refine ⟨14220335375610468698237701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18960447167480624930983601 14220335375610468698237701)
                ·
                  refine ⟨2666312882926962880919569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 14220335375610468698237701 2666312882926962880919569)
                  ·
                    refine ⟨1999734662195222160689677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2666312882926962880919569 1999734662195222160689677)
                    ·
                      refine ⟨749900498323208310258629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1999734662195222160689677 749900498323208310258629)
                      ·
                        rfl

theorem cell23_1460426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 1, 2, 4, 2, 3].length) (baseStart_1460426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460426 prefixEnd_1460426 := by exact prefixLift 1460426
  have htrace : WordTrace (prefixWord ++ tailWord_1460426) baseStart_1460426 baseEnd_1460426 := by
    simpa [prefixWord, tailWord_1460426, baseEnd_1460426] using wordTrace_append hprefix tailTrace_1460426
  have hstable : (prefixWord ++ tailWord_1460426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460426).length < 2 ^ (prefixWord ++ tailWord_1460426).sum := by decide
  have hdescent : baseEnd_1460426 < baseStart_1460426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460476 : List Nat := [2, 2, 2, 1, 4, 1, 1, 2, 3, 5]
def baseStart_1460476 : Nat := 118140960795 + 1460476 * 2 ^ 59
def prefixEnd_1460476 : Nat := 4983230072969 + 3 ^ 40 * 1460476 * 2
def baseEnd_1460476 : Nat := 249975390785311038211133

theorem tailTrace_1460476 : CollatzResearch.WordTrace tailWord_1460476 prefixEnd_1460476 249975390785311038211133 := by
  unfold tailWord_1460476
  simp only [CollatzResearch.WordTrace]
  refine ⟨26633967928476178143908641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35511957237968237525211521 26633967928476178143908641)
  ·
    refine ⟨19975475946357133607931481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26633967928476178143908641 19975475946357133607931481)
    ·
      refine ⟨14981606959767850205948611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19975475946357133607931481 14981606959767850205948611)
      ·
        refine ⟨22472410439651775308922917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14981606959767850205948611 22472410439651775308922917)
        ·
          refine ⟨4213576957434707870423047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22472410439651775308922917 4213576957434707870423047)
          ·
            refine ⟨6320365436152061805634571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4213576957434707870423047 6320365436152061805634571)
            ·
              refine ⟨9480548154228092708451857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6320365436152061805634571 9480548154228092708451857)
              ·
                refine ⟨7110411115671069531338893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9480548154228092708451857 7110411115671069531338893)
                ·
                  refine ⟨2666404168376651074252085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7110411115671069531338893 2666404168376651074252085)
                  ·
                    refine ⟨249975390785311038211133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2666404168376651074252085 249975390785311038211133)
                    ·
                      rfl

theorem cell23_1460476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 2, 3, 5].length) (baseStart_1460476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460476 prefixEnd_1460476 := by exact prefixLift 1460476
  have htrace : WordTrace (prefixWord ++ tailWord_1460476) baseStart_1460476 baseEnd_1460476 := by
    simpa [prefixWord, tailWord_1460476, baseEnd_1460476] using wordTrace_append hprefix tailTrace_1460476
  have hstable : (prefixWord ++ tailWord_1460476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460476).length < 2 ^ (prefixWord ++ tailWord_1460476).sum := by decide
  have hdescent : baseEnd_1460476 < baseStart_1460476 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460540 : List Nat := [2, 2, 2, 2, 1, 2, 5, 1, 2, 4]
def baseStart_1460540 : Nat := 118140960795 + 1460540 * 2 ^ 59
def prefixEnd_1460540 : Nat := 4983230072969 + 3 ^ 40 * 1460540 * 2
def baseEnd_1460540 : Nat := 249986345039273621411035

theorem tailTrace_1460540 : CollatzResearch.WordTrace tailWord_1460540 prefixEnd_1460540 249986345039273621411035 := by
  unfold tailWord_1460540
  simp only [CollatzResearch.WordTrace]
  refine ⟨26635135064360247609073537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35513513419146996812098049 26635135064360247609073537)
  ·
    refine ⟨19976351298270185706805153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26635135064360247609073537 19976351298270185706805153)
    ·
      refine ⟨14982263473702639280103865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19976351298270185706805153 14982263473702639280103865)
      ·
        refine ⟨11236697605276979460077899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14982263473702639280103865 11236697605276979460077899)
        ·
          refine ⟨16855046407915469190116849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11236697605276979460077899 16855046407915469190116849)
          ·
            refine ⟨12641284805936601892587637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16855046407915469190116849 12641284805936601892587637)
            ·
              refine ⟨1185120450556556427430091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12641284805936601892587637 1185120450556556427430091)
              ·
                refine ⟨1777680675834834641145137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1185120450556556427430091 1777680675834834641145137)
                ·
                  refine ⟨1333260506876125980858853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1777680675834834641145137 1333260506876125980858853)
                  ·
                    refine ⟨249986345039273621411035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1333260506876125980858853 249986345039273621411035)
                    ·
                      rfl

theorem cell23_1460540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 5, 1, 2, 4].length) (baseStart_1460540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460540 prefixEnd_1460540 := by exact prefixLift 1460540
  have htrace : WordTrace (prefixWord ++ tailWord_1460540) baseStart_1460540 baseEnd_1460540 := by
    simpa [prefixWord, tailWord_1460540, baseEnd_1460540] using wordTrace_append hprefix tailTrace_1460540
  have hstable : (prefixWord ++ tailWord_1460540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460540).length < 2 ^ (prefixWord ++ tailWord_1460540).sum := by decide
  have hdescent : baseEnd_1460540 < baseStart_1460540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460564 : List Nat := [2, 4, 1, 1, 2, 2, 3, 3, 1, 2, 2]
def baseStart_1460564 : Nat := 118140960795 + 1460564 * 2 ^ 59
def prefixEnd_1460564 : Nat := 4983230072969 + 3 ^ 40 * 1460564 * 2
def baseEnd_1460564 : Nat := 749971358653528770332995

theorem tailTrace_1460564 : CollatzResearch.WordTrace tailWord_1460564 prefixEnd_1460564 749971358653528770332995 := by
  unfold tailWord_1460564
  simp only [CollatzResearch.WordTrace]
  refine ⟨26635572740316773658510373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35514096987089031544680497 26635572740316773658510373)
  ·
    refine ⟨4994169888809395060970695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26635572740316773658510373 4994169888809395060970695)
    ·
      refine ⟨7491254833214092591456043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4994169888809395060970695 7491254833214092591456043)
      ·
        refine ⟨11236882249821138887184065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7491254833214092591456043 11236882249821138887184065)
        ·
          refine ⟨8427661687365854165388049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11236882249821138887184065 8427661687365854165388049)
          ·
            refine ⟨6320746265524390624041037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8427661687365854165388049 6320746265524390624041037)
            ·
              refine ⟨2370279849571646484015389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6320746265524390624041037 2370279849571646484015389)
              ·
                refine ⟨888854943589367431505771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2370279849571646484015389 888854943589367431505771)
                ·
                  refine ⟨1333282415384051147258657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 888854943589367431505771 1333282415384051147258657)
                  ·
                    refine ⟨999961811538038360443993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1333282415384051147258657 999961811538038360443993)
                    ·
                      refine ⟨749971358653528770332995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 999961811538038360443993 749971358653528770332995)
                      ·
                        rfl

theorem cell23_1460564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 3, 1, 2, 2].length) (baseStart_1460564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460564 prefixEnd_1460564 := by exact prefixLift 1460564
  have htrace : WordTrace (prefixWord ++ tailWord_1460564) baseStart_1460564 baseEnd_1460564 := by
    simpa [prefixWord, tailWord_1460564, baseEnd_1460564] using wordTrace_append hprefix tailTrace_1460564
  have hstable : (prefixWord ++ tailWord_1460564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460564).length < 2 ^ (prefixWord ++ tailWord_1460564).sum := by decide
  have hdescent : baseEnd_1460564 < baseStart_1460564 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460580 : List Nat := [2, 3, 1, 1, 3, 1, 2, 4, 2, 1, 3]
def baseStart_1460580 : Nat := 118140960795 + 1460580 * 2 ^ 59
def prefixEnd_1460580 : Nat := 4983230072969 + 3 ^ 40 * 1460580 * 2
def baseEnd_1460580 : Nat := 749979574344000707732921

theorem tailTrace_1460580 : CollatzResearch.WordTrace tailWord_1460580 prefixEnd_1460580 749979574344000707732921 := by
  unfold tailWord_1460580
  simp only [CollatzResearch.WordTrace]
  refine ⟨26635864524287791024801597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35514486032383721366402129 26635864524287791024801597)
  ·
    refine ⟨9988449196607921634300599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26635864524287791024801597 9988449196607921634300599)
    ·
      refine ⟨14982673794911882451450899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9988449196607921634300599 14982673794911882451450899)
      ·
        refine ⟨22474010692367823677176349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14982673794911882451450899 22474010692367823677176349)
        ·
          refine ⟨8427754009637933878941131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22474010692367823677176349 8427754009637933878941131)
          ·
            refine ⟨12641631014456900818411697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8427754009637933878941131 12641631014456900818411697)
            ·
              refine ⟨9481223260842675613808773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12641631014456900818411697 9481223260842675613808773)
              ·
                refine ⟨1777729361408001677589145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9481223260842675613808773 1777729361408001677589145)
                ·
                  refine ⟨1333297021056001258191859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1777729361408001677589145 1333297021056001258191859)
                  ·
                    refine ⟨1999945531584001887287789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1333297021056001258191859 1999945531584001887287789)
                    ·
                      refine ⟨749979574344000707732921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1999945531584001887287789 749979574344000707732921)
                      ·
                        rfl

theorem cell23_1460580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 2, 4, 2, 1, 3].length) (baseStart_1460580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460580 prefixEnd_1460580 := by exact prefixLift 1460580
  have htrace : WordTrace (prefixWord ++ tailWord_1460580) baseStart_1460580 baseEnd_1460580 := by
    simpa [prefixWord, tailWord_1460580, baseEnd_1460580] using wordTrace_append hprefix tailTrace_1460580
  have hstable : (prefixWord ++ tailWord_1460580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460580).length < 2 ^ (prefixWord ++ tailWord_1460580).sum := by decide
  have hdescent : baseEnd_1460580 < baseStart_1460580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460597 : List Nat := [1, 3, 4, 1, 2, 2, 1, 3, 2, 1, 3]
def baseStart_1460597 : Nat := 118140960795 + 1460597 * 2 ^ 59
def prefixEnd_1460597 : Nat := 4983230072969 + 3 ^ 40 * 1460597 * 2
def baseEnd_1460597 : Nat := 749988303515127141220343

theorem tailTrace_1460597 : CollatzResearch.WordTrace tailWord_1460597 prefixEnd_1460597 749988303515127141220343 := by
  unfold tailWord_1460597
  simp only [CollatzResearch.WordTrace]
  refine ⟨53272349089513993952972045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35514899393009329301981363 53272349089513993952972045)
  ·
    refine ⟨19977130908567747732364517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53272349089513993952972045 19977130908567747732364517)
    ·
      refine ⟨3745712045356452699818347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19977130908567747732364517 3745712045356452699818347)
      ·
        refine ⟨5618568068034679049727521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3745712045356452699818347 5618568068034679049727521)
        ·
          refine ⟨4213926051026009287295641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5618568068034679049727521 4213926051026009287295641)
          ·
            refine ⟨3160444538269506965471731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4213926051026009287295641 3160444538269506965471731)
            ·
              refine ⟨4740666807404260448207597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3160444538269506965471731 4740666807404260448207597)
              ·
                refine ⟨1777750052776597668077849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4740666807404260448207597 1777750052776597668077849)
                ·
                  refine ⟨1333312539582448251058387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1777750052776597668077849 1333312539582448251058387)
                  ·
                    refine ⟨1999968809373672376587581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1333312539582448251058387 1999968809373672376587581)
                    ·
                      refine ⟨749988303515127141220343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1999968809373672376587581 749988303515127141220343)
                      ·
                        rfl

theorem cell23_1460597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_1460597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460597 prefixEnd_1460597 := by exact prefixLift 1460597
  have htrace : WordTrace (prefixWord ++ tailWord_1460597) baseStart_1460597 baseEnd_1460597 := by
    simpa [prefixWord, tailWord_1460597, baseEnd_1460597] using wordTrace_append hprefix tailTrace_1460597
  have hstable : (prefixWord ++ tailWord_1460597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460597).length < 2 ^ (prefixWord ++ tailWord_1460597).sum := by decide
  have hdescent : baseEnd_1460597 < baseStart_1460597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460620 : List Nat := [2, 2, 1, 2, 1, 5, 1, 2, 1, 4, 2]
def baseStart_1460620 : Nat := 118140960795 + 1460620 * 2 ^ 59
def prefixEnd_1460620 : Nat := 4983230072969 + 3 ^ 40 * 1460620 * 2
def baseEnd_1460620 : Nat := 750000113570180551232737

theorem tailTrace_1460620 : CollatzResearch.WordTrace tailWord_1460620 prefixEnd_1460620 750000113570180551232737 := by
  unfold tailWord_1460620
  simp only [CollatzResearch.WordTrace]
  refine ⟨26636593984215334440529657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35515458645620445920706209 26636593984215334440529657)
  ·
    refine ⟨19977445488161500830397243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26636593984215334440529657 19977445488161500830397243)
    ·
      refine ⟨29966168232242251245595865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19977445488161500830397243 29966168232242251245595865)
      ·
        refine ⟨22474626174181688434196899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29966168232242251245595865 22474626174181688434196899)
        ·
          refine ⟨33711939261272532651295349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22474626174181688434196899 33711939261272532651295349)
          ·
            refine ⟨3160494305744299936058939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 33711939261272532651295349 3160494305744299936058939)
            ·
              refine ⟨4740741458616449904088409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3160494305744299936058939 4740741458616449904088409)
              ·
                refine ⟨3555556093962337428066307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4740741458616449904088409 3555556093962337428066307)
                ·
                  refine ⟨5333334140943506142099461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3555556093962337428066307 5333334140943506142099461)
                  ·
                    refine ⟨1000000151426907401643649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5333334140943506142099461 1000000151426907401643649)
                    ·
                      refine ⟨750000113570180551232737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1000000151426907401643649 750000113570180551232737)
                      ·
                        rfl

theorem cell23_1460620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 1, 2, 1, 4, 2].length) (baseStart_1460620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460620 prefixEnd_1460620 := by exact prefixLift 1460620
  have htrace : WordTrace (prefixWord ++ tailWord_1460620) baseStart_1460620 baseEnd_1460620 := by
    simpa [prefixWord, tailWord_1460620, baseEnd_1460620] using wordTrace_append hprefix tailTrace_1460620
  have hstable : (prefixWord ++ tailWord_1460620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460620).length < 2 ^ (prefixWord ++ tailWord_1460620).sum := by decide
  have hdescent : baseEnd_1460620 < baseStart_1460620 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460666 : List Nat := [3, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7]
def baseStart_1460666 : Nat := 118140960795 + 1460666 * 2 ^ 59
def prefixEnd_1460666 : Nat := 4983230072969 + 3 ^ 40 * 1460666 * 2
def baseEnd_1460666 : Nat := 750023733680287371257525

theorem tailTrace_1460666 : CollatzResearch.WordTrace tailWord_1460666 prefixEnd_1460666 750023733680287371257525 := by
  unfold tailWord_1460666
  simp only [CollatzResearch.WordTrace]
  refine ⟨13318716431566004684308463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35516577150842679158155901 13318716431566004684308463)
  ·
    refine ⟨19978074647349007026462695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13318716431566004684308463 19978074647349007026462695)
    ·
      refine ⟨29967111971023510539694043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19978074647349007026462695 29967111971023510539694043)
      ·
        refine ⟨44950667956535265809541065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29967111971023510539694043 44950667956535265809541065)
        ·
          refine ⟨33713000967401449357155799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44950667956535265809541065 33713000967401449357155799)
          ·
            refine ⟨50569501451102174035733699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33713000967401449357155799 50569501451102174035733699)
            ·
              refine ⟨75854252176653261053600549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50569501451102174035733699 75854252176653261053600549)
              ·
                refine ⟨14222672283122486447550103, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 75854252176653261053600549 14222672283122486447550103)
                ·
                  refine ⟨21334008424683729671325155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14222672283122486447550103 21334008424683729671325155)
                  ·
                    refine ⟨32001012637025594506987733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21334008424683729671325155 32001012637025594506987733)
                    ·
                      refine ⟨750023733680287371257525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 32001012637025594506987733 750023733680287371257525)
                      ·
                        rfl

theorem cell23_1460666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_1460666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460666 prefixEnd_1460666 := by exact prefixLift 1460666
  have htrace : WordTrace (prefixWord ++ tailWord_1460666) baseStart_1460666 baseEnd_1460666 := by
    simpa [prefixWord, tailWord_1460666, baseEnd_1460666] using wordTrace_append hprefix tailTrace_1460666
  have hstable : (prefixWord ++ tailWord_1460666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460666).length < 2 ^ (prefixWord ++ tailWord_1460666).sum := by decide
  have hdescent : baseEnd_1460666 < baseStart_1460666 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460713 : List Nat := [1, 2, 1, 1, 1, 2, 1, 3, 6, 2, 3]
def baseStart_1460713 : Nat := 118140960795 + 1460713 * 2 ^ 59
def prefixEnd_1460713 : Nat := 4983230072969 + 3 ^ 40 * 1460713 * 2
def baseEnd_1460713 : Nat := 750047867271048687369809

theorem tailTrace_1460713 : CollatzResearch.WordTrace tailWord_1460713 prefixEnd_1460713 750047867271048687369809 := by
  unfold tailWord_1460713
  simp only [CollatzResearch.WordTrace]
  refine ⟨53276579957093745764194793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35517719971395830509463195 53276579957093745764194793)
  ·
    refine ⟨39957434967820309323146095, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53276579957093745764194793 39957434967820309323146095)
    ·
      refine ⟨59936152451730463984719143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39957434967820309323146095 59936152451730463984719143)
      ·
        refine ⟨89904228677595695977078715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59936152451730463984719143 89904228677595695977078715)
        ·
          refine ⟨134856343016393543965618073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89904228677595695977078715 134856343016393543965618073)
          ·
            refine ⟨101142257262295157974213555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 134856343016393543965618073 101142257262295157974213555)
            ·
              refine ⟨151713385893442736961320333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101142257262295157974213555 151713385893442736961320333)
              ·
                refine ⟨56892519710041026360495125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151713385893442736961320333 56892519710041026360495125)
                ·
                  refine ⟨2666836861408173110648209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 56892519710041026360495125 2666836861408173110648209)
                  ·
                    refine ⟨2000127646056129832986157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2666836861408173110648209 2000127646056129832986157)
                    ·
                      refine ⟨750047867271048687369809, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2000127646056129832986157 750047867271048687369809)
                      ·
                        rfl

theorem cell23_1460713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 3, 6, 2, 3].length) (baseStart_1460713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460713 prefixEnd_1460713 := by exact prefixLift 1460713
  have htrace : WordTrace (prefixWord ++ tailWord_1460713) baseStart_1460713 baseEnd_1460713 := by
    simpa [prefixWord, tailWord_1460713, baseEnd_1460713] using wordTrace_append hprefix tailTrace_1460713
  have hstable : (prefixWord ++ tailWord_1460713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460713).length < 2 ^ (prefixWord ++ tailWord_1460713).sum := by decide
  have hdescent : baseEnd_1460713 < baseStart_1460713 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460787 : List Nat := [1, 1, 1, 2, 4, 2, 4, 1, 2, 3, 2]
def baseStart_1460787 : Nat := 118140960795 + 1460787 * 2 ^ 59
def prefixEnd_1460787 : Nat := 4983230072969 + 3 ^ 40 * 1460787 * 2
def baseEnd_1460787 : Nat := 750085864839481397844469

theorem tailTrace_1460787 : CollatzResearch.WordTrace tailWord_1460787 prefixEnd_1460787 750085864839481397844469 := by
  unfold tailWord_1460787
  simp only [CollatzResearch.WordTrace]
  refine ⟨53279278958825656402388615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35519519305883770934925743 53279278958825656402388615)
  ·
    refine ⟨79918918438238484603582923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53279278958825656402388615 79918918438238484603582923)
    ·
      refine ⟨119878377657357726905374385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79918918438238484603582923 119878377657357726905374385)
      ·
        refine ⟨89908783243018295179030789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119878377657357726905374385 89908783243018295179030789)
        ·
          refine ⟨16857896858065930346068273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 89908783243018295179030789 16857896858065930346068273)
          ·
            refine ⟨12643422643549447759551205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16857896858065930346068273 12643422643549447759551205)
            ·
              refine ⟨2370641745665521454915851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12643422643549447759551205 2370641745665521454915851)
              ·
                refine ⟨3555962618498282182373777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2370641745665521454915851 3555962618498282182373777)
                ·
                  refine ⟨2666971963873711636780333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3555962618498282182373777 2666971963873711636780333)
                  ·
                    refine ⟨1000114486452641863792625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2666971963873711636780333 1000114486452641863792625)
                    ·
                      refine ⟨750085864839481397844469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1000114486452641863792625 750085864839481397844469)
                      ·
                        rfl

theorem cell23_1460787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 4, 1, 2, 3, 2].length) (baseStart_1460787 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460787 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460787 prefixEnd_1460787 := by exact prefixLift 1460787
  have htrace : WordTrace (prefixWord ++ tailWord_1460787) baseStart_1460787 baseEnd_1460787 := by
    simpa [prefixWord, tailWord_1460787, baseEnd_1460787] using wordTrace_append hprefix tailTrace_1460787
  have hstable : (prefixWord ++ tailWord_1460787).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460787).length < 2 ^ (prefixWord ++ tailWord_1460787).sum := by decide
  have hdescent : baseEnd_1460787 < baseStart_1460787 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460800 : List Nat := [2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 4]
def baseStart_1460800 : Nat := 118140960795 + 1460800 * 2 ^ 59
def prefixEnd_1460800 : Nat := 4983230072969 + 3 ^ 40 * 1460800 * 2
def baseEnd_1460800 : Nat := 750092540087989846981909

theorem tailTrace_1460800 : CollatzResearch.WordTrace tailWord_1460800 prefixEnd_1460800 750092540087989846981909 := by
  unfold tailWord_1460800
  simp only [CollatzResearch.WordTrace]
  refine ⟨26639876553889279811305927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35519835405185706415074569 26639876553889279811305927)
  ·
    refine ⟨39959814830833919716958891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26639876553889279811305927 39959814830833919716958891)
    ·
      refine ⟨59939722246250879575438337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39959814830833919716958891 59939722246250879575438337)
      ·
        refine ⟨44954791684688159681578753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59939722246250879575438337 44954791684688159681578753)
        ·
          refine ⟨33716093763516119761184065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44954791684688159681578753 33716093763516119761184065)
          ·
            refine ⟨25287070322637089820888049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33716093763516119761184065 25287070322637089820888049)
            ·
              refine ⟨18965302741977817365666037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25287070322637089820888049 18965302741977817365666037)
              ·
                refine ⟨1777997132060420378031191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 18965302741977817365666037 1777997132060420378031191)
                ·
                  refine ⟨2666995698090630567046787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1777997132060420378031191 2666995698090630567046787)
                  ·
                    refine ⟨4000493547135945850570181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2666995698090630567046787 4000493547135945850570181)
                    ·
                      refine ⟨750092540087989846981909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 4000493547135945850570181 750092540087989846981909)
                      ·
                        rfl

theorem cell23_1460800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 2, 5, 1, 1, 4].length) (baseStart_1460800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460800 prefixEnd_1460800 := by exact prefixLift 1460800
  have htrace : WordTrace (prefixWord ++ tailWord_1460800) baseStart_1460800 baseEnd_1460800 := by
    simpa [prefixWord, tailWord_1460800, baseEnd_1460800] using wordTrace_append hprefix tailTrace_1460800
  have hstable : (prefixWord ++ tailWord_1460800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460800).length < 2 ^ (prefixWord ++ tailWord_1460800).sum := by decide
  have hdescent : baseEnd_1460800 < baseStart_1460800 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460861 : List Nat := [1, 4, 1, 1, 6, 1, 1, 2, 2, 4]
def baseStart_1460861 : Nat := 118140960795 + 1460861 * 2 ^ 59
def prefixEnd_1460861 : Nat := 4983230072969 + 3 ^ 40 * 1460861 * 2
def baseEnd_1460861 : Nat := 250041287469304702773043

theorem tailTrace_1460861 : CollatzResearch.WordTrace tailWord_1460861 prefixEnd_1460861 250041287469304702773043 := by
  unfold tailWord_1460861
  simp only [CollatzResearch.WordTrace]
  refine ⟨53281977960557567040582437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35521318640371711360388291 53281977960557567040582437)
  ·
    refine ⟨9990370867604543820109207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53281977960557567040582437 9990370867604543820109207)
    ·
      refine ⟨14985556301406815730163811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9990370867604543820109207 14985556301406815730163811)
      ·
        refine ⟨22478334452110223595245717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14985556301406815730163811 22478334452110223595245717)
        ·
          refine ⟨1053671927442666731027143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 22478334452110223595245717 1053671927442666731027143)
          ·
            refine ⟨1580507891164000096540715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1053671927442666731027143 1580507891164000096540715)
            ·
              refine ⟨2370761836746000144811073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1580507891164000096540715 2370761836746000144811073)
              ·
                refine ⟨1778071377559500108608305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2370761836746000144811073 1778071377559500108608305)
                ·
                  refine ⟨1333553533169625081456229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1778071377559500108608305 1333553533169625081456229)
                  ·
                    refine ⟨250041287469304702773043, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1333553533169625081456229 250041287469304702773043)
                    ·
                      rfl

theorem cell23_1460861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 6, 1, 1, 2, 2, 4].length) (baseStart_1460861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460861 prefixEnd_1460861 := by exact prefixLift 1460861
  have htrace : WordTrace (prefixWord ++ tailWord_1460861) baseStart_1460861 baseEnd_1460861 := by
    simpa [prefixWord, tailWord_1460861, baseEnd_1460861] using wordTrace_append hprefix tailTrace_1460861
  have hstable : (prefixWord ++ tailWord_1460861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460861).length < 2 ^ (prefixWord ++ tailWord_1460861).sum := by decide
  have hdescent : baseEnd_1460861 < baseStart_1460861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460863 : List Nat := [1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 5]
def baseStart_1460863 : Nat := 118140960795 + 1460863 * 2 ^ 59
def prefixEnd_1460863 : Nat := 4983230072969 + 3 ^ 40 * 1460863 * 2
def baseEnd_1460863 : Nat := 750124889369223100494119

theorem tailTrace_1460863 : CollatzResearch.WordTrace tailWord_1460863 prefixEnd_1460863 750124889369223100494119 := by
  unfold tailWord_1460863
  simp only [CollatzResearch.WordTrace]
  refine ⟨53282050906550321382155243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35521367271033547588103495 53282050906550321382155243)
  ·
    refine ⟨79923076359825482073232865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53282050906550321382155243 79923076359825482073232865)
    ·
      refine ⟨59942307269869111554924649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79923076359825482073232865 59942307269869111554924649)
      ·
        refine ⟨44956730452401833666193487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59942307269869111554924649 44956730452401833666193487)
        ·
          refine ⟨67435095678602750499290231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44956730452401833666193487 67435095678602750499290231)
          ·
            refine ⟨101152643517904125748935347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67435095678602750499290231 101152643517904125748935347)
            ·
              refine ⟨151728965276856188623403021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101152643517904125748935347 151728965276856188623403021)
              ·
                refine ⟨56898361978821070733776133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 151728965276856188623403021 56898361978821070733776133)
                ·
                  refine ⟨10668442871028950762583025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 56898361978821070733776133 10668442871028950762583025)
                  ·
                    refine ⟨8001332153271713071937269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10668442871028950762583025 8001332153271713071937269)
                    ·
                      refine ⟨750124889369223100494119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8001332153271713071937269 750124889369223100494119)
                      ·
                        rfl

theorem cell23_1460863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_1460863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460863 prefixEnd_1460863 := by exact prefixLift 1460863
  have htrace : WordTrace (prefixWord ++ tailWord_1460863) baseStart_1460863 baseEnd_1460863 := by
    simpa [prefixWord, tailWord_1460863, baseEnd_1460863] using wordTrace_append hprefix tailTrace_1460863
  have hstable : (prefixWord ++ tailWord_1460863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460863).length < 2 ^ (prefixWord ++ tailWord_1460863).sum := by decide
  have hdescent : baseEnd_1460863 < baseStart_1460863 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460884 : List Nat := [2, 4, 2, 2, 1, 1, 3, 1, 1, 3, 3]
def baseStart_1460884 : Nat := 118140960795 + 1460884 * 2 ^ 59
def prefixEnd_1460884 : Nat := 4983230072969 + 3 ^ 40 * 1460884 * 2
def baseEnd_1460884 : Nat := 750135672462967518331523

theorem tailTrace_1460884 : CollatzResearch.WordTrace tailWord_1460884 prefixEnd_1460884 750135672462967518331523 := by
  unfold tailWord_1460884
  simp only [CollatzResearch.WordTrace]
  refine ⟨26641408419737120984334853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35521877892982827979113137 26641408419737120984334853)
  ·
    refine ⟨4995264078700710184562785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26641408419737120984334853 4995264078700710184562785)
    ·
      refine ⟨3746448059025532638422089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4995264078700710184562785 3746448059025532638422089)
      ·
        refine ⟨2809836044269149478816567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3746448059025532638422089 2809836044269149478816567)
        ·
          refine ⟨4214754066403724218224851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2809836044269149478816567 4214754066403724218224851)
          ·
            refine ⟨6322131099605586327337277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4214754066403724218224851 6322131099605586327337277)
            ·
              refine ⟨2370799162352094872751479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6322131099605586327337277 2370799162352094872751479)
              ·
                refine ⟨3556198743528142309127219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2370799162352094872751479 3556198743528142309127219)
                ·
                  refine ⟨5334298115292213463690829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3556198743528142309127219 5334298115292213463690829)
                  ·
                    refine ⟨2000361793234580048884061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 5334298115292213463690829 2000361793234580048884061)
                    ·
                      refine ⟨750135672462967518331523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2000361793234580048884061 750135672462967518331523)
                      ·
                        rfl

theorem cell23_1460884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_1460884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460884 prefixEnd_1460884 := by exact prefixLift 1460884
  have htrace : WordTrace (prefixWord ++ tailWord_1460884) baseStart_1460884 baseEnd_1460884 := by
    simpa [prefixWord, tailWord_1460884, baseEnd_1460884] using wordTrace_append hprefix tailTrace_1460884
  have hstable : (prefixWord ++ tailWord_1460884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460884).length < 2 ^ (prefixWord ++ tailWord_1460884).sum := by decide
  have hdescent : baseEnd_1460884 < baseStart_1460884 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1460924 : List Nat := [2, 2, 2, 3, 1, 1, 1, 3, 4, 2, 2]
def baseStart_1460924 : Nat := 118140960795 + 1460924 * 2 ^ 59
def prefixEnd_1460924 : Nat := 4983230072969 + 3 ^ 40 * 1460924 * 2
def baseEnd_1460924 : Nat := 750156211689147361831339

theorem tailTrace_1460924 : CollatzResearch.WordTrace tailWord_1460924 prefixEnd_1460924 750156211689147361831339 := by
  unfold tailWord_1460924
  simp only [CollatzResearch.WordTrace]
  refine ⟨26642137879664664400062913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35522850506219552533417217 26642137879664664400062913)
  ·
    refine ⟨19981603409748498300047185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26642137879664664400062913 19981603409748498300047185)
    ·
      refine ⟨14986202557311373725035389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19981603409748498300047185 14986202557311373725035389)
      ·
        refine ⟨5619825958991765146888271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14986202557311373725035389 5619825958991765146888271)
        ·
          refine ⟨8429738938487647720332407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5619825958991765146888271 8429738938487647720332407)
          ·
            refine ⟨12644608407731471580498611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8429738938487647720332407 12644608407731471580498611)
            ·
              refine ⟨18966912611597207370747917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12644608407731471580498611 18966912611597207370747917)
              ·
                refine ⟨7112592229348952764030469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18966912611597207370747917 7112592229348952764030469)
                ·
                  refine ⟨1333611043002928643255713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 7112592229348952764030469 1333611043002928643255713)
                  ·
                    refine ⟨1000208282252196482441785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1333611043002928643255713 1000208282252196482441785)
                    ·
                      refine ⟨750156211689147361831339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1000208282252196482441785 750156211689147361831339)
                      ·
                        rfl

theorem cell23_1460924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 1, 3, 4, 2, 2].length) (baseStart_1460924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1460924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1460924 prefixEnd_1460924 := by exact prefixLift 1460924
  have htrace : WordTrace (prefixWord ++ tailWord_1460924) baseStart_1460924 baseEnd_1460924 := by
    simpa [prefixWord, tailWord_1460924, baseEnd_1460924] using wordTrace_append hprefix tailTrace_1460924
  have hstable : (prefixWord ++ tailWord_1460924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1460924).length < 2 ^ (prefixWord ++ tailWord_1460924).sum := by decide
  have hdescent : baseEnd_1460924 < baseStart_1460924 := by decide
  rcases family_descends (prefixWord ++ tailWord_1460924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461007 : List Nat := [1, 1, 2, 1, 1, 1, 7, 2, 3, 4]
def baseStart_1461007 : Nat := 118140960795 + 1461007 * 2 ^ 59
def prefixEnd_1461007 : Nat := 4983230072969 + 3 ^ 40 * 1461007 * 2
def baseEnd_1461007 : Nat := 250066276861156845697819

theorem tailTrace_1461007 : CollatzResearch.WordTrace tailWord_1461007 prefixEnd_1461007 250066276861156845697819 := by
  unfold tailWord_1461007
  simp only [CollatzResearch.WordTrace]
  refine ⟨53287303018028633975397275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35524868678685755983598183 53287303018028633975397275)
  ·
    refine ⟨79930954527042950963095913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53287303018028633975397275 79930954527042950963095913)
    ·
      refine ⟨59948215895282213222321935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 79930954527042950963095913 59948215895282213222321935)
      ·
        refine ⟨89922323842923319833482903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 59948215895282213222321935 89922323842923319833482903)
        ·
          refine ⟨134883485764384979750224355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 89922323842923319833482903 134883485764384979750224355)
          ·
            refine ⟨202325228646577469625336533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 134883485764384979750224355 202325228646577469625336533)
            ·
              refine ⟨4741997546404159444343825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 202325228646577469625336533 4741997546404159444343825)
              ·
                refine ⟨3556498159803119583257869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4741997546404159444343825 3556498159803119583257869)
                ·
                  refine ⟨1333686809926169843721701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3556498159803119583257869 1333686809926169843721701)
                  ·
                    refine ⟨250066276861156845697819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1333686809926169843721701 250066276861156845697819)
                    ·
                      rfl

theorem cell23_1461007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 7, 2, 3, 4].length) (baseStart_1461007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461007 prefixEnd_1461007 := by exact prefixLift 1461007
  have htrace : WordTrace (prefixWord ++ tailWord_1461007) baseStart_1461007 baseEnd_1461007 := by
    simpa [prefixWord, tailWord_1461007, baseEnd_1461007] using wordTrace_append hprefix tailTrace_1461007
  have hstable : (prefixWord ++ tailWord_1461007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461007).length < 2 ^ (prefixWord ++ tailWord_1461007).sum := by decide
  have hdescent : baseEnd_1461007 < baseStart_1461007 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461017 : List Nat := [1, 2, 1, 2, 1, 1, 1, 7, 2, 2, 3]
def baseStart_1461017 : Nat := 118140960795 + 1461017 * 2 ^ 59
def prefixEnd_1461017 : Nat := 4983230072969 + 3 ^ 40 * 1461017 * 2
def baseEnd_1461017 : Nat := 750203965390015497968411

theorem tailTrace_1461017 : CollatzResearch.WordTrace tailWord_1461017 prefixEnd_1461017 750203965390015497968411 := by
  unfold tailWord_1461017
  simp only [CollatzResearch.WordTrace]
  refine ⟨53287667747992405683261305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35525111831994937122174203 53287667747992405683261305)
  ·
    refine ⟨39965750810994304262445979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53287667747992405683261305 39965750810994304262445979)
    ·
      refine ⟨59948626216491456393668969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 39965750810994304262445979 59948626216491456393668969)
      ·
        refine ⟨44961469662368592295251727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 59948626216491456393668969 44961469662368592295251727)
        ·
          refine ⟨67442204493552888442877591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44961469662368592295251727 67442204493552888442877591)
          ·
            refine ⟨101163306740329332664316387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67442204493552888442877591 101163306740329332664316387)
            ·
              refine ⟨151744960110493998996474581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101163306740329332664316387 151744960110493998996474581)
              ·
                refine ⟨3556522502589703101479873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 151744960110493998996474581 3556522502589703101479873)
                ·
                  refine ⟨2667391876942277326109905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3556522502589703101479873 2667391876942277326109905)
                  ·
                    refine ⟨2000543907706707994582429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2667391876942277326109905 2000543907706707994582429)
                    ·
                      refine ⟨750203965390015497968411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2000543907706707994582429 750203965390015497968411)
                      ·
                        rfl

theorem cell23_1461017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 1, 7, 2, 2, 3].length) (baseStart_1461017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461017 prefixEnd_1461017 := by exact prefixLift 1461017
  have htrace : WordTrace (prefixWord ++ tailWord_1461017) baseStart_1461017 baseEnd_1461017 := by
    simpa [prefixWord, tailWord_1461017, baseEnd_1461017] using wordTrace_append hprefix tailTrace_1461017
  have hstable : (prefixWord ++ tailWord_1461017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461017).length < 2 ^ (prefixWord ++ tailWord_1461017).sum := by decide
  have hdescent : baseEnd_1461017 < baseStart_1461017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461064 : List Nat := [2, 1, 3, 1, 1, 3, 1, 4, 3, 1, 3]
def baseStart_1461064 : Nat := 118140960795 + 1461064 * 2 ^ 59
def prefixEnd_1461064 : Nat := 4983230072969 + 3 ^ 40 * 1461064 * 2
def baseEnd_1461064 : Nat := 750228098980776814080695

theorem tailTrace_1461064 : CollatzResearch.WordTrace tailWord_1461064 prefixEnd_1461064 750228098980776814080695 := by
  unfold tailWord_1461064
  simp only [CollatzResearch.WordTrace]
  refine ⟨26644690989411066355111123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35526254652548088473481497 26644690989411066355111123)
  ·
    refine ⟨39967036484116599532666685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26644690989411066355111123 39967036484116599532666685)
    ·
      refine ⟨14987638681543724824750007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 39967036484116599532666685 14987638681543724824750007)
      ·
        refine ⟨22481458022315587237125011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14987638681543724824750007 22481458022315587237125011)
        ·
          refine ⟨33722187033473380855687517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22481458022315587237125011 33722187033473380855687517)
          ·
            refine ⟨12645820137552517820882819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33722187033473380855687517 12645820137552517820882819)
            ·
              refine ⟨18968730206328776731324229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12645820137552517820882819 18968730206328776731324229)
              ·
                refine ⟨3556636913686645637123293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 18968730206328776731324229 3556636913686645637123293)
                ·
                  refine ⟨1333738842632492113921235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3556636913686645637123293 1333738842632492113921235)
                  ·
                    refine ⟨2000608263948738170881853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1333738842632492113921235 2000608263948738170881853)
                    ·
                      refine ⟨750228098980776814080695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2000608263948738170881853 750228098980776814080695)
                      ·
                        rfl

theorem cell23_1461064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 1, 4, 3, 1, 3].length) (baseStart_1461064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461064 prefixEnd_1461064 := by exact prefixLift 1461064
  have htrace : WordTrace (prefixWord ++ tailWord_1461064) baseStart_1461064 baseEnd_1461064 := by
    simpa [prefixWord, tailWord_1461064, baseEnd_1461064] using wordTrace_append hprefix tailTrace_1461064
  have hstable : (prefixWord ++ tailWord_1461064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461064).length < 2 ^ (prefixWord ++ tailWord_1461064).sum := by decide
  have hdescent : baseEnd_1461064 < baseStart_1461064 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461074 : List Nat := [3, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2]
def baseStart_1461074 : Nat := 118140960795 + 1461074 * 2 ^ 59
def prefixEnd_1461074 : Nat := 4983230072969 + 3 ^ 40 * 1461074 * 2
def baseEnd_1461074 : Nat := 750233233787321774955649

theorem tailTrace_1461074 : CollatzResearch.WordTrace tailWord_1461074 prefixEnd_1461074 750233233787321774955649 := by
  unfold tailWord_1461074
  simp only [CollatzResearch.WordTrace]
  refine ⟨13322436677196476104521569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 35526497805857269612057517 13322436677196476104521569)
  ·
    refine ⟨9991827507897357078391177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13322436677196476104521569 9991827507897357078391177)
    ·
      refine ⟨7493870630923017808793383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9991827507897357078391177 7493870630923017808793383)
      ·
        refine ⟨11240805946384526713190075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7493870630923017808793383 11240805946384526713190075)
        ·
          refine ⟨16861208919576790069785113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11240805946384526713190075 16861208919576790069785113)
          ·
            refine ⟨12645906689682592552338835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16861208919576790069785113 12645906689682592552338835)
            ·
              refine ⟨18968860034523888828508253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12645906689682592552338835 18968860034523888828508253)
              ·
                refine ⟨7113322512946458310690595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 18968860034523888828508253 7113322512946458310690595)
                ·
                  refine ⟨10669983769419687466035893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7113322512946458310690595 10669983769419687466035893)
                  ·
                    refine ⟨1000310978383095699940865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10669983769419687466035893 1000310978383095699940865)
                    ·
                      refine ⟨750233233787321774955649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1000310978383095699940865 750233233787321774955649)
                      ·
                        rfl

theorem cell23_1461074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2].length) (baseStart_1461074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461074 prefixEnd_1461074 := by exact prefixLift 1461074
  have htrace : WordTrace (prefixWord ++ tailWord_1461074) baseStart_1461074 baseEnd_1461074 := by
    simpa [prefixWord, tailWord_1461074, baseEnd_1461074] using wordTrace_append hprefix tailTrace_1461074
  have hstable : (prefixWord ++ tailWord_1461074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461074).length < 2 ^ (prefixWord ++ tailWord_1461074).sum := by decide
  have hdescent : baseEnd_1461074 < baseStart_1461074 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461091 : List Nat := [1, 1, 1, 5, 3, 2, 1, 2, 2, 3, 2]
def baseStart_1461091 : Nat := 118140960795 + 1461091 * 2 ^ 59
def prefixEnd_1461091 : Nat := 4983230072969 + 3 ^ 40 * 1461091 * 2
def baseEnd_1461091 : Nat := 750241962958448208443071

theorem tailTrace_1461091 : CollatzResearch.WordTrace tailWord_1461091 prefixEnd_1461091 750241962958448208443071 := by
  unfold tailWord_1461091
  simp only [CollatzResearch.WordTrace]
  refine ⟨53290366749724316321455127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35526911166482877547636751 53290366749724316321455127)
  ·
    refine ⟨79935550124586474482182691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53290366749724316321455127 79935550124586474482182691)
    ·
      refine ⟨119903325186879711723274037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79935550124586474482182691 119903325186879711723274037)
      ·
        refine ⟨11240936736269972974056941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 119903325186879711723274037 11240936736269972974056941)
        ·
          refine ⟨4215351276101239865271353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11240936736269972974056941 4215351276101239865271353)
          ·
            refine ⟨3161513457075929898953515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4215351276101239865271353 3161513457075929898953515)
            ·
              refine ⟨4742270185613894848430273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3161513457075929898953515 4742270185613894848430273)
              ·
                refine ⟨3556702639210421136322705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4742270185613894848430273 3556702639210421136322705)
                ·
                  refine ⟨2667526979407815852242029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3556702639210421136322705 2667526979407815852242029)
                  ·
                    refine ⟨1000322617277930944590761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2667526979407815852242029 1000322617277930944590761)
                    ·
                      refine ⟨750241962958448208443071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1000322617277930944590761 750241962958448208443071)
                      ·
                        rfl

theorem cell23_1461091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 2, 2, 3, 2].length) (baseStart_1461091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461091 prefixEnd_1461091 := by exact prefixLift 1461091
  have htrace : WordTrace (prefixWord ++ tailWord_1461091) baseStart_1461091 baseEnd_1461091 := by
    simpa [prefixWord, tailWord_1461091, baseEnd_1461091] using wordTrace_append hprefix tailTrace_1461091
  have hstable : (prefixWord ++ tailWord_1461091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461091).length < 2 ^ (prefixWord ++ tailWord_1461091).sum := by decide
  have hdescent : baseEnd_1461091 < baseStart_1461091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461107 : List Nat := [1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 5]
def baseStart_1461107 : Nat := 118140960795 + 1461107 * 2 ^ 59
def prefixEnd_1461107 : Nat := 4983230072969 + 3 ^ 40 * 1461107 * 2
def baseEnd_1461107 : Nat := 750250178648920145842997

theorem tailTrace_1461107 : CollatzResearch.WordTrace tailWord_1461107 prefixEnd_1461107 750250178648920145842997 := by
  unfold tailWord_1461107
  simp only [CollatzResearch.WordTrace]
  refine ⟨53290950317666351054037575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35527300211777567369358383 53290950317666351054037575)
  ·
    refine ⟨79936425476499526581056363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53290950317666351054037575 79936425476499526581056363)
    ·
      refine ⟨119904638214749289871584545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79936425476499526581056363 119904638214749289871584545)
      ·
        refine ⟨89928478661061967403688409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 119904638214749289871584545 89928478661061967403688409)
        ·
          refine ⟨67446358995796475552766307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 89928478661061967403688409 67446358995796475552766307)
          ·
            refine ⟨101169538493694713329149461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67446358995796475552766307 101169538493694713329149461)
            ·
              refine ⟨4742322116891939687303881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 101169538493694713329149461 4742322116891939687303881)
              ·
                refine ⟨3556741587668954765477911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4742322116891939687303881 3556741587668954765477911)
                ·
                  refine ⟨5335112381503432148216867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3556741587668954765477911 5335112381503432148216867)
                  ·
                    refine ⟨8002668572255148222325301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5335112381503432148216867 8002668572255148222325301)
                    ·
                      refine ⟨750250178648920145842997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 8002668572255148222325301 750250178648920145842997)
                      ·
                        rfl

theorem cell23_1461107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 1, 1, 5].length) (baseStart_1461107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461107 prefixEnd_1461107 := by exact prefixLift 1461107
  have htrace : WordTrace (prefixWord ++ tailWord_1461107) baseStart_1461107 baseEnd_1461107 := by
    simpa [prefixWord, tailWord_1461107, baseEnd_1461107] using wordTrace_append hprefix tailTrace_1461107
  have hstable : (prefixWord ++ tailWord_1461107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461107).length < 2 ^ (prefixWord ++ tailWord_1461107).sum := by decide
  have hdescent : baseEnd_1461107 < baseStart_1461107 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461117 : List Nat := [1, 4, 1, 1, 2, 1, 4, 1, 1, 1, 6]
def baseStart_1461117 : Nat := 118140960795 + 1461117 * 2 ^ 59
def prefixEnd_1461117 : Nat := 4983230072969 + 3 ^ 40 * 1461117 * 2
def baseEnd_1461117 : Nat := 750255313455465106717951

theorem tailTrace_1461117 : CollatzResearch.WordTrace tailWord_1461117 prefixEnd_1461117 750255313455465106717951 := by
  unfold tailWord_1461117
  simp only [CollatzResearch.WordTrace]
  refine ⟨53291315047630122761901605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35527543365086748507934403 53291315047630122761901605)
  ·
    refine ⟨9992121571430648017856551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53291315047630122761901605 9992121571430648017856551)
    ·
      refine ⟨14988182357145972026784827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9992121571430648017856551 14988182357145972026784827)
      ·
        refine ⟨22482273535718958040177241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14988182357145972026784827 22482273535718958040177241)
        ·
          refine ⟨16861705151789218530132931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22482273535718958040177241 16861705151789218530132931)
          ·
            refine ⟨25292557727683827795199397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16861705151789218530132931 25292557727683827795199397)
            ·
              refine ⟨4742354573940717711599887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25292557727683827795199397 4742354573940717711599887)
              ·
                refine ⟨7113531860911076567399831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4742354573940717711599887 7113531860911076567399831)
                ·
                  refine ⟨10670297791366614851099747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7113531860911076567399831 10670297791366614851099747)
                  ·
                    refine ⟨16005446687049922276649621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10670297791366614851099747 16005446687049922276649621)
                    ·
                      refine ⟨750255313455465106717951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 16005446687049922276649621 750255313455465106717951)
                      ·
                        rfl

theorem cell23_1461117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 4, 1, 1, 1, 6].length) (baseStart_1461117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461117 prefixEnd_1461117 := by exact prefixLift 1461117
  have htrace : WordTrace (prefixWord ++ tailWord_1461117) baseStart_1461117 baseEnd_1461117 := by
    simpa [prefixWord, tailWord_1461117, baseEnd_1461117] using wordTrace_append hprefix tailTrace_1461117
  have hstable : (prefixWord ++ tailWord_1461117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461117).length < 2 ^ (prefixWord ++ tailWord_1461117).sum := by decide
  have hdescent : baseEnd_1461117 < baseStart_1461117 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461127 : List Nat := [1, 1, 4, 2, 3, 1, 2, 9]
def baseStart_1461127 : Nat := 118140960795 + 1461127 * 2 ^ 59
def prefixEnd_1461127 : Nat := 4983230072969 + 3 ^ 40 * 1461127 * 2
def baseEnd_1461127 : Nat := 27787424009704076577515

theorem tailTrace_1461127 : CollatzResearch.WordTrace tailWord_1461127 prefixEnd_1461127 27787424009704076577515 := by
  unfold tailWord_1461127
  simp only [CollatzResearch.WordTrace]
  refine ⟨53291679777593894469765635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35527786518395929646510423 53291679777593894469765635)
  ·
    refine ⟨79937519666390841704648453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53291679777593894469765635 79937519666390841704648453)
    ·
      refine ⟨14988284937448282819621585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 79937519666390841704648453 14988284937448282819621585)
      ·
        refine ⟨11241213703086212114716189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14988284937448282819621585 11241213703086212114716189)
        ·
          refine ⟨4215455138657329543018571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11241213703086212114716189 4215455138657329543018571)
          ·
            refine ⟨6323182707985994314527857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4215455138657329543018571 6323182707985994314527857)
            ·
              refine ⟨4742387030989495735895893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6323182707985994314527857 4742387030989495735895893)
              ·
                refine ⟨27787424009704076577515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4742387030989495735895893 27787424009704076577515)
                ·
                  rfl

theorem cell23_1461127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 1, 2, 9].length) (baseStart_1461127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461127 prefixEnd_1461127 := by exact prefixLift 1461127
  have htrace : WordTrace (prefixWord ++ tailWord_1461127) baseStart_1461127 baseEnd_1461127 := by
    simpa [prefixWord, tailWord_1461127, baseEnd_1461127] using wordTrace_append hprefix tailTrace_1461127
  have hstable : (prefixWord ++ tailWord_1461127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461127).length < 2 ^ (prefixWord ++ tailWord_1461127).sum := by decide
  have hdescent : baseEnd_1461127 < baseStart_1461127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461148 : List Nat := [2, 2, 3, 3, 2, 1, 2, 2, 2, 4]
def baseStart_1461148 : Nat := 118140960795 + 1461148 * 2 ^ 59
def prefixEnd_1461148 : Nat := 4983230072969 + 3 ^ 40 * 1461148 * 2
def baseEnd_1461148 : Nat := 250090410451918161810103

theorem tailTrace_1461148 : CollatzResearch.WordTrace tailWord_1461148 prefixEnd_1461148 250090410451918161810103 := by
  unfold tailWord_1461148
  simp only [CollatzResearch.WordTrace]
  refine ⟨26646222855258907528140049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35528297140345210037520065 26646222855258907528140049)
  ·
    refine ⟨19984667141444180646105037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26646222855258907528140049 19984667141444180646105037)
    ·
      refine ⟨7494250178041567742289389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19984667141444180646105037 7494250178041567742289389)
      ·
        refine ⟨2810343816765587903358521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7494250178041567742289389 2810343816765587903358521)
        ·
          refine ⟨2107757862574190927518891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2810343816765587903358521 2107757862574190927518891)
          ·
            refine ⟨3161636793861286391278337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2107757862574190927518891 3161636793861286391278337)
            ·
              refine ⟨2371227595395964793458753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3161636793861286391278337 2371227595395964793458753)
              ·
                refine ⟨1778420696546973595094065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2371227595395964793458753 1778420696546973595094065)
                ·
                  refine ⟨1333815522410230196320549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1778420696546973595094065 1333815522410230196320549)
                  ·
                    refine ⟨250090410451918161810103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1333815522410230196320549 250090410451918161810103)
                    ·
                      rfl

theorem cell23_1461148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 3, 2, 1, 2, 2, 2, 4].length) (baseStart_1461148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461148 prefixEnd_1461148 := by exact prefixLift 1461148
  have htrace : WordTrace (prefixWord ++ tailWord_1461148) baseStart_1461148 baseEnd_1461148 := by
    simpa [prefixWord, tailWord_1461148, baseEnd_1461148] using wordTrace_append hprefix tailTrace_1461148
  have hstable : (prefixWord ++ tailWord_1461148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461148).length < 2 ^ (prefixWord ++ tailWord_1461148).sum := by decide
  have hdescent : baseEnd_1461148 < baseStart_1461148 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461155 : List Nat := [1, 1, 1, 4, 1, 2, 6, 2, 1, 2, 2]
def baseStart_1461155 : Nat := 118140960795 + 1461155 * 2 ^ 59
def prefixEnd_1461155 : Nat := 4983230072969 + 3 ^ 40 * 1461155 * 2
def baseEnd_1461155 : Nat := 750274825720335958042777

theorem tailTrace_1461155 : CollatzResearch.WordTrace tailWord_1461155 prefixEnd_1461155 750274825720335958042777 := by
  unfold tailWord_1461155
  simp only [CollatzResearch.WordTrace]
  refine ⟨53292701021492455251784919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35528467347661636834523279 53292701021492455251784919)
  ·
    refine ⟨79939051532238682877677379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53292701021492455251784919 79939051532238682877677379)
    ·
      refine ⟨119908577298358024316516069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 79939051532238682877677379 119908577298358024316516069)
      ·
        refine ⟨22482858243442129559346763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 119908577298358024316516069 22482858243442129559346763)
        ·
          refine ⟨33724287365163194339020145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22482858243442129559346763 33724287365163194339020145)
          ·
            refine ⟨25293215523872395754265109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33724287365163194339020145 25293215523872395754265109)
            ·
              refine ⟨1185619477681518550981177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 25293215523872395754265109 1185619477681518550981177)
              ·
                refine ⟨889214608261138913235883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1185619477681518550981177 889214608261138913235883)
                ·
                  refine ⟨1333821912391708369853825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 889214608261138913235883 1333821912391708369853825)
                  ·
                    refine ⟨1000366434293781277390369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1333821912391708369853825 1000366434293781277390369)
                    ·
                      refine ⟨750274825720335958042777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1000366434293781277390369 750274825720335958042777)
                      ·
                        rfl

theorem cell23_1461155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 2, 1, 2, 2].length) (baseStart_1461155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461155 prefixEnd_1461155 := by exact prefixLift 1461155
  have htrace : WordTrace (prefixWord ++ tailWord_1461155) baseStart_1461155 baseEnd_1461155 := by
    simpa [prefixWord, tailWord_1461155, baseEnd_1461155] using wordTrace_append hprefix tailTrace_1461155
  have hstable : (prefixWord ++ tailWord_1461155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461155).length < 2 ^ (prefixWord ++ tailWord_1461155).sum := by decide
  have hdescent : baseEnd_1461155 < baseStart_1461155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461198 : List Nat := [4, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2]
def baseStart_1461198 : Nat := 118140960795 + 1461198 * 2 ^ 59
def prefixEnd_1461198 : Nat := 4983230072969 + 3 ^ 40 * 1461198 * 2
def baseEnd_1461198 : Nat := 750296905388479289805079

theorem tailTrace_1461198 : CollatzResearch.WordTrace tailWord_1461198 prefixEnd_1461198 750296905388479289805079 := by
  unfold tailWord_1461198
  simp only [CollatzResearch.WordTrace]
  refine ⟨6661783670042084199450031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 35529512906891115730400165 6661783670042084199450031)
  ·
    refine ⟨9992675505063126299175047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6661783670042084199450031 9992675505063126299175047)
    ·
      refine ⟨14989013257594689448762571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9992675505063126299175047 14989013257594689448762571)
      ·
        refine ⟨22483519886392034173143857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14989013257594689448762571 22483519886392034173143857)
        ·
          refine ⟨16862639914794025629857893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22483519886392034173143857 16862639914794025629857893)
          ·
            refine ⟨3161744984023879805598355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16862639914794025629857893 3161744984023879805598355)
            ·
              refine ⟨4742617476035819708397533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3161744984023879805598355 4742617476035819708397533)
              ·
                refine ⟨1778481553513432390649075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4742617476035819708397533 1778481553513432390649075)
                ·
                  refine ⟨2667722330270148585973613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1778481553513432390649075 2667722330270148585973613)
                  ·
                    refine ⟨1000395873851305719740105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2667722330270148585973613 1000395873851305719740105)
                    ·
                      refine ⟨750296905388479289805079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1000395873851305719740105 750296905388479289805079)
                      ·
                        rfl

theorem cell23_1461198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 1, 3, 1, 3, 2].length) (baseStart_1461198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461198 prefixEnd_1461198 := by exact prefixLift 1461198
  have htrace : WordTrace (prefixWord ++ tailWord_1461198) baseStart_1461198 baseEnd_1461198 := by
    simpa [prefixWord, tailWord_1461198, baseEnd_1461198] using wordTrace_append hprefix tailTrace_1461198
  have hstable : (prefixWord ++ tailWord_1461198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461198).length < 2 ^ (prefixWord ++ tailWord_1461198).sum := by decide
  have hdescent : baseEnd_1461198 < baseStart_1461198 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461204 : List Nat := [2, 4, 1, 2, 1, 2, 1, 2, 2, 6]
def baseStart_1461204 : Nat := 118140960795 + 1461204 * 2 ^ 59
def prefixEnd_1461204 : Nat := 4983230072969 + 3 ^ 40 * 1461204 * 2
def baseEnd_1461204 : Nat := 250099995424135422110017

theorem tailTrace_1461204 : CollatzResearch.WordTrace tailWord_1461204 prefixEnd_1461204 250099995424135422110017 := by
  unfold tailWord_1461204
  simp only [CollatzResearch.WordTrace]
  refine ⟨26647244099157468310159333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 35529658798876624413545777 26647244099157468310159333)
  ·
    refine ⟨4996358268592025308154875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 26647244099157468310159333 4996358268592025308154875)
    ·
      refine ⟨7494537402888037962232313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4996358268592025308154875 7494537402888037962232313)
      ·
        refine ⟨5620903052166028471674235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7494537402888037962232313 5620903052166028471674235)
        ·
          refine ⟨8431354578249042707511353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5620903052166028471674235 8431354578249042707511353)
          ·
            refine ⟨6323515933686782030633515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8431354578249042707511353 6323515933686782030633515)
            ·
              refine ⟨9485273900530173045950273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6323515933686782030633515 9485273900530173045950273)
              ·
                refine ⟨7113955425397629784462705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9485273900530173045950273 7113955425397629784462705)
                ·
                  refine ⟨5335466569048222338347029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7113955425397629784462705 5335466569048222338347029)
                  ·
                    refine ⟨250099995424135422110017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 5335466569048222338347029 250099995424135422110017)
                    ·
                      rfl

theorem cell23_1461204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 2, 1, 2, 2, 6].length) (baseStart_1461204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461204 prefixEnd_1461204 := by exact prefixLift 1461204
  have htrace : WordTrace (prefixWord ++ tailWord_1461204) baseStart_1461204 baseEnd_1461204 := by
    simpa [prefixWord, tailWord_1461204, baseEnd_1461204] using wordTrace_append hprefix tailTrace_1461204
  have hstable : (prefixWord ++ tailWord_1461204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461204).length < 2 ^ (prefixWord ++ tailWord_1461204).sum := by decide
  have hdescent : baseEnd_1461204 < baseStart_1461204 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1461205 : List Nat := [1, 3, 2, 3, 3, 2, 1, 2, 2, 1, 3]
def baseStart_1461205 : Nat := 118140960795 + 1461205 * 2 ^ 59
def prefixEnd_1461205 : Nat := 4983230072969 + 3 ^ 40 * 1461205 * 2
def baseEnd_1461205 : Nat := 750300499753060762417547

theorem tailTrace_1461205 : CollatzResearch.WordTrace tailWord_1461205 prefixEnd_1461205 750300499753060762417547 := by
  unfold tailWord_1461205
  simp only [CollatzResearch.WordTrace]
  refine ⟨53294524671311313791105069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 35529683114207542527403379 53294524671311313791105069)
  ·
    refine ⟨19985446751741742671664401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53294524671311313791105069 19985446751741742671664401)
    ·
      refine ⟨14989085063806307003748301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19985446751741742671664401 14989085063806307003748301)
      ·
        refine ⟨5620906898927365126405613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14989085063806307003748301 5620906898927365126405613)
        ·
          refine ⟨2107840087097761922402105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5620906898927365126405613 2107840087097761922402105)
          ·
            refine ⟨1580880065323321441801579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2107840087097761922402105 1580880065323321441801579)
            ·
              refine ⟨2371320097984982162702369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1580880065323321441801579 2371320097984982162702369)
              ·
                refine ⟨1778490073488736622026777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2371320097984982162702369 1778490073488736622026777)
                ·
                  refine ⟨1333867555116552466520083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1778490073488736622026777 1333867555116552466520083)
                  ·
                    refine ⟨2000801332674828699780125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1333867555116552466520083 2000801332674828699780125)
                    ·
                      refine ⟨750300499753060762417547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 2000801332674828699780125 750300499753060762417547)
                      ·
                        rfl

theorem cell23_1461205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 3, 2, 1, 2, 2, 1, 3].length) (baseStart_1461205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1461205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1461205 prefixEnd_1461205 := by exact prefixLift 1461205
  have htrace : WordTrace (prefixWord ++ tailWord_1461205) baseStart_1461205 baseEnd_1461205 := by
    simpa [prefixWord, tailWord_1461205, baseEnd_1461205] using wordTrace_append hprefix tailTrace_1461205
  have hstable : (prefixWord ++ tailWord_1461205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1461205).length < 2 ^ (prefixWord ++ tailWord_1461205).sum := by decide
  have hdescent : baseEnd_1461205 < baseStart_1461205 := by decide
  rcases family_descends (prefixWord ++ tailWord_1461205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
