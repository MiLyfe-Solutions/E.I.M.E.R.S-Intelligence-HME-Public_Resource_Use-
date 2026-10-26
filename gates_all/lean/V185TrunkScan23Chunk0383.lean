import V185TrunkScan23Chunk0382

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_2264426 : List Nat := [3, 1, 3, 3, 3, 1, 2, 1, 1, 1, 4]
def baseStart_2264426 : Nat := 118140960795 + 2264426 * 2 ^ 59
def prefixEnd_2264426 : Nat := 4983230072969 + 3 ^ 40 * 2264426 * 2
def baseEnd_2264426 : Nat := 1162738944538062656561101

theorem tailTrace_2264426 : CollatzResearch.WordTrace tailWord_2264426 prefixEnd_2264426 1162738944538062656561101 := by
  unfold tailWord_2264426
  simp only [CollatzResearch.WordTrace]
  refine ⟨20647600323594702504127283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55060267529585873344339421 20647600323594702504127283)
  ·
    refine ⟨30971400485392053756190925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20647600323594702504127283 30971400485392053756190925)
    ·
      refine ⟨11614275182022020158571597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30971400485392053756190925 11614275182022020158571597)
      ·
        refine ⟨4355353193258257559464349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11614275182022020158571597 4355353193258257559464349)
        ·
          refine ⟨1633257447471846584799131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4355353193258257559464349 1633257447471846584799131)
          ·
            refine ⟨2449886171207769877198697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1633257447471846584799131 2449886171207769877198697)
            ·
              refine ⟨1837414628405827407899023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2449886171207769877198697 1837414628405827407899023)
              ·
                refine ⟨2756121942608741111848535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1837414628405827407899023 2756121942608741111848535)
                ·
                  refine ⟨4134182913913111667772803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2756121942608741111848535 4134182913913111667772803)
                  ·
                    refine ⟨6201274370869667501659205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4134182913913111667772803 6201274370869667501659205)
                    ·
                      refine ⟨1162738944538062656561101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6201274370869667501659205 1162738944538062656561101)
                      ·
                        rfl

theorem cell23_2264426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_2264426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264426 prefixEnd_2264426 := by exact prefixLift 2264426
  have htrace : WordTrace (prefixWord ++ tailWord_2264426) baseStart_2264426 baseEnd_2264426 := by
    simpa [prefixWord, tailWord_2264426, baseEnd_2264426] using wordTrace_append hprefix tailTrace_2264426
  have hstable : (prefixWord ++ tailWord_2264426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264426).length < 2 ^ (prefixWord ++ tailWord_2264426).sum := by decide
  have hdescent : baseEnd_2264426 < baseStart_2264426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264429 : List Nat := [1, 5, 1, 1, 1, 5, 2, 1, 1, 2, 3]
def baseStart_2264429 : Nat := 118140960795 + 2264429 * 2 ^ 59
def prefixEnd_2264429 : Nat := 4983230072969 + 3 ^ 40 * 2264429 * 2
def baseEnd_2264429 : Nat := 1162740484980026144823587

theorem tailTrace_2264429 : CollatzResearch.WordTrace tailWord_2264429 prefixEnd_2264429 1162740484980026144823587 := by
  unfold tailWord_2264429
  simp only [CollatzResearch.WordTrace]
  refine ⟨82590510713367941528868341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55060340475578627685912227 82590510713367941528868341)
  ·
    refine ⟨7742860379378244518331407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82590510713367941528868341 7742860379378244518331407)
    ·
      refine ⟨11614290569067366777497111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7742860379378244518331407 11614290569067366777497111)
      ·
        refine ⟨17421435853601050166245667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11614290569067366777497111 17421435853601050166245667)
        ·
          refine ⟨26132153780401575249368501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17421435853601050166245667 26132153780401575249368501)
          ·
            refine ⟨2449889416912647679628297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26132153780401575249368501 2449889416912647679628297)
            ·
              refine ⟨1837417062684485759721223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2449889416912647679628297 1837417062684485759721223)
              ·
                refine ⟨2756125594026728639581835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1837417062684485759721223 2756125594026728639581835)
                ·
                  refine ⟨4134188391040092959372753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2756125594026728639581835 4134188391040092959372753)
                  ·
                    refine ⟨3100641293280069719529565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4134188391040092959372753 3100641293280069719529565)
                    ·
                      refine ⟨1162740484980026144823587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3100641293280069719529565 1162740484980026144823587)
                      ·
                        rfl

theorem cell23_2264429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 2, 1, 1, 2, 3].length) (baseStart_2264429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264429 prefixEnd_2264429 := by exact prefixLift 2264429
  have htrace : WordTrace (prefixWord ++ tailWord_2264429) baseStart_2264429 baseEnd_2264429 := by
    simpa [prefixWord, tailWord_2264429, baseEnd_2264429] using wordTrace_append hprefix tailTrace_2264429
  have hstable : (prefixWord ++ tailWord_2264429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264429).length < 2 ^ (prefixWord ++ tailWord_2264429).sum := by decide
  have hdescent : baseEnd_2264429 < baseStart_2264429 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264516 : List Nat := [2, 3, 3, 2, 1, 2, 1, 3, 2, 2, 2]
def baseStart_2264516 : Nat := 118140960795 + 2264516 * 2 ^ 59
def prefixEnd_2264516 : Nat := 4983230072969 + 3 ^ 40 * 2264516 * 2
def baseEnd_2264516 : Nat := 1162785157796967304435687

theorem tailTrace_2264516 : CollatzResearch.WordTrace tailWord_2264516 prefixEnd_2264516 1162785157796967304435687 := by
  unfold tailWord_2264516
  simp only [CollatzResearch.WordTrace]
  refine ⟨41296841932026377693642701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55062455909368503591523601 41296841932026377693642701)
  ·
    refine ⟨15486315724509891635116013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41296841932026377693642701 15486315724509891635116013)
    ·
      refine ⟨5807368396691209363168505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15486315724509891635116013 5807368396691209363168505)
      ·
        refine ⟨4355526297518407022376379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5807368396691209363168505 4355526297518407022376379)
        ·
          refine ⟨6533289446277610533564569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4355526297518407022376379 6533289446277610533564569)
          ·
            refine ⟨4899967084708207900173427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6533289446277610533564569 4899967084708207900173427)
            ·
              refine ⟨7349950627062311850260141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4899967084708207900173427 7349950627062311850260141)
              ·
                refine ⟨2756231485148366943847553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7349950627062311850260141 2756231485148366943847553)
                ·
                  refine ⟨2067173613861275207885665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2756231485148366943847553 2067173613861275207885665)
                  ·
                    refine ⟨1550380210395956405914249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2067173613861275207885665 1550380210395956405914249)
                    ·
                      refine ⟨1162785157796967304435687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1550380210395956405914249 1162785157796967304435687)
                      ·
                        rfl

theorem cell23_2264516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 1, 3, 2, 2, 2].length) (baseStart_2264516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264516 prefixEnd_2264516 := by exact prefixLift 2264516
  have htrace : WordTrace (prefixWord ++ tailWord_2264516) baseStart_2264516 baseEnd_2264516 := by
    simpa [prefixWord, tailWord_2264516, baseEnd_2264516] using wordTrace_append hprefix tailTrace_2264516
  have hstable : (prefixWord ++ tailWord_2264516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264516).length < 2 ^ (prefixWord ++ tailWord_2264516).sum := by decide
  have hdescent : baseEnd_2264516 < baseStart_2264516 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264632 : List Nat := [2, 1, 2, 1, 4, 2, 1, 2, 1, 5, 2]
def baseStart_2264632 : Nat := 118140960795 + 2264632 * 2 ^ 59
def prefixEnd_2264632 : Nat := 4983230072969 + 3 ^ 40 * 2264632 * 2
def baseEnd_2264632 : Nat := 1162844721552888850585153

theorem tailTrace_2264632 : CollatzResearch.WordTrace tailWord_2264632 prefixEnd_2264632 1162844721552888850585153 := by
  unfold tailWord_2264632
  simp only [CollatzResearch.WordTrace]
  refine ⟨41298957365816253599254075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55065276487755004799005433 41298957365816253599254075)
  ·
    refine ⟨61948436048724380398881113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41298957365816253599254075 61948436048724380398881113)
    ·
      refine ⟨46461327036543285299160835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61948436048724380398881113 46461327036543285299160835)
      ·
        refine ⟨69691990554814927948741253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46461327036543285299160835 69691990554814927948741253)
        ·
          refine ⟨13067248229027798990388985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69691990554814927948741253 13067248229027798990388985)
          ·
            refine ⟨9800436171770849242791739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13067248229027798990388985 9800436171770849242791739)
            ·
              refine ⟨14700654257656273864187609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9800436171770849242791739 14700654257656273864187609)
              ·
                refine ⟨11025490693242205398140707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14700654257656273864187609 11025490693242205398140707)
                ·
                  refine ⟨16538236039863308097211061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11025490693242205398140707 16538236039863308097211061)
                  ·
                    refine ⟨1550459628737185134113537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16538236039863308097211061 1550459628737185134113537)
                    ·
                      refine ⟨1162844721552888850585153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1550459628737185134113537 1162844721552888850585153)
                      ·
                        rfl

theorem cell23_2264632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 1, 5, 2].length) (baseStart_2264632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264632 prefixEnd_2264632 := by exact prefixLift 2264632
  have htrace : WordTrace (prefixWord ++ tailWord_2264632) baseStart_2264632 baseEnd_2264632 := by
    simpa [prefixWord, tailWord_2264632, baseEnd_2264632] using wordTrace_append hprefix tailTrace_2264632
  have hstable : (prefixWord ++ tailWord_2264632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264632).length < 2 ^ (prefixWord ++ tailWord_2264632).sum := by decide
  have hdescent : baseEnd_2264632 < baseStart_2264632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264672 : List Nat := [2, 1, 1, 3, 2, 1, 1, 6, 2, 4]
def baseStart_2264672 : Nat := 118140960795 + 2264672 * 2 ^ 59
def prefixEnd_2264672 : Nat := 4983230072969 + 3 ^ 40 * 2264672 * 2
def baseEnd_2264672 : Nat := 387621753593022898028323

theorem tailTrace_2264672 : CollatzResearch.WordTrace tailWord_2264672 prefixEnd_2264672 387621753593022898028323 := by
  unfold tailWord_2264672
  simp only [CollatzResearch.WordTrace]
  refine ⟨41299686825743797014982135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55066249100991729353309513 41299686825743797014982135)
  ·
    refine ⟨61949530238615695522473203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41299686825743797014982135 61949530238615695522473203)
    ·
      refine ⟨92924295357923543283709805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61949530238615695522473203 92924295357923543283709805)
      ·
        refine ⟨34846610759221328731391177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92924295357923543283709805 34846610759221328731391177)
        ·
          refine ⟨26134958069415996548543383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34846610759221328731391177 26134958069415996548543383)
          ·
            refine ⟨39202437104123994822815075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26134958069415996548543383 39202437104123994822815075)
            ·
              refine ⟨58803655656185992234222613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39202437104123994822815075 58803655656185992234222613)
              ·
                refine ⟨2756421358883718385979185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 58803655656185992234222613 2756421358883718385979185)
                ·
                  refine ⟨2067316019162788789484389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2756421358883718385979185 2067316019162788789484389)
                  ·
                    refine ⟨387621753593022898028323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2067316019162788789484389 387621753593022898028323)
                    ·
                      rfl

theorem cell23_2264672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 6, 2, 4].length) (baseStart_2264672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264672 prefixEnd_2264672 := by exact prefixLift 2264672
  have htrace : WordTrace (prefixWord ++ tailWord_2264672) baseStart_2264672 baseEnd_2264672 := by
    simpa [prefixWord, tailWord_2264672, baseEnd_2264672] using wordTrace_append hprefix tailTrace_2264672
  have hstable : (prefixWord ++ tailWord_2264672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264672).length < 2 ^ (prefixWord ++ tailWord_2264672).sum := by decide
  have hdescent : baseEnd_2264672 < baseStart_2264672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264675 : List Nat := [1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 6]
def baseStart_2264675 : Nat := 118140960795 + 2264675 * 2 ^ 59
def prefixEnd_2264675 : Nat := 4983230072969 + 3 ^ 40 * 2264675 * 2
def baseEnd_2264675 : Nat := 1162866801221032182347455

theorem tailTrace_2264675 : CollatzResearch.WordTrace tailWord_2264675 prefixEnd_2264675 1162866801221032182347455 := by
  unfold tailWord_2264675
  simp only [CollatzResearch.WordTrace]
  refine ⟨82599483070476725542323479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55066322046984483694882319 82599483070476725542323479)
  ·
    refine ⟨123899224605715088313485219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82599483070476725542323479 123899224605715088313485219)
    ·
      refine ⟨185848836908572632470227829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123899224605715088313485219 185848836908572632470227829)
      ·
        refine ⟨17423328460178684294083859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 185848836908572632470227829 17423328460178684294083859)
        ·
          refine ⟨26134992690268026441125789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17423328460178684294083859 26134992690268026441125789)
          ·
            refine ⟨9800622258850509915422171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26134992690268026441125789 9800622258850509915422171)
            ·
              refine ⟨14700933388275764873133257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9800622258850509915422171 14700933388275764873133257)
              ·
                refine ⟨11025700041206823654849943, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14700933388275764873133257 11025700041206823654849943)
                ·
                  refine ⟨16538550061810235482274915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11025700041206823654849943 16538550061810235482274915)
                  ·
                    refine ⟨24807825092715353223412373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16538550061810235482274915 24807825092715353223412373)
                    ·
                      refine ⟨1162866801221032182347455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24807825092715353223412373 1162866801221032182347455)
                      ·
                        rfl

theorem cell23_2264675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_2264675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264675 prefixEnd_2264675 := by exact prefixLift 2264675
  have htrace : WordTrace (prefixWord ++ tailWord_2264675) baseStart_2264675 baseEnd_2264675 := by
    simpa [prefixWord, tailWord_2264675, baseEnd_2264675] using wordTrace_append hprefix tailTrace_2264675
  have hstable : (prefixWord ++ tailWord_2264675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264675).length < 2 ^ (prefixWord ++ tailWord_2264675).sum := by decide
  have hdescent : baseEnd_2264675 < baseStart_2264675 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264682 : List Nat := [3, 1, 3, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_2264682 : Nat := 118140960795 + 2264682 * 2 ^ 59
def prefixEnd_2264682 : Nat := 4983230072969 + 3 ^ 40 * 2264682 * 2
def baseEnd_2264682 : Nat := 1162870395585613654959923

theorem tailTrace_2264682 : CollatzResearch.WordTrace tailWord_2264682 prefixEnd_2264682 1162870395585613654959923 := by
  unfold tailWord_2264682
  simp only [CollatzResearch.WordTrace]
  refine ⟨20649934595362841434457075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55066492254300910491885533 20649934595362841434457075)
  ·
    refine ⟨30974901893044262151685613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20649934595362841434457075 30974901893044262151685613)
    ·
      refine ⟨11615588209891598306882105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30974901893044262151685613 11615588209891598306882105)
      ·
        refine ⟨8711691157418698730161579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11615588209891598306882105 8711691157418698730161579)
        ·
          refine ⟨13067536736128048095242369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8711691157418698730161579 13067536736128048095242369)
          ·
            refine ⟨9800652552096036071431777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13067536736128048095242369 9800652552096036071431777)
            ·
              refine ⟨7350489414072027053573833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9800652552096036071431777 7350489414072027053573833)
              ·
                refine ⟨5512867060554020290180375, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7350489414072027053573833 5512867060554020290180375)
                ·
                  refine ⟨8269300590831030435270563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5512867060554020290180375 8269300590831030435270563)
                  ·
                    refine ⟨12403950886246545652905845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8269300590831030435270563 12403950886246545652905845)
                    ·
                      refine ⟨1162870395585613654959923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12403950886246545652905845 1162870395585613654959923)
                      ·
                        rfl

theorem cell23_2264682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_2264682 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264682 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264682 prefixEnd_2264682 := by exact prefixLift 2264682
  have htrace : WordTrace (prefixWord ++ tailWord_2264682) baseStart_2264682 baseEnd_2264682 := by
    simpa [prefixWord, tailWord_2264682, baseEnd_2264682] using wordTrace_append hprefix tailTrace_2264682
  have hstable : (prefixWord ++ tailWord_2264682).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264682).length < 2 ^ (prefixWord ++ tailWord_2264682).sum := by decide
  have hdescent : baseEnd_2264682 < baseStart_2264682 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264725 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 2, 2, 5]
def baseStart_2264725 : Nat := 118140960795 + 2264725 * 2 ^ 59
def prefixEnd_2264725 : Nat := 4983230072969 + 3 ^ 40 * 2264725 * 2
def baseEnd_2264725 : Nat := 1162892475253756986722225

theorem tailTrace_2264725 : CollatzResearch.WordTrace tailWord_2264725 prefixEnd_2264725 1162892475253756986722225 := by
  unfold tailWord_2264725
  simp only [CollatzResearch.WordTrace]
  refine ⟨82601306720295584081643629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55067537813530389387762419 82601306720295584081643629)
  ·
    refine ⟨30975490020110844030616361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82601306720295584081643629 30975490020110844030616361)
    ·
      refine ⟨23231617515083133022962271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30975490020110844030616361 23231617515083133022962271)
      ·
        refine ⟨34847426272624699534443407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23231617515083133022962271 34847426272624699534443407)
        ·
          refine ⟨52271139408937049301665111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34847426272624699534443407 52271139408937049301665111)
          ·
            refine ⟨78406709113405573952497667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52271139408937049301665111 78406709113405573952497667)
            ·
              refine ⟨117610063670108360928746501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78406709113405573952497667 117610063670108360928746501)
              ·
                refine ⟨22051886938145317674139969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117610063670108360928746501 22051886938145317674139969)
                ·
                  refine ⟨16538915203608988255604977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22051886938145317674139969 16538915203608988255604977)
                  ·
                    refine ⟨12404186402706741191703733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16538915203608988255604977 12404186402706741191703733)
                    ·
                      refine ⟨1162892475253756986722225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12404186402706741191703733 1162892475253756986722225)
                      ·
                        rfl

theorem cell23_2264725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 2, 2, 5].length) (baseStart_2264725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264725 prefixEnd_2264725 := by exact prefixLift 2264725
  have htrace : WordTrace (prefixWord ++ tailWord_2264725) baseStart_2264725 baseEnd_2264725 := by
    simpa [prefixWord, tailWord_2264725, baseEnd_2264725] using wordTrace_append hprefix tailTrace_2264725
  have hstable : (prefixWord ++ tailWord_2264725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264725).length < 2 ^ (prefixWord ++ tailWord_2264725).sum := by decide
  have hdescent : baseEnd_2264725 < baseStart_2264725 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264772 : List Nat := [2, 3, 3, 1, 1, 1, 2, 1, 1, 3, 5]
def baseStart_2264772 : Nat := 118140960795 + 2264772 * 2 ^ 59
def prefixEnd_2264772 : Nat := 4983230072969 + 3 ^ 40 * 2264772 * 2
def baseEnd_2264772 : Nat := 1162916608844518302834509

theorem tailTrace_2264772 : CollatzResearch.WordTrace tailWord_2264772 prefixEnd_2264772 1162916608844518302834509 := by
  unfold tailWord_2264772
  simp only [CollatzResearch.WordTrace]
  refine ⟨41301510475562655554302285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55068680634083540739069713 41301510475562655554302285)
  ·
    refine ⟨15488066428335995832863357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41301510475562655554302285 15488066428335995832863357)
    ·
      refine ⟨5808024910625998437323759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15488066428335995832863357 5808024910625998437323759)
      ·
        refine ⟨8712037365938997655985639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5808024910625998437323759 8712037365938997655985639)
        ·
          refine ⟨13068056048908496483978459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8712037365938997655985639 13068056048908496483978459)
          ·
            refine ⟨19602084073362744725967689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13068056048908496483978459 19602084073362744725967689)
            ·
              refine ⟨14701563055022058544475767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19602084073362744725967689 14701563055022058544475767)
              ·
                refine ⟨22052344582533087816713651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14701563055022058544475767 22052344582533087816713651)
                ·
                  refine ⟨33078516873799631725070477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22052344582533087816713651 33078516873799631725070477)
                  ·
                    refine ⟨12404443827674861896901429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33078516873799631725070477 12404443827674861896901429)
                    ·
                      refine ⟨1162916608844518302834509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12404443827674861896901429 1162916608844518302834509)
                      ·
                        rfl

theorem cell23_2264772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 1, 1, 3, 5].length) (baseStart_2264772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264772 prefixEnd_2264772 := by exact prefixLift 2264772
  have htrace : WordTrace (prefixWord ++ tailWord_2264772) baseStart_2264772 baseEnd_2264772 := by
    simpa [prefixWord, tailWord_2264772, baseEnd_2264772] using wordTrace_append hprefix tailTrace_2264772
  have hstable : (prefixWord ++ tailWord_2264772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264772).length < 2 ^ (prefixWord ++ tailWord_2264772).sum := by decide
  have hdescent : baseEnd_2264772 < baseStart_2264772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264775 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 9]
def baseStart_2264775 : Nat := 118140960795 + 2264775 * 2 ^ 59
def prefixEnd_2264775 : Nat := 4983230072969 + 3 ^ 40 * 2264775 * 2
def baseEnd_2264775 : Nat := 129213127698497976788555

theorem tailTrace_2264775 : CollatzResearch.WordTrace tailWord_2264775 prefixEnd_2264775 129213127698497976788555 := by
  unfold tailWord_2264775
  simp only [CollatzResearch.WordTrace]
  refine ⟨82603130370114442620963779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55068753580076295080642519 82603130370114442620963779)
  ·
    refine ⟨123904695555171663931445669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82603130370114442620963779 123904695555171663931445669)
    ·
      refine ⟨23232130416594686987146063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123904695555171663931445669 23232130416594686987146063)
      ·
        refine ⟨34848195624892030480719095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23232130416594686987146063 34848195624892030480719095)
        ·
          refine ⟨52272293437338045721078643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34848195624892030480719095 52272293437338045721078643)
          ·
            refine ⟨78408440156007068581617965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52272293437338045721078643 78408440156007068581617965)
            ·
              refine ⟨29403165058502650718106737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78408440156007068581617965 29403165058502650718106737)
              ·
                refine ⟨22052373793876988038580053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29403165058502650718106737 22052373793876988038580053)
                ·
                  refine ⟨129213127698497976788555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 22052373793876988038580053 129213127698497976788555)
                  ·
                    rfl

theorem cell23_2264775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 9].length) (baseStart_2264775 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264775 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264775 prefixEnd_2264775 := by exact prefixLift 2264775
  have htrace : WordTrace (prefixWord ++ tailWord_2264775) baseStart_2264775 baseEnd_2264775 := by
    simpa [prefixWord, tailWord_2264775, baseEnd_2264775] using wordTrace_append hprefix tailTrace_2264775
  have hstable : (prefixWord ++ tailWord_2264775).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264775).length < 2 ^ (prefixWord ++ tailWord_2264775).sum := by decide
  have hdescent : baseEnd_2264775 < baseStart_2264775 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264780 : List Nat := [2, 2, 1, 5, 3, 1, 1, 2, 2, 1, 3]
def baseStart_2264780 : Nat := 118140960795 + 2264780 * 2 ^ 59
def prefixEnd_2264780 : Nat := 4983230072969 + 3 ^ 40 * 2264780 * 2
def baseEnd_2264780 : Nat := 1162920716689754271534473

theorem tailTrace_2264780 : CollatzResearch.WordTrace tailWord_2264780 prefixEnd_2264780 1162920716689754271534473 := by
  unfold tailWord_2264780
  simp only [CollatzResearch.WordTrace]
  refine ⟨41301656367548164237447897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55068875156730885649930529 41301656367548164237447897)
  ·
    refine ⟨30976242275661123178085923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41301656367548164237447897 30976242275661123178085923)
    ·
      refine ⟨46464363413491684767128885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30976242275661123178085923 46464363413491684767128885)
      ·
        refine ⟨4356034070014845446918333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46464363413491684767128885 4356034070014845446918333)
        ·
          refine ⟨1633512776255567042594375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4356034070014845446918333 1633512776255567042594375)
          ·
            refine ⟨2450269164383350563891563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1633512776255567042594375 2450269164383350563891563)
            ·
              refine ⟨3675403746575025845837345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2450269164383350563891563 3675403746575025845837345)
              ·
                refine ⟨2756552809931269384378009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3675403746575025845837345 2756552809931269384378009)
                ·
                  refine ⟨2067414607448452038283507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2756552809931269384378009 2067414607448452038283507)
                  ·
                    refine ⟨3101121911172678057425261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2067414607448452038283507 3101121911172678057425261)
                    ·
                      refine ⟨1162920716689754271534473, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3101121911172678057425261 1162920716689754271534473)
                      ·
                        rfl

theorem cell23_2264780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 3, 1, 1, 2, 2, 1, 3].length) (baseStart_2264780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264780 prefixEnd_2264780 := by exact prefixLift 2264780
  have htrace : WordTrace (prefixWord ++ tailWord_2264780) baseStart_2264780 baseEnd_2264780 := by
    simpa [prefixWord, tailWord_2264780, baseEnd_2264780] using wordTrace_append hprefix tailTrace_2264780
  have hstable : (prefixWord ++ tailWord_2264780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264780).length < 2 ^ (prefixWord ++ tailWord_2264780).sum := by decide
  have hdescent : baseEnd_2264780 < baseStart_2264780 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264782 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4]
def baseStart_2264782 : Nat := 118140960795 + 2264782 * 2 ^ 59
def prefixEnd_2264782 : Nat := 4983230072969 + 3 ^ 40 * 2264782 * 2
def baseEnd_2264782 : Nat := 1162921743651063263709463

theorem tailTrace_2264782 : CollatzResearch.WordTrace tailWord_2264782 prefixEnd_2264782 1162921743651063263709463 := by
  unfold tailWord_2264782
  simp only [CollatzResearch.WordTrace]
  refine ⟨10325423210136135352058575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55068923787392721877645733 10325423210136135352058575)
  ·
    refine ⟨15488134815204203028087863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10325423210136135352058575 15488134815204203028087863)
    ·
      refine ⟨23232202222806304542131795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15488134815204203028087863 23232202222806304542131795)
      ·
        refine ⟨34848303334209456813197693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23232202222806304542131795 34848303334209456813197693)
        ·
          refine ⟨13068113750328546304949135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34848303334209456813197693 13068113750328546304949135)
          ·
            refine ⟨19602170625492819457423703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13068113750328546304949135 19602170625492819457423703)
            ·
              refine ⟨29403255938239229186135555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19602170625492819457423703 29403255938239229186135555)
              ·
                refine ⟨44104883907358843779203333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29403255938239229186135555 44104883907358843779203333)
                ·
                  refine ⟨8269665732629783208600625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44104883907358843779203333 8269665732629783208600625)
                  ·
                    refine ⟨6202249299472337406450469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8269665732629783208600625 6202249299472337406450469)
                    ·
                      refine ⟨1162921743651063263709463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6202249299472337406450469 1162921743651063263709463)
                      ·
                        rfl

theorem cell23_2264782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_2264782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264782 prefixEnd_2264782 := by exact prefixLift 2264782
  have htrace : WordTrace (prefixWord ++ tailWord_2264782) baseStart_2264782 baseEnd_2264782 := by
    simpa [prefixWord, tailWord_2264782, baseEnd_2264782] using wordTrace_append hprefix tailTrace_2264782
  have hstable : (prefixWord ++ tailWord_2264782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264782).length < 2 ^ (prefixWord ++ tailWord_2264782).sum := by decide
  have hdescent : baseEnd_2264782 < baseStart_2264782 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264792 : List Nat := [2, 1, 2, 2, 3, 1, 4, 1, 7]
def baseStart_2264792 : Nat := 118140960795 + 2264792 * 2 ^ 59
def prefixEnd_2264792 : Nat := 4983230072969 + 3 ^ 40 * 2264792 * 2
def baseEnd_2264792 : Nat := 129214097606400913842713

theorem tailTrace_2264792 : CollatzResearch.WordTrace tailWord_2264792 prefixEnd_2264792 129214097606400913842713 := by
  unfold tailWord_2264792
  simp only [CollatzResearch.WordTrace]
  refine ⟨41301875205526427262166315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55069166940701903016221753 41301875205526427262166315)
  ·
    refine ⟨61952812808289640893249473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41301875205526427262166315 61952812808289640893249473)
    ·
      refine ⟨46464609606217230669937105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61952812808289640893249473 46464609606217230669937105)
      ·
        refine ⟨34848457204662923002452829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46464609606217230669937105 34848457204662923002452829)
        ·
          refine ⟨13068171451748596125919811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34848457204662923002452829 13068171451748596125919811)
          ·
            refine ⟨19602257177622894188879717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13068171451748596125919811 19602257177622894188879717)
            ·
              refine ⟨3675423220804292660414947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19602257177622894188879717 3675423220804292660414947)
              ·
                refine ⟨5513134831206438990622421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3675423220804292660414947 5513134831206438990622421)
                ·
                  refine ⟨129214097606400913842713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5513134831206438990622421 129214097606400913842713)
                  ·
                    rfl

theorem cell23_2264792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 4, 1, 7].length) (baseStart_2264792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264792 prefixEnd_2264792 := by exact prefixLift 2264792
  have htrace : WordTrace (prefixWord ++ tailWord_2264792) baseStart_2264792 baseEnd_2264792 := by
    simpa [prefixWord, tailWord_2264792, baseEnd_2264792] using wordTrace_append hprefix tailTrace_2264792
  have hstable : (prefixWord ++ tailWord_2264792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264792).length < 2 ^ (prefixWord ++ tailWord_2264792).sum := by decide
  have hdescent : baseEnd_2264792 < baseStart_2264792 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264803 : List Nat := [1, 1, 1, 7, 2, 2, 1, 1, 1, 4, 2]
def baseStart_2264803 : Nat := 118140960795 + 2264803 * 2 ^ 59
def prefixEnd_2264803 : Nat := 4983230072969 + 3 ^ 40 * 2264803 * 2
def baseEnd_2264803 : Nat := 1162932526744807681546867

theorem tailTrace_2264803 : CollatzResearch.WordTrace tailWord_2264803 prefixEnd_2264803 1162932526744807681546867 := by
  unfold tailWord_2264803
  simp only [CollatzResearch.WordTrace]
  refine ⟨82604151614013003402983063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55069434409342002268655375 82604151614013003402983063)
  ·
    refine ⟨123906227421019505104474595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82604151614013003402983063 123906227421019505104474595)
    ·
      refine ⟨185859341131529257656711893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123906227421019505104474595 185859341131529257656711893)
      ·
        refine ⟨4356078307770216976329185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 185859341131529257656711893 4356078307770216976329185)
        ·
          refine ⟨3267058730827662732246889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4356078307770216976329185 3267058730827662732246889)
          ·
            refine ⟨2450294048120747049185167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3267058730827662732246889 2450294048120747049185167)
            ·
              refine ⟨3675441072181120573777751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2450294048120747049185167 3675441072181120573777751)
              ·
                refine ⟨5513161608271680860666627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3675441072181120573777751 5513161608271680860666627)
                ·
                  refine ⟨8269742412407521290999941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5513161608271680860666627 8269742412407521290999941)
                  ·
                    refine ⟨1550576702326410242062489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8269742412407521290999941 1550576702326410242062489)
                    ·
                      refine ⟨1162932526744807681546867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1550576702326410242062489 1162932526744807681546867)
                      ·
                        rfl

theorem cell23_2264803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_2264803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264803 prefixEnd_2264803 := by exact prefixLift 2264803
  have htrace : WordTrace (prefixWord ++ tailWord_2264803) baseStart_2264803 baseEnd_2264803 := by
    simpa [prefixWord, tailWord_2264803, baseEnd_2264803] using wordTrace_append hprefix tailTrace_2264803
  have hstable : (prefixWord ++ tailWord_2264803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264803).length < 2 ^ (prefixWord ++ tailWord_2264803).sum := by decide
  have hdescent : baseEnd_2264803 < baseStart_2264803 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264820 : List Nat := [2, 6, 1, 1, 1, 1, 1, 2, 4, 2, 2]
def baseStart_2264820 : Nat := 118140960795 + 2264820 * 2 ^ 59
def prefixEnd_2264820 : Nat := 4983230072969 + 3 ^ 40 * 2264820 * 2
def baseEnd_2264820 : Nat := 1162941255915934115034289

theorem tailTrace_2264820 : CollatzResearch.WordTrace tailWord_2264820 prefixEnd_2264820 1162941255915934115034289 := by
  unfold tailWord_2264820
  simp only [CollatzResearch.WordTrace]
  refine ⟨41302385827475707653175957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55069847769967610204234609 41302385827475707653175957)
  ·
    refine ⟨1936049335662923796242623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 41302385827475707653175957 1936049335662923796242623)
    ·
      refine ⟨2904074003494385694363935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1936049335662923796242623 2904074003494385694363935)
      ·
        refine ⟨4356111005241578541545903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2904074003494385694363935 4356111005241578541545903)
        ·
          refine ⟨6534166507862367812318855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4356111005241578541545903 6534166507862367812318855)
          ·
            refine ⟨9801249761793551718478283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6534166507862367812318855 9801249761793551718478283)
            ·
              refine ⟨14701874642690327577717425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9801249761793551718478283 14701874642690327577717425)
              ·
                refine ⟨11026405982017745683288069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14701874642690327577717425 11026405982017745683288069)
                ·
                  refine ⟨2067451121628327315616513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11026405982017745683288069 2067451121628327315616513)
                  ·
                    refine ⟨1550588341221245486712385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2067451121628327315616513 1550588341221245486712385)
                    ·
                      refine ⟨1162941255915934115034289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1550588341221245486712385 1162941255915934115034289)
                      ·
                        rfl

theorem cell23_2264820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 2, 4, 2, 2].length) (baseStart_2264820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264820 prefixEnd_2264820 := by exact prefixLift 2264820
  have htrace : WordTrace (prefixWord ++ tailWord_2264820) baseStart_2264820 baseEnd_2264820 := by
    simpa [prefixWord, tailWord_2264820, baseEnd_2264820] using wordTrace_append hprefix tailTrace_2264820
  have hstable : (prefixWord ++ tailWord_2264820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264820).length < 2 ^ (prefixWord ++ tailWord_2264820).sum := by decide
  have hdescent : baseEnd_2264820 < baseStart_2264820 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264899 : List Nat := [1, 1, 1, 3, 1, 6, 2, 2, 6]
def baseStart_2264899 : Nat := 118140960795 + 2264899 * 2 ^ 59
def prefixEnd_2264899 : Nat := 4983230072969 + 3 ^ 40 * 2264899 * 2
def baseEnd_2264899 : Nat := 129220202320848811771825

theorem tailTrace_2264899 : CollatzResearch.WordTrace tailWord_2264899 prefixEnd_2264899 129220202320848811771825 := by
  unfold tailWord_2264899
  simp only [CollatzResearch.WordTrace]
  refine ⟨82607653021665211798477751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55071768681110141198985167 82607653021665211798477751)
  ·
    refine ⟨123911479532497817697716627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82607653021665211798477751 123911479532497817697716627)
    ·
      refine ⟨185867219298746726546574941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123911479532497817697716627 185867219298746726546574941)
      ·
        refine ⟨69700207237030022454965603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 185867219298746726546574941 69700207237030022454965603)
        ·
          refine ⟨104550310855545033682448405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69700207237030022454965603 104550310855545033682448405)
          ·
            refine ⟨4900795821353673453864769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 104550310855545033682448405 4900795821353673453864769)
            ·
              refine ⟨3675596866015255090398577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4900795821353673453864769 3675596866015255090398577)
              ·
                refine ⟨2756697649511441317798933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3675596866015255090398577 2756697649511441317798933)
                ·
                  refine ⟨129220202320848811771825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2756697649511441317798933 129220202320848811771825)
                  ·
                    rfl

theorem cell23_2264899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 2, 6].length) (baseStart_2264899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264899 prefixEnd_2264899 := by exact prefixLift 2264899
  have htrace : WordTrace (prefixWord ++ tailWord_2264899) baseStart_2264899 baseEnd_2264899 := by
    simpa [prefixWord, tailWord_2264899, baseEnd_2264899] using wordTrace_append hprefix tailTrace_2264899
  have hstable : (prefixWord ++ tailWord_2264899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264899).length < 2 ^ (prefixWord ++ tailWord_2264899).sum := by decide
  have hdescent : baseEnd_2264899 < baseStart_2264899 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264903 : List Nat := [1, 1, 4, 1, 2, 1, 6, 2, 1, 4]
def baseStart_2264903 : Nat := 118140960795 + 2264903 * 2 ^ 59
def prefixEnd_2264903 : Nat := 4983230072969 + 3 ^ 40 * 2264903 * 2
def baseEnd_2264903 : Nat := 387661291603419096765469

theorem tailTrace_2264903 : CollatzResearch.WordTrace tailWord_2264903 prefixEnd_2264903 387661291603419096765469 := by
  unfold tailWord_2264903
  simp only [CollatzResearch.WordTrace]
  refine ⟨82607798913650720481623363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55071865942433813654415575 82607798913650720481623363)
  ·
    refine ⟨123911698370476080722435045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82607798913650720481623363 123911698370476080722435045)
    ·
      refine ⟨23233443444464265135456571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123911698370476080722435045 23233443444464265135456571)
      ·
        refine ⟨34850165166696397703184857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23233443444464265135456571 34850165166696397703184857)
        ·
          refine ⟨26137623875022298277388643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34850165166696397703184857 26137623875022298277388643)
          ·
            refine ⟨39206435812533447416082965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26137623875022298277388643 39206435812533447416082965)
            ·
              refine ⟨1837801678712505347628889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39206435812533447416082965 1837801678712505347628889)
              ·
                refine ⟨1378351259034379010721667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1837801678712505347628889 1378351259034379010721667)
                ·
                  refine ⟨2067526888551568516082501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1378351259034379010721667 2067526888551568516082501)
                  ·
                    refine ⟨387661291603419096765469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2067526888551568516082501 387661291603419096765469)
                    ·
                      rfl

theorem cell23_2264903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 6, 2, 1, 4].length) (baseStart_2264903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264903 prefixEnd_2264903 := by exact prefixLift 2264903
  have htrace : WordTrace (prefixWord ++ tailWord_2264903) baseStart_2264903 baseEnd_2264903 := by
    simpa [prefixWord, tailWord_2264903, baseEnd_2264903] using wordTrace_append hprefix tailTrace_2264903
  have hstable : (prefixWord ++ tailWord_2264903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264903).length < 2 ^ (prefixWord ++ tailWord_2264903).sum := by decide
  have hdescent : baseEnd_2264903 < baseStart_2264903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264922 : List Nat := [3, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7]
def baseStart_2264922 : Nat := 118140960795 + 2264922 * 2 ^ 59
def prefixEnd_2264922 : Nat := 4983230072969 + 3 ^ 40 * 2264922 * 2
def baseEnd_2264922 : Nat := 1162993630942692715958819

theorem tailTrace_2264922 : CollatzResearch.WordTrace tailWord_2264922 prefixEnd_2264922 1162993630942692715958819 := by
  unfold tailWord_2264922
  simp only [CollatzResearch.WordTrace]
  refine ⟨20652122975145471681641255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55072327933721257817710013 20652122975145471681641255)
  ·
    refine ⟨30978184462718207522461883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20652122975145471681641255 30978184462718207522461883)
    ·
      refine ⟨46467276694077311283692825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30978184462718207522461883 46467276694077311283692825)
      ·
        refine ⟨34850457520557983462769619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46467276694077311283692825 34850457520557983462769619)
        ·
          refine ⟨52275686280836975194154429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34850457520557983462769619 52275686280836975194154429)
          ·
            refine ⟨19603382355313865697807911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52275686280836975194154429 19603382355313865697807911)
            ·
              refine ⟨29405073532970798546711867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19603382355313865697807911 29405073532970798546711867)
              ·
                refine ⟨44107610299456197820067801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29405073532970798546711867 44107610299456197820067801)
                ·
                  refine ⟨33080707724592148365050851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44107610299456197820067801 33080707724592148365050851)
                  ·
                    refine ⟨49621061586888222547576277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 33080707724592148365050851 49621061586888222547576277)
                    ·
                      refine ⟨1162993630942692715958819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49621061586888222547576277 1162993630942692715958819)
                      ·
                        rfl

theorem cell23_2264922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 1, 1, 2, 1, 7].length) (baseStart_2264922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264922 prefixEnd_2264922 := by exact prefixLift 2264922
  have htrace : WordTrace (prefixWord ++ tailWord_2264922) baseStart_2264922 baseEnd_2264922 := by
    simpa [prefixWord, tailWord_2264922, baseEnd_2264922] using wordTrace_append hprefix tailTrace_2264922
  have hstable : (prefixWord ++ tailWord_2264922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264922).length < 2 ^ (prefixWord ++ tailWord_2264922).sum := by decide
  have hdescent : baseEnd_2264922 < baseStart_2264922 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264929 : List Nat := [1, 2, 3, 1, 1, 1, 4, 4, 1, 5]
def baseStart_2264929 : Nat := 118140960795 + 2264929 * 2 ^ 59
def prefixEnd_2264929 : Nat := 4983230072969 + 3 ^ 40 * 2264929 * 2
def baseEnd_2264929 : Nat := 387665741769091396190429

theorem tailTrace_2264929 : CollatzResearch.WordTrace tailWord_2264929 prefixEnd_2264929 387665741769091396190429 := by
  unfold tailWord_2264929
  simp only [CollatzResearch.WordTrace]
  refine ⟨82608747211556526922069841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55072498141037684614713227 82608747211556526922069841)
  ·
    refine ⟨61956560408667395191552381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82608747211556526922069841 61956560408667395191552381)
    ·
      refine ⟨23233710153250273196832143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61956560408667395191552381 23233710153250273196832143)
      ·
        refine ⟨34850565229875409795248215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23233710153250273196832143 34850565229875409795248215)
        ·
          refine ⟨52275847844813114692872323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34850565229875409795248215 52275847844813114692872323)
          ·
            refine ⟨78413771767219672039308485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52275847844813114692872323 78413771767219672039308485)
            ·
              refine ⟨14702582206353688507370341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78413771767219672039308485 14702582206353688507370341)
              ·
                refine ⟨2756734163691316595131939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14702582206353688507370341 2756734163691316595131939)
                ·
                  refine ⟨4135101245536974892697909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2756734163691316595131939 4135101245536974892697909)
                  ·
                    refine ⟨387665741769091396190429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4135101245536974892697909 387665741769091396190429)
                    ·
                      rfl

theorem cell23_2264929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_2264929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264929 prefixEnd_2264929 := by exact prefixLift 2264929
  have htrace : WordTrace (prefixWord ++ tailWord_2264929) baseStart_2264929 baseEnd_2264929 := by
    simpa [prefixWord, tailWord_2264929, baseEnd_2264929] using wordTrace_append hprefix tailTrace_2264929
  have hstable : (prefixWord ++ tailWord_2264929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264929).length < 2 ^ (prefixWord ++ tailWord_2264929).sum := by decide
  have hdescent : baseEnd_2264929 < baseStart_2264929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264936 : List Nat := [2, 1, 4, 2, 1, 1, 3, 1, 1, 5, 2]
def baseStart_2264936 : Nat := 118140960795 + 2264936 * 2 ^ 59
def prefixEnd_2264936 : Nat := 4983230072969 + 3 ^ 40 * 2264936 * 2
def baseEnd_2264936 : Nat := 1163000819671855661183755

theorem tailTrace_2264936 : CollatzResearch.WordTrace tailWord_2264936 prefixEnd_2264936 1163000819671855661183755 := by
  unfold tailWord_2264936
  simp only [CollatzResearch.WordTrace]
  refine ⟨41304501261265583558787331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55072668348354111411716441 41304501261265583558787331)
  ·
    refine ⟨61956751891898375338180997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41304501261265583558787331 61956751891898375338180997)
    ·
      refine ⟨11616890979730945375908937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61956751891898375338180997 11616890979730945375908937)
      ·
        refine ⟨8712668234798209031931703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11616890979730945375908937 8712668234798209031931703)
        ·
          refine ⟨13069002352197313547897555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8712668234798209031931703 13069002352197313547897555)
          ·
            refine ⟨19603503528295970321846333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13069002352197313547897555 19603503528295970321846333)
            ·
              refine ⟨7351313823110988870692375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19603503528295970321846333 7351313823110988870692375)
              ·
                refine ⟨11026970734666483306038563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7351313823110988870692375 11026970734666483306038563)
                ·
                  refine ⟨16540456101999724959057845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11026970734666483306038563 16540456101999724959057845)
                  ·
                    refine ⟨1550667759562474214911673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16540456101999724959057845 1550667759562474214911673)
                    ·
                      refine ⟨1163000819671855661183755, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1550667759562474214911673 1163000819671855661183755)
                      ·
                        rfl

theorem cell23_2264936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 1, 5, 2].length) (baseStart_2264936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264936 prefixEnd_2264936 := by exact prefixLift 2264936
  have htrace : WordTrace (prefixWord ++ tailWord_2264936) baseStart_2264936 baseEnd_2264936 := by
    simpa [prefixWord, tailWord_2264936, baseEnd_2264936] using wordTrace_append hprefix tailTrace_2264936
  have hstable : (prefixWord ++ tailWord_2264936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264936).length < 2 ^ (prefixWord ++ tailWord_2264936).sum := by decide
  have hdescent : baseEnd_2264936 < baseStart_2264936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264950 : List Nat := [5, 1, 1, 3, 3, 1, 1, 2, 6]
def baseStart_2264950 : Nat := 118140960795 + 2264950 * 2 ^ 59
def prefixEnd_2264950 : Nat := 4983230072969 + 3 ^ 40 * 2264950 * 2
def baseEnd_2264950 : Nat := 129223112044557622934299

theorem tailTrace_2264950 : CollatzResearch.WordTrace tailWord_2264950 prefixEnd_2264950 129223112044557622934299 := by
  unfold tailWord_2264950
  simp only [CollatzResearch.WordTrace]
  refine ⟨5163094571530027969286519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55073008762986965005722869 5163094571530027969286519)
  ·
    refine ⟨7744641857295041953929779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5163094571530027969286519 7744641857295041953929779)
    ·
      refine ⟨11616962785942562930894669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7744641857295041953929779 11616962785942562930894669)
      ·
        refine ⟨4356361044728461099085501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11616962785942562930894669 4356361044728461099085501)
        ·
          refine ⟨1633635391773172912157063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4356361044728461099085501 1633635391773172912157063)
          ·
            refine ⟨2450453087659759368235595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1633635391773172912157063 2450453087659759368235595)
            ·
              refine ⟨3675679631489639052353393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2450453087659759368235595 3675679631489639052353393)
              ·
                refine ⟨2756759723617229289265045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3675679631489639052353393 2756759723617229289265045)
                ·
                  refine ⟨129223112044557622934299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2756759723617229289265045 129223112044557622934299)
                  ·
                    rfl

theorem cell23_2264950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 2, 6].length) (baseStart_2264950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264950 prefixEnd_2264950 := by exact prefixLift 2264950
  have htrace : WordTrace (prefixWord ++ tailWord_2264950) baseStart_2264950 baseEnd_2264950 := by
    simpa [prefixWord, tailWord_2264950, baseEnd_2264950] using wordTrace_append hprefix tailTrace_2264950
  have hstable : (prefixWord ++ tailWord_2264950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264950).length < 2 ^ (prefixWord ++ tailWord_2264950).sum := by decide
  have hdescent : baseEnd_2264950 < baseStart_2264950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264969 : List Nat := [1, 2, 1, 1, 5, 1, 3, 2, 1, 1, 5]
def baseStart_2264969 : Nat := 118140960795 + 2264969 * 2 ^ 59
def prefixEnd_2264969 : Nat := 4983230072969 + 3 ^ 40 * 2264969 * 2
def baseEnd_2264969 : Nat := 1163017764533454032071103

theorem tailTrace_2264969 : CollatzResearch.WordTrace tailWord_2264969 prefixEnd_2264969 1163017764533454032071103 := by
  unfold tailWord_2264969
  simp only [CollatzResearch.WordTrace]
  refine ⟨82610206131411613753525961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55073470754274409169017307 82610206131411613753525961)
  ·
    refine ⟨61957654598558710315144471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82610206131411613753525961 61957654598558710315144471)
    ·
      refine ⟨92936481897838065472716707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61957654598558710315144471 92936481897838065472716707)
      ·
        refine ⟨139404722846757098209075061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92936481897838065472716707 139404722846757098209075061)
        ·
          refine ⟨13069192766883477957100787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 139404722846757098209075061 13069192766883477957100787)
          ·
            refine ⟨19603789150325216935651181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13069192766883477957100787 19603789150325216935651181)
            ·
              refine ⟨7351420931371956350869193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19603789150325216935651181 7351420931371956350869193)
              ·
                refine ⟨5513565698528967263151895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7351420931371956350869193 5513565698528967263151895)
                ·
                  refine ⟨8270348547793450894727843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5513565698528967263151895 8270348547793450894727843)
                  ·
                    refine ⟨12405522821690176342091765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8270348547793450894727843 12405522821690176342091765)
                    ·
                      refine ⟨1163017764533454032071103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12405522821690176342091765 1163017764533454032071103)
                      ·
                        rfl

theorem cell23_2264969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 3, 2, 1, 1, 5].length) (baseStart_2264969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264969 prefixEnd_2264969 := by exact prefixLift 2264969
  have htrace : WordTrace (prefixWord ++ tailWord_2264969) baseStart_2264969 baseEnd_2264969 := by
    simpa [prefixWord, tailWord_2264969, baseEnd_2264969] using wordTrace_append hprefix tailTrace_2264969
  have hstable : (prefixWord ++ tailWord_2264969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264969).length < 2 ^ (prefixWord ++ tailWord_2264969).sum := by decide
  have hdescent : baseEnd_2264969 < baseStart_2264969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264972 : List Nat := [2, 2, 1, 2, 1, 2, 1, 12]
def baseStart_2264972 : Nat := 118140960795 + 2264972 * 2 ^ 59
def prefixEnd_2264972 : Nat := 4983230072969 + 3 ^ 40 * 2264972 * 2
def baseEnd_2264972 : Nat := 43074789073163611864207

theorem tailTrace_2264972 : CollatzResearch.WordTrace tailWord_2264972 prefixEnd_2264972 43074789073163611864207 := by
  unfold tailWord_2264972
  simp only [CollatzResearch.WordTrace]
  refine ⟨41305157775200372632942585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55073543700267163510590113 41305157775200372632942585)
  ·
    refine ⟨30978868331400279474706939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41305157775200372632942585 30978868331400279474706939)
    ·
      refine ⟨46468302497100419212060409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30978868331400279474706939 46468302497100419212060409)
      ·
        refine ⟨34851226872825314409045307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46468302497100419212060409 34851226872825314409045307)
        ·
          refine ⟨52276840309237971613567961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34851226872825314409045307 52276840309237971613567961)
          ·
            refine ⟨39207630231928478710175971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52276840309237971613567961 39207630231928478710175971)
            ·
              refine ⟨58811445347892718065263957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39207630231928478710175971 58811445347892718065263957)
              ·
                refine ⟨43074789073163611864207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 58811445347892718065263957 43074789073163611864207)
                ·
                  rfl

theorem cell23_2264972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 12].length) (baseStart_2264972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264972 prefixEnd_2264972 := by exact prefixLift 2264972
  have htrace : WordTrace (prefixWord ++ tailWord_2264972) baseStart_2264972 baseEnd_2264972 := by
    simpa [prefixWord, tailWord_2264972, baseEnd_2264972] using wordTrace_append hprefix tailTrace_2264972
  have hstable : (prefixWord ++ tailWord_2264972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264972).length < 2 ^ (prefixWord ++ tailWord_2264972).sum := by decide
  have hdescent : baseEnd_2264972 < baseStart_2264972 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264983 : List Nat := [1, 1, 3, 3, 1, 3, 2, 2, 3, 2, 2]
def baseStart_2264983 : Nat := 118140960795 + 2264983 * 2 ^ 59
def prefixEnd_2264983 : Nat := 4983230072969 + 3 ^ 40 * 2264983 * 2
def baseEnd_2264983 : Nat := 1163024953262616977296039

theorem tailTrace_2264983 : CollatzResearch.WordTrace tailWord_2264983 prefixEnd_2264983 1163024953262616977296039 := by
  unfold tailWord_2264983
  simp only [CollatzResearch.WordTrace]
  refine ⟨82610716753360894144535603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55073811168907262763023735 82610716753360894144535603)
  ·
    refine ⟨123916075130041341216803405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82610716753360894144535603 123916075130041341216803405)
    ·
      refine ⟨46468528173765502956301277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123916075130041341216803405 46468528173765502956301277)
      ·
        refine ⟨17425698065162063608612979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46468528173765502956301277 17425698065162063608612979)
        ·
          refine ⟨26138547097743095412919469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17425698065162063608612979 26138547097743095412919469)
          ·
            refine ⟨9801955161653660779844801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26138547097743095412919469 9801955161653660779844801)
            ·
              refine ⟨7351466371240245584883601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9801955161653660779844801 7351466371240245584883601)
              ·
                refine ⟨5513599778430184188662701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7351466371240245584883601 5513599778430184188662701)
                ·
                  refine ⟨2067599916911319070748513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5513599778430184188662701 2067599916911319070748513)
                  ·
                    refine ⟨1550699937683489303061385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2067599916911319070748513 1550699937683489303061385)
                    ·
                      refine ⟨1163024953262616977296039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1550699937683489303061385 1163024953262616977296039)
                      ·
                        rfl

theorem cell23_2264983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 2, 2, 3, 2, 2].length) (baseStart_2264983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264983 prefixEnd_2264983 := by exact prefixLift 2264983
  have htrace : WordTrace (prefixWord ++ tailWord_2264983) baseStart_2264983 baseEnd_2264983 := by
    simpa [prefixWord, tailWord_2264983, baseEnd_2264983] using wordTrace_append hprefix tailTrace_2264983
  have hstable : (prefixWord ++ tailWord_2264983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264983).length < 2 ^ (prefixWord ++ tailWord_2264983).sum := by decide
  have hdescent : baseEnd_2264983 < baseStart_2264983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264989 : List Nat := [1, 4, 2, 1, 2, 3, 1, 9]
def baseStart_2264989 : Nat := 118140960795 + 2264989 * 2 ^ 59
def prefixEnd_2264989 : Nat := 4983230072969 + 3 ^ 40 * 2264989 * 2
def baseEnd_2264989 : Nat := 43075112375797924215593

theorem tailTrace_2264989 : CollatzResearch.WordTrace tailWord_2264989 prefixEnd_2264989 43075112375797924215593 := by
  unfold tailWord_2264989
  simp only [CollatzResearch.WordTrace]
  refine ⟨82610935591339157169254021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55073957060892771446169347 82610935591339157169254021)
  ·
    refine ⟨15489550423376091969235129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82610935591339157169254021 15489550423376091969235129)
    ·
      refine ⟨11617162817532068976926347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15489550423376091969235129 11617162817532068976926347)
      ·
        refine ⟨17425744226298103465389521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11617162817532068976926347 17425744226298103465389521)
        ·
          refine ⟨13069308169723577599042141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17425744226298103465389521 13069308169723577599042141)
          ·
            refine ⟨4900990563646341599640803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13069308169723577599042141 4900990563646341599640803)
            ·
              refine ⟨7351485845469512399461205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4900990563646341599640803 7351485845469512399461205)
              ·
                refine ⟨43075112375797924215593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7351485845469512399461205 43075112375797924215593)
                ·
                  rfl

theorem cell23_2264989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 3, 1, 9].length) (baseStart_2264989 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264989 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264989 prefixEnd_2264989 := by exact prefixLift 2264989
  have htrace : WordTrace (prefixWord ++ tailWord_2264989) baseStart_2264989 baseEnd_2264989 := by
    simpa [prefixWord, tailWord_2264989, baseEnd_2264989] using wordTrace_append hprefix tailTrace_2264989
  have hstable : (prefixWord ++ tailWord_2264989).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264989).length < 2 ^ (prefixWord ++ tailWord_2264989).sum := by decide
  have hdescent : baseEnd_2264989 < baseStart_2264989 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2264994 : List Nat := [3, 3, 1, 2, 4, 1, 1, 3, 1, 1, 3]
def baseStart_2264994 : Nat := 118140960795 + 2264994 * 2 ^ 59
def prefixEnd_2264994 : Nat := 4983230072969 + 3 ^ 40 * 2264994 * 2
def baseEnd_2264994 : Nat := 1163030601549816434258489

theorem tailTrace_2264994 : CollatzResearch.WordTrace tailWord_2264994 prefixEnd_2264994 1163030601549816434258489 := by
  unfold tailWord_2264994
  simp only [CollatzResearch.WordTrace]
  refine ⟨20652779489080260755796509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55074078637547362015457357 20652779489080260755796509)
  ·
    refine ⟨7744792308405097783423691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20652779489080260755796509 7744792308405097783423691)
    ·
      refine ⟨11617188462607646675135537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7744792308405097783423691 11617188462607646675135537)
      ·
        refine ⟨8712891346955735006351653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11617188462607646675135537 8712891346955735006351653)
        ·
          refine ⟨1633667127554200313690935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8712891346955735006351653 1633667127554200313690935)
          ·
            refine ⟨2450500691331300470536403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1633667127554200313690935 2450500691331300470536403)
            ·
              refine ⟨3675751036996950705804605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2450500691331300470536403 3675751036996950705804605)
              ·
                refine ⟨1378406638873856514676727, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3675751036996950705804605 1378406638873856514676727)
                ·
                  refine ⟨2067609958310784772015091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1378406638873856514676727 2067609958310784772015091)
                  ·
                    refine ⟨3101414937466177158022637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2067609958310784772015091 3101414937466177158022637)
                    ·
                      refine ⟨1163030601549816434258489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3101414937466177158022637 1163030601549816434258489)
                      ·
                        rfl

theorem cell23_2264994_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 3, 1, 1, 3].length) (baseStart_2264994 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2264994 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2264994 prefixEnd_2264994 := by exact prefixLift 2264994
  have htrace : WordTrace (prefixWord ++ tailWord_2264994) baseStart_2264994 baseEnd_2264994 := by
    simpa [prefixWord, tailWord_2264994, baseEnd_2264994] using wordTrace_append hprefix tailTrace_2264994
  have hstable : (prefixWord ++ tailWord_2264994).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2264994).length < 2 ^ (prefixWord ++ tailWord_2264994).sum := by decide
  have hdescent : baseEnd_2264994 < baseStart_2264994 := by decide
  rcases family_descends (prefixWord ++ tailWord_2264994) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265016 : List Nat := [2, 1, 2, 1, 2, 3, 1, 3, 4, 1, 3]
def baseStart_2265016 : Nat := 118140960795 + 2265016 * 2 ^ 59
def prefixEnd_2265016 : Nat := 4983230072969 + 3 ^ 40 * 2265016 * 2
def baseEnd_2265016 : Nat := 1163041898124215348183387

theorem tailTrace_2265016 : CollatzResearch.WordTrace tailWord_2265016 prefixEnd_2265016 1163041898124215348183387 := by
  unfold tailWord_2265016
  simp only [CollatzResearch.WordTrace]
  refine ⟨41305960181120670390243451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55074613574827560520324601 41305960181120670390243451)
  ·
    refine ⟨61958940271681005585365177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41305960181120670390243451 61958940271681005585365177)
    ·
      refine ⟨46469205203760754189023883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61958940271681005585365177 46469205203760754189023883)
      ·
        refine ⟨69703807805641131283535825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46469205203760754189023883 69703807805641131283535825)
        ·
          refine ⟨52277855854230848462651869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69703807805641131283535825 52277855854230848462651869)
          ·
            refine ⟨19604195945336568173494451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52277855854230848462651869 19604195945336568173494451)
            ·
              refine ⟨29406293918004852260241677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19604195945336568173494451 29406293918004852260241677)
              ·
                refine ⟨11027360219251819597590629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29406293918004852260241677 11027360219251819597590629)
                ·
                  refine ⟨2067630041109716174548243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11027360219251819597590629 2067630041109716174548243)
                  ·
                    refine ⟨3101445061664574261822365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2067630041109716174548243 3101445061664574261822365)
                    ·
                      refine ⟨1163041898124215348183387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3101445061664574261822365 1163041898124215348183387)
                      ·
                        rfl

theorem cell23_2265016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 4, 1, 3].length) (baseStart_2265016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265016 prefixEnd_2265016 := by exact prefixLift 2265016
  have htrace : WordTrace (prefixWord ++ tailWord_2265016) baseStart_2265016 baseEnd_2265016 := by
    simpa [prefixWord, tailWord_2265016, baseEnd_2265016] using wordTrace_append hprefix tailTrace_2265016
  have hstable : (prefixWord ++ tailWord_2265016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265016).length < 2 ^ (prefixWord ++ tailWord_2265016).sum := by decide
  have hdescent : baseEnd_2265016 < baseStart_2265016 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265017 : List Nat := [1, 2, 1, 4, 2, 1, 5, 2, 1, 2, 2]
def baseStart_2265017 : Nat := 118140960795 + 2265017 * 2 ^ 59
def prefixEnd_2265017 : Nat := 4983230072969 + 3 ^ 40 * 2265017 * 2
def baseEnd_2265017 : Nat := 1163042411604869844270883

theorem tailTrace_2265017 : CollatzResearch.WordTrace tailWord_2265017 prefixEnd_2265017 1163042411604869844270883 := by
  unfold tailWord_2265017
  simp only [CollatzResearch.WordTrace]
  refine ⟨82611956835237717951273305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55074637890158478634182203 82611956835237717951273305)
  ·
    refine ⟨61958967626428288463454979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82611956835237717951273305 61958967626428288463454979)
    ·
      refine ⟨92938451439642432695182469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61958967626428288463454979 92938451439642432695182469)
      ·
        refine ⟨17425959644932956130346713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92938451439642432695182469 17425959644932956130346713)
        ·
          refine ⟨13069469733699717097760035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17425959644932956130346713 13069469733699717097760035)
          ·
            refine ⟨19604204600549575646640053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13069469733699717097760035 19604204600549575646640053)
            ·
              refine ⟨1837894181301522716872505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19604204600549575646640053 1837894181301522716872505)
              ·
                refine ⟨1378420635976142037654379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1837894181301522716872505 1378420635976142037654379)
                ·
                  refine ⟨2067630953964213056481569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1378420635976142037654379 2067630953964213056481569)
                  ·
                    refine ⟨1550723215473159792361177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2067630953964213056481569 1550723215473159792361177)
                    ·
                      refine ⟨1163042411604869844270883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1550723215473159792361177 1163042411604869844270883)
                      ·
                        rfl

theorem cell23_2265017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_2265017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265017 prefixEnd_2265017 := by exact prefixLift 2265017
  have htrace : WordTrace (prefixWord ++ tailWord_2265017) baseStart_2265017 baseEnd_2265017 := by
    simpa [prefixWord, tailWord_2265017, baseEnd_2265017] using wordTrace_append hprefix tailTrace_2265017
  have hstable : (prefixWord ++ tailWord_2265017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265017).length < 2 ^ (prefixWord ++ tailWord_2265017).sum := by decide
  have hdescent : baseEnd_2265017 < baseStart_2265017 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265060 : List Nat := [2, 3, 1, 1, 1, 1, 7, 1, 1, 3, 2]
def baseStart_2265060 : Nat := 118140960795 + 2265060 * 2 ^ 59
def prefixEnd_2265060 : Nat := 4983230072969 + 3 ^ 40 * 2265060 * 2
def baseEnd_2265060 : Nat := 1163064491273013176033185

theorem tailTrace_2265060 : CollatzResearch.WordTrace tailWord_2265060 prefixEnd_2265060 1163064491273013176033185 := by
  unfold tailWord_2265060
  simp only [CollatzResearch.WordTrace]
  refine ⟨41306762587040968147544317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55075683449387957530059089 41306762587040968147544317)
  ·
    refine ⟨15490035970140363055329119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41306762587040968147544317 15490035970140363055329119)
    ·
      refine ⟨23235053955210544582993679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15490035970140363055329119 23235053955210544582993679)
      ·
        refine ⟨34852580932815816874490519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23235053955210544582993679 34852580932815816874490519)
        ·
          refine ⟨52278871399223725311735779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34852580932815816874490519 52278871399223725311735779)
          ·
            refine ⟨78418307098835587967603669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52278871399223725311735779 78418307098835587967603669)
            ·
              refine ⟨1837929072628959092990711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 78418307098835587967603669 1837929072628959092990711)
              ·
                refine ⟨2756893608943438639486067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1837929072628959092990711 2756893608943438639486067)
                ·
                  refine ⟨4135340413415157959229101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2756893608943438639486067 4135340413415157959229101)
                  ·
                    refine ⟨1550752655030684234710913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4135340413415157959229101 1550752655030684234710913)
                    ·
                      refine ⟨1163064491273013176033185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1550752655030684234710913 1163064491273013176033185)
                      ·
                        rfl

theorem cell23_2265060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 7, 1, 1, 3, 2].length) (baseStart_2265060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265060 prefixEnd_2265060 := by exact prefixLift 2265060
  have htrace : WordTrace (prefixWord ++ tailWord_2265060) baseStart_2265060 baseEnd_2265060 := by
    simpa [prefixWord, tailWord_2265060, baseEnd_2265060] using wordTrace_append hprefix tailTrace_2265060
  have hstable : (prefixWord ++ tailWord_2265060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265060).length < 2 ^ (prefixWord ++ tailWord_2265060).sum := by decide
  have hdescent : baseEnd_2265060 < baseStart_2265060 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265124 : List Nat := [2, 3, 1, 4, 2, 2, 1, 2, 2, 2, 2]
def baseStart_2265124 : Nat := 118140960795 + 2265124 * 2 ^ 59
def prefixEnd_2265124 : Nat := 4983230072969 + 3 ^ 40 * 2265124 * 2
def baseEnd_2265124 : Nat := 1163097354034900925632891

theorem tailTrace_2265124 : CollatzResearch.WordTrace tailWord_2265124 prefixEnd_2265124 1163097354034900925632891 := by
  unfold tailWord_2265124
  simp only [CollatzResearch.WordTrace]
  refine ⟨41307929722925037612709213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55077239630566716816945617 41307929722925037612709213)
  ·
    refine ⟨15490473646096889104765955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41307929722925037612709213 15490473646096889104765955)
    ·
      refine ⟨23235710469145333657148933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15490473646096889104765955 23235710469145333657148933)
      ·
        refine ⟨4356695712964750060715425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23235710469145333657148933 4356695712964750060715425)
        ·
          refine ⟨3267521784723562545536569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4356695712964750060715425 3267521784723562545536569)
          ·
            refine ⟨2450641338542671909152427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3267521784723562545536569 2450641338542671909152427)
            ·
              refine ⟨3675962007814007863728641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2450641338542671909152427 3675962007814007863728641)
              ·
                refine ⟨2756971505860505897796481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3675962007814007863728641 2756971505860505897796481)
                ·
                  refine ⟨2067728629395379423347361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2756971505860505897796481 2067728629395379423347361)
                  ·
                    refine ⟨1550796472046534567510521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2067728629395379423347361 1550796472046534567510521)
                    ·
                      refine ⟨1163097354034900925632891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1550796472046534567510521 1163097354034900925632891)
                      ·
                        rfl

theorem cell23_2265124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_2265124 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265124 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265124 prefixEnd_2265124 := by exact prefixLift 2265124
  have htrace : WordTrace (prefixWord ++ tailWord_2265124) baseStart_2265124 baseEnd_2265124 := by
    simpa [prefixWord, tailWord_2265124, baseEnd_2265124] using wordTrace_append hprefix tailTrace_2265124
  have hstable : (prefixWord ++ tailWord_2265124).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265124).length < 2 ^ (prefixWord ++ tailWord_2265124).sum := by decide
  have hdescent : baseEnd_2265124 < baseStart_2265124 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265223 : List Nat := [1, 1, 4, 2, 1, 1, 2, 3, 1, 5, 2]
def baseStart_2265223 : Nat := 118140960795 + 2265223 * 2 ^ 59
def prefixEnd_2265223 : Nat := 4983230072969 + 3 ^ 40 * 2265223 * 2
def baseEnd_2265223 : Nat := 1163148188619696038294935

theorem tailTrace_2265223 : CollatzResearch.WordTrace tailWord_2265223 prefixEnd_2265223 1163148188619696038294935 := by
  unfold tailWord_2265223
  simp only [CollatzResearch.WordTrace]
  refine ⟨82619470272491415133272323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55079646848327610088848215 82619470272491415133272323)
  ·
    refine ⟨123929205408737122699908485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82619470272491415133272323 123929205408737122699908485)
    ·
      refine ⟨23236726014138210506232841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123929205408737122699908485 23236726014138210506232841)
      ·
        refine ⟨17427544510603657879674631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23236726014138210506232841 17427544510603657879674631)
        ·
          refine ⟨26141316765905486819511947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17427544510603657879674631 26141316765905486819511947)
          ·
            refine ⟨39211975148858230229267921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26141316765905486819511947 39211975148858230229267921)
            ·
              refine ⟨29408981361643672671950941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39211975148858230229267921 29408981361643672671950941)
              ·
                refine ⟨11028368010616377251981603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29408981361643672671950941 11028368010616377251981603)
                ·
                  refine ⟨16542552015924565877972405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11028368010616377251981603 16542552015924565877972405)
                  ·
                    refine ⟨1550864251492928051059913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16542552015924565877972405 1550864251492928051059913)
                    ·
                      refine ⟨1163148188619696038294935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1550864251492928051059913 1163148188619696038294935)
                      ·
                        rfl

theorem cell23_2265223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 1, 5, 2].length) (baseStart_2265223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265223 prefixEnd_2265223 := by exact prefixLift 2265223
  have htrace : WordTrace (prefixWord ++ tailWord_2265223) baseStart_2265223 baseEnd_2265223 := by
    simpa [prefixWord, tailWord_2265223, baseEnd_2265223] using wordTrace_append hprefix tailTrace_2265223
  have hstable : (prefixWord ++ tailWord_2265223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265223).length < 2 ^ (prefixWord ++ tailWord_2265223).sum := by decide
  have hdescent : baseEnd_2265223 < baseStart_2265223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265268 : List Nat := [2, 5, 3, 1, 2, 1, 1, 1, 2, 2, 3]
def baseStart_2265268 : Nat := 118140960795 + 2265268 * 2 ^ 59
def prefixEnd_2265268 : Nat := 4983230072969 + 3 ^ 40 * 2265268 * 2
def baseEnd_2265268 : Nat := 1163171295249148362232229

theorem tailTrace_2265268 : CollatzResearch.WordTrace tailWord_2265268 prefixEnd_2265268 1163171295249148362232229 := by
  unfold tailWord_2265268
  simp only [CollatzResearch.WordTrace]
  refine ⟨41310555778664193909330229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55080741038218925212440305 41310555778664193909330229)
  ·
    refine ⟨3872864604249768178999709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41310555778664193909330229 3872864604249768178999709)
    ·
      refine ⟨1452324226593663067124891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3872864604249768178999709 1452324226593663067124891)
      ·
        refine ⟨2178486339890494600687337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1452324226593663067124891 2178486339890494600687337)
        ·
          refine ⟨1633864754917870950515503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2178486339890494600687337 1633864754917870950515503)
          ·
            refine ⟨2450797132376806425773255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1633864754917870950515503 2450797132376806425773255)
            ·
              refine ⟨3676195698565209638659883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2450797132376806425773255 3676195698565209638659883)
              ·
                refine ⟨5514293547847814457989825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3676195698565209638659883 5514293547847814457989825)
                ·
                  refine ⟨4135720160885860843492369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5514293547847814457989825 4135720160885860843492369)
                  ·
                    refine ⟨3101790120664395632619277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4135720160885860843492369 3101790120664395632619277)
                    ·
                      refine ⟨1163171295249148362232229, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3101790120664395632619277 1163171295249148362232229)
                      ·
                        rfl

theorem cell23_2265268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 1, 2, 2, 3].length) (baseStart_2265268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265268 prefixEnd_2265268 := by exact prefixLift 2265268
  have htrace : WordTrace (prefixWord ++ tailWord_2265268) baseStart_2265268 baseEnd_2265268 := by
    simpa [prefixWord, tailWord_2265268, baseEnd_2265268] using wordTrace_append hprefix tailTrace_2265268
  have hstable : (prefixWord ++ tailWord_2265268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265268).length < 2 ^ (prefixWord ++ tailWord_2265268).sum := by decide
  have hdescent : baseEnd_2265268 < baseStart_2265268 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265273 : List Nat := [1, 2, 1, 4, 1, 2, 1, 3, 3, 2, 3]
def baseStart_2265273 : Nat := 118140960795 + 2265273 * 2 ^ 59
def prefixEnd_2265273 : Nat := 4983230072969 + 3 ^ 40 * 2265273 * 2
def baseEnd_2265273 : Nat := 1163173862652420842669705

theorem tailTrace_2265273 : CollatzResearch.WordTrace tailWord_2265273 prefixEnd_2265273 1163173862652420842669705 := by
  unfold tailWord_2265273
  simp only [CollatzResearch.WordTrace]
  refine ⟨82621293922310273672592473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55080862614873515781728315 82621293922310273672592473)
  ·
    refine ⟨61965970441732705254444355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82621293922310273672592473 61965970441732705254444355)
    ·
      refine ⟨92948955662599057881666533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61965970441732705254444355 92948955662599057881666533)
      ·
        refine ⟨17427929186737323352812475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92948955662599057881666533 17427929186737323352812475)
        ·
          refine ⟨26141893780105985029218713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17427929186737323352812475 26141893780105985029218713)
          ·
            refine ⟨19606420335079488771914035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26141893780105985029218713 19606420335079488771914035)
            ·
              refine ⟨29409630502619233157871053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19606420335079488771914035 29409630502619233157871053)
              ·
                refine ⟨11028611438482212434201645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29409630502619233157871053 11028611438482212434201645)
                ·
                  refine ⟨4135729289430829662825617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11028611438482212434201645 4135729289430829662825617)
                  ·
                    refine ⟨3101796967073122247119213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4135729289430829662825617 3101796967073122247119213)
                    ·
                      refine ⟨1163173862652420842669705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3101796967073122247119213 1163173862652420842669705)
                      ·
                        rfl

theorem cell23_2265273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_2265273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265273 prefixEnd_2265273 := by exact prefixLift 2265273
  have htrace : WordTrace (prefixWord ++ tailWord_2265273) baseStart_2265273 baseEnd_2265273 := by
    simpa [prefixWord, tailWord_2265273, baseEnd_2265273] using wordTrace_append hprefix tailTrace_2265273
  have hstable : (prefixWord ++ tailWord_2265273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265273).length < 2 ^ (prefixWord ++ tailWord_2265273).sum := by decide
  have hdescent : baseEnd_2265273 < baseStart_2265273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265281 : List Nat := [1, 2, 6, 1, 2, 1, 2, 3, 1, 1, 3]
def baseStart_2265281 : Nat := 118140960795 + 2265281 * 2 ^ 59
def prefixEnd_2265281 : Nat := 4983230072969 + 3 ^ 40 * 2265281 * 2
def baseEnd_2265281 : Nat := 1163177970497656811369669

theorem tailTrace_2265281 : CollatzResearch.WordTrace tailWord_2265281 prefixEnd_2265281 1163177970497656811369669 := by
  unfold tailWord_2265281
  simp only [CollatzResearch.WordTrace]
  refine ⟨82621585706281291038883697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55081057137520860692589131 82621585706281291038883697)
  ·
    refine ⟨61966189279710968279162773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82621585706281291038883697 61966189279710968279162773)
    ·
      refine ⟨2904665122486451638085755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 61966189279710968279162773 2904665122486451638085755)
      ·
        refine ⟨4356997683729677457128633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2904665122486451638085755 4356997683729677457128633)
        ·
          refine ⟨3267748262797258092846475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4356997683729677457128633 3267748262797258092846475)
          ·
            refine ⟨4901622394195887139269713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3267748262797258092846475 4901622394195887139269713)
            ·
              refine ⟨3676216795646915354452285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4901622394195887139269713 3676216795646915354452285)
              ·
                refine ⟨1378581298367593257919607, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3676216795646915354452285 1378581298367593257919607)
                ·
                  refine ⟨2067871947551389886879411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1378581298367593257919607 2067871947551389886879411)
                  ·
                    refine ⟨3101807921327084830319117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2067871947551389886879411 3101807921327084830319117)
                    ·
                      refine ⟨1163177970497656811369669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3101807921327084830319117 1163177970497656811369669)
                      ·
                        rfl

theorem cell23_2265281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 3, 1, 1, 3].length) (baseStart_2265281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265281 prefixEnd_2265281 := by exact prefixLift 2265281
  have htrace : WordTrace (prefixWord ++ tailWord_2265281) baseStart_2265281 baseEnd_2265281 := by
    simpa [prefixWord, tailWord_2265281, baseEnd_2265281] using wordTrace_append hprefix tailTrace_2265281
  have hstable : (prefixWord ++ tailWord_2265281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265281).length < 2 ^ (prefixWord ++ tailWord_2265281).sum := by decide
  have hdescent : baseEnd_2265281 < baseStart_2265281 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265290 : List Nat := [3, 1, 2, 1, 3, 1, 3, 3, 1, 2, 3]
def baseStart_2265290 : Nat := 118140960795 + 2265290 * 2 ^ 59
def prefixEnd_2265290 : Nat := 4983230072969 + 3 ^ 40 * 2265290 * 2
def baseEnd_2265290 : Nat := 1163182591823547276157127

theorem tailTrace_2265290 : CollatzResearch.WordTrace tailWord_2265290 prefixEnd_2265290 1163182591823547276157127 := by
  unfold tailWord_2265290
  simp only [CollatzResearch.WordTrace]
  refine ⟨20655478490812171393990331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55081275975499123717307549 20655478490812171393990331)
  ·
    refine ⟨30983217736218257090985497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20655478490812171393990331 30983217736218257090985497)
    ·
      refine ⟨23237413302163692818239123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30983217736218257090985497 23237413302163692818239123)
      ·
        refine ⟨34856119953245539227358685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23237413302163692818239123 34856119953245539227358685)
        ·
          refine ⟨13071044982467077210259507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34856119953245539227358685 13071044982467077210259507)
          ·
            refine ⟨19606567473700615815389261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13071044982467077210259507 19606567473700615815389261)
            ·
              refine ⟨7352462802637730930770973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19606567473700615815389261 7352462802637730930770973)
              ·
                refine ⟨2757173550989149099039115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7352462802637730930770973 2757173550989149099039115)
                ·
                  refine ⟨4135760326483723648558673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2757173550989149099039115 4135760326483723648558673)
                  ·
                    refine ⟨3101820244862792736419005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4135760326483723648558673 3101820244862792736419005)
                    ·
                      refine ⟨1163182591823547276157127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3101820244862792736419005 1163182591823547276157127)
                      ·
                        rfl

theorem cell23_2265290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 3, 3, 1, 2, 3].length) (baseStart_2265290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265290 prefixEnd_2265290 := by exact prefixLift 2265290
  have htrace : WordTrace (prefixWord ++ tailWord_2265290) baseStart_2265290 baseEnd_2265290 := by
    simpa [prefixWord, tailWord_2265290, baseEnd_2265290] using wordTrace_append hprefix tailTrace_2265290
  have hstable : (prefixWord ++ tailWord_2265290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265290).length < 2 ^ (prefixWord ++ tailWord_2265290).sum := by decide
  have hdescent : baseEnd_2265290 < baseStart_2265290 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265304 : List Nat := [2, 1, 2, 2, 4, 1, 2, 4, 1, 2, 2]
def baseStart_2265304 : Nat := 118140960795 + 2265304 * 2 ^ 59
def prefixEnd_2265304 : Nat := 4983230072969 + 3 ^ 40 * 2265304 * 2
def baseEnd_2265304 : Nat := 1163189780552710221382063

theorem tailTrace_2265304 : CollatzResearch.WordTrace tailWord_2265304 prefixEnd_2265304 1163189780552710221382063 := by
  unfold tailWord_2265304
  simp only [CollatzResearch.WordTrace]
  refine ⟨41311212292598982983485483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55081616390131977311313977 41311212292598982983485483)
  ·
    refine ⟨61966818438898474475228225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41311212292598982983485483 61966818438898474475228225)
    ·
      refine ⟨46475113829173855856421169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61966818438898474475228225 46475113829173855856421169)
      ·
        refine ⟨34856335371880391892315877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46475113829173855856421169 34856335371880391892315877)
        ·
          refine ⟨6535562882227573479809227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34856335371880391892315877 6535562882227573479809227)
          ·
            refine ⟨9803344323341360219713841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6535562882227573479809227 9803344323341360219713841)
            ·
              refine ⟨7352508242506020164785381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9803344323341360219713841 7352508242506020164785381)
              ·
                refine ⟨1378595295469878780897259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7352508242506020164785381 1378595295469878780897259)
                ·
                  refine ⟨2067892943204818171345889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1378595295469878780897259 2067892943204818171345889)
                  ·
                    refine ⟨1550919707403613628509417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2067892943204818171345889 1550919707403613628509417)
                    ·
                      refine ⟨1163189780552710221382063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1550919707403613628509417 1163189780552710221382063)
                      ·
                        rfl

theorem cell23_2265304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 2, 4, 1, 2, 2].length) (baseStart_2265304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265304 prefixEnd_2265304 := by exact prefixLift 2265304
  have htrace : WordTrace (prefixWord ++ tailWord_2265304) baseStart_2265304 baseEnd_2265304 := by
    simpa [prefixWord, tailWord_2265304, baseEnd_2265304] using wordTrace_append hprefix tailTrace_2265304
  have hstable : (prefixWord ++ tailWord_2265304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265304).length < 2 ^ (prefixWord ++ tailWord_2265304).sum := by decide
  have hdescent : baseEnd_2265304 < baseStart_2265304 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265306 : List Nat := [3, 1, 1, 2, 2, 1, 2, 1, 1, 9]
def baseStart_2265306 : Nat := 118140960795 + 2265306 * 2 ^ 59
def prefixEnd_2265306 : Nat := 4983230072969 + 3 ^ 40 * 2265306 * 2
def baseEnd_2265306 : Nat := 387730269171339737852351

theorem tailTrace_2265306 : CollatzResearch.WordTrace tailWord_2265306 prefixEnd_2265306 387730269171339737852351 := by
  unfold tailWord_2265306
  simp only [CollatzResearch.WordTrace]
  refine ⟨20655624382797680077135943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55081665020793813539029181 20655624382797680077135943)
  ·
    refine ⟨30983436574196520115703915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20655624382797680077135943 30983436574196520115703915)
    ·
      refine ⟨46475154861294780173555873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30983436574196520115703915 46475154861294780173555873)
      ·
        refine ⟨34856366145971085130166905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46475154861294780173555873 34856366145971085130166905)
        ·
          refine ⟨26142274609478313847625179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34856366145971085130166905 26142274609478313847625179)
          ·
            refine ⟨39213411914217470771437769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26142274609478313847625179 39213411914217470771437769)
            ·
              refine ⟨29410058935663103078578327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39213411914217470771437769 29410058935663103078578327)
              ·
                refine ⟨44115088403494654617867491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29410058935663103078578327 44115088403494654617867491)
                ·
                  refine ⟨66172632605241981926801237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44115088403494654617867491 66172632605241981926801237)
                  ·
                    refine ⟨387730269171339737852351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 66172632605241981926801237 387730269171339737852351)
                    ·
                      rfl

theorem cell23_2265306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 2, 1, 1, 9].length) (baseStart_2265306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265306 prefixEnd_2265306 := by exact prefixLift 2265306
  have htrace : WordTrace (prefixWord ++ tailWord_2265306) baseStart_2265306 baseEnd_2265306 := by
    simpa [prefixWord, tailWord_2265306, baseEnd_2265306] using wordTrace_append hprefix tailTrace_2265306
  have hstable : (prefixWord ++ tailWord_2265306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265306).length < 2 ^ (prefixWord ++ tailWord_2265306).sum := by decide
  have hdescent : baseEnd_2265306 < baseStart_2265306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265320 : List Nat := [2, 1, 4, 1, 2, 2, 3, 1, 1, 3, 3]
def baseStart_2265320 : Nat := 118140960795 + 2265320 * 2 ^ 59
def prefixEnd_2265320 : Nat := 4983230072969 + 3 ^ 40 * 2265320 * 2
def baseEnd_2265320 : Nat := 1163197996243182158781989

theorem tailTrace_2265320 : CollatzResearch.WordTrace tailWord_2265320 prefixEnd_2265320 1163197996243182158781989 := by
  unfold tailWord_2265320
  simp only [CollatzResearch.WordTrace]
  refine ⟨41311504076570000349776707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55082005435426667133035609 41311504076570000349776707)
  ·
    refine ⟨61967256114855000524665061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41311504076570000349776707 61967256114855000524665061)
    ·
      refine ⟨11618860521535312598374699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61967256114855000524665061 11618860521535312598374699)
      ·
        refine ⟨17428290782302968897562049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11618860521535312598374699 17428290782302968897562049)
        ·
          refine ⟨13071218086727226673171537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17428290782302968897562049 13071218086727226673171537)
          ·
            refine ⟨9803413565045420004878653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13071218086727226673171537 9803413565045420004878653)
            ·
              refine ⟨3676280086892032501829495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9803413565045420004878653 3676280086892032501829495)
              ·
                refine ⟨5514420130338048752744243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3676280086892032501829495 5514420130338048752744243)
                ·
                  refine ⟨8271630195507073129116365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5514420130338048752744243 8271630195507073129116365)
                  ·
                    refine ⟨3101861323315152423418637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8271630195507073129116365 3101861323315152423418637)
                    ·
                      refine ⟨1163197996243182158781989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3101861323315152423418637 1163197996243182158781989)
                      ·
                        rfl

theorem cell23_2265320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 1, 1, 3, 3].length) (baseStart_2265320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265320 prefixEnd_2265320 := by exact prefixLift 2265320
  have htrace : WordTrace (prefixWord ++ tailWord_2265320) baseStart_2265320 baseEnd_2265320 := by
    simpa [prefixWord, tailWord_2265320, baseEnd_2265320] using wordTrace_append hprefix tailTrace_2265320
  have hstable : (prefixWord ++ tailWord_2265320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265320).length < 2 ^ (prefixWord ++ tailWord_2265320).sum := by decide
  have hdescent : baseEnd_2265320 < baseStart_2265320 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265336 : List Nat := [2, 1, 2, 1, 1, 2, 1, 4, 1, 8]
def baseStart_2265336 : Nat := 118140960795 + 2265336 * 2 ^ 59
def prefixEnd_2265336 : Nat := 4983230072969 + 3 ^ 40 * 2265336 * 2
def baseEnd_2265336 : Nat := 387735403977884698727305

theorem tailTrace_2265336 : CollatzResearch.WordTrace tailWord_2265336 prefixEnd_2265336 387735403977884698727305 := by
  unfold tailWord_2265336
  simp only [CollatzResearch.WordTrace]
  refine ⟨41311795860541017716067931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55082394480721356954757241 41311795860541017716067931)
  ·
    refine ⟨61967693790811526574101897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41311795860541017716067931 61967693790811526574101897)
    ·
      refine ⟨46475770343108644930576423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61967693790811526574101897 46475770343108644930576423)
      ·
        refine ⟨69713655514662967395864635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46475770343108644930576423 69713655514662967395864635)
        ·
          refine ⟨104570483271994451093796953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69713655514662967395864635 104570483271994451093796953)
          ·
            refine ⟨78427862453995838320347715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104570483271994451093796953 78427862453995838320347715)
            ·
              refine ⟨117641793680993757480521573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78427862453995838320347715 117641793680993757480521573)
              ·
                refine ⟨22057836315186329527597795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117641793680993757480521573 22057836315186329527597795)
                ·
                  refine ⟨33086754472779494291396693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22057836315186329527597795 33086754472779494291396693)
                  ·
                    refine ⟨387735403977884698727305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33086754472779494291396693 387735403977884698727305)
                    ·
                      rfl

theorem cell23_2265336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 1, 4, 1, 8].length) (baseStart_2265336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265336 prefixEnd_2265336 := by exact prefixLift 2265336
  have htrace : WordTrace (prefixWord ++ tailWord_2265336) baseStart_2265336 baseEnd_2265336 := by
    simpa [prefixWord, tailWord_2265336, baseEnd_2265336] using wordTrace_append hprefix tailTrace_2265336
  have hstable : (prefixWord ++ tailWord_2265336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265336).length < 2 ^ (prefixWord ++ tailWord_2265336).sum := by decide
  have hdescent : baseEnd_2265336 < baseStart_2265336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265381 : List Nat := [1, 3, 1, 2, 6, 1, 1, 2, 1, 3, 2]
def baseStart_2265381 : Nat := 118140960795 + 2265381 * 2 ^ 59
def prefixEnd_2265381 : Nat := 4983230072969 + 3 ^ 40 * 2265381 * 2
def baseEnd_2265381 : Nat := 1163229318563106420119209

theorem tailTrace_2265381 : CollatzResearch.WordTrace tailWord_2265381 prefixEnd_2265381 1163229318563106420119209 := by
  unfold tailWord_2265381
  simp only [CollatzResearch.WordTrace]
  refine ⟨82625233005919008117523997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55083488670612672078349331 82625233005919008117523997)
  ·
    refine ⟨30984462377219628044071499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82625233005919008117523997 30984462377219628044071499)
    ·
      refine ⟨46476693565829442066107249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30984462377219628044071499 46476693565829442066107249)
      ·
        refine ⟨34857520174372081549580437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46476693565829442066107249 34857520174372081549580437)
        ·
          refine ⟨1633946258173691322636583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34857520174372081549580437 1633946258173691322636583)
          ·
            refine ⟨2450919387260536983954875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1633946258173691322636583 2450919387260536983954875)
            ·
              refine ⟨3676379080890805475932313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2450919387260536983954875 3676379080890805475932313)
              ·
                refine ⟨2757284310668104106949235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3676379080890805475932313 2757284310668104106949235)
                ·
                  refine ⟨4135926466002156160423853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2757284310668104106949235 4135926466002156160423853)
                  ·
                    refine ⟨1550972424750808560158945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4135926466002156160423853 1550972424750808560158945)
                    ·
                      refine ⟨1163229318563106420119209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1550972424750808560158945 1163229318563106420119209)
                      ·
                        rfl

theorem cell23_2265381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 6, 1, 1, 2, 1, 3, 2].length) (baseStart_2265381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265381 prefixEnd_2265381 := by exact prefixLift 2265381
  have htrace : WordTrace (prefixWord ++ tailWord_2265381) baseStart_2265381 baseEnd_2265381 := by
    simpa [prefixWord, tailWord_2265381, baseEnd_2265381] using wordTrace_append hprefix tailTrace_2265381
  have hstable : (prefixWord ++ tailWord_2265381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265381).length < 2 ^ (prefixWord ++ tailWord_2265381).sum := by decide
  have hdescent : baseEnd_2265381 < baseStart_2265381 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265420 : List Nat := [2, 2, 1, 3, 2, 1, 1, 1, 1, 7, 2]
def baseStart_2265420 : Nat := 118140960795 + 2265420 * 2 ^ 59
def prefixEnd_2265420 : Nat := 4983230072969 + 3 ^ 40 * 2265420 * 2
def baseEnd_2265420 : Nat := 1163249344308631767531529

theorem tailTrace_2265420 : CollatzResearch.WordTrace tailWord_2265420 prefixEnd_2265420 1163249344308631767531529 := by
  unfold tailWord_2265420
  simp only [CollatzResearch.WordTrace]
  refine ⟨41313327726388858889096857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55084436968518478518795809 41313327726388858889096857)
  ·
    refine ⟨30984995794791644166822643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41313327726388858889096857 30984995794791644166822643)
    ·
      refine ⟨46477493692187466250233965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30984995794791644166822643 46477493692187466250233965)
      ·
        refine ⟨17429060134570299843837737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46477493692187466250233965 17429060134570299843837737)
        ·
          refine ⟨13071795100927724882878303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17429060134570299843837737 13071795100927724882878303)
          ·
            refine ⟨19607692651391587324317455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13071795100927724882878303 19607692651391587324317455)
            ·
              refine ⟨29411538977087380986476183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19607692651391587324317455 29411538977087380986476183)
              ·
                refine ⟨44117308465631071479714275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29411538977087380986476183 44117308465631071479714275)
                ·
                  refine ⟨66175962698446607219571413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44117308465631071479714275 66175962698446607219571413)
                  ·
                    refine ⟨1550999125744842356708705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 66175962698446607219571413 1550999125744842356708705)
                    ·
                      refine ⟨1163249344308631767531529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1550999125744842356708705 1163249344308631767531529)
                      ·
                        rfl

theorem cell23_2265420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 1, 1, 1, 1, 7, 2].length) (baseStart_2265420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265420 prefixEnd_2265420 := by exact prefixLift 2265420
  have htrace : WordTrace (prefixWord ++ tailWord_2265420) baseStart_2265420 baseEnd_2265420 := by
    simpa [prefixWord, tailWord_2265420, baseEnd_2265420] using wordTrace_append hprefix tailTrace_2265420
  have hstable : (prefixWord ++ tailWord_2265420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265420).length < 2 ^ (prefixWord ++ tailWord_2265420).sum := by decide
  have hdescent : baseEnd_2265420 < baseStart_2265420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265433 : List Nat := [1, 2, 1, 2, 2, 2, 1, 4, 1, 3, 4]
def baseStart_2265433 : Nat := 118140960795 + 2265433 * 2 ^ 59
def prefixEnd_2265433 : Nat := 4983230072969 + 3 ^ 40 * 2265433 * 2
def baseEnd_2265433 : Nat := 1163256019557140216668969

theorem tailTrace_2265433 : CollatzResearch.WordTrace tailWord_2265433 prefixEnd_2265433 1163256019557140216668969 := by
  unfold tailWord_2265433
  simp only [CollatzResearch.WordTrace]
  refine ⟨82627129601730620998416953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55084753067820413998944635 82627129601730620998416953)
  ·
    refine ⟨61970347201297965748812715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82627129601730620998416953 61970347201297965748812715)
    ·
      refine ⟨92955520801946948623219073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61970347201297965748812715 92955520801946948623219073)
      ·
        refine ⟨69716640601460211467414305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92955520801946948623219073 69716640601460211467414305)
        ·
          refine ⟨52287480451095158600560729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69716640601460211467414305 52287480451095158600560729)
          ·
            refine ⟨39215610338321368950420547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52287480451095158600560729 39215610338321368950420547)
            ·
              refine ⟨58823415507482053425630821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39215610338321368950420547 58823415507482053425630821)
              ·
                refine ⟨11029390407652885017305779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58823415507482053425630821 11029390407652885017305779)
                ·
                  refine ⟨16544085611479327525958669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11029390407652885017305779 16544085611479327525958669)
                  ·
                    refine ⟨6204032104304747822234501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16544085611479327525958669 6204032104304747822234501)
                    ·
                      refine ⟨1163256019557140216668969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6204032104304747822234501 1163256019557140216668969)
                      ·
                        rfl

theorem cell23_2265433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_2265433 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265433 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265433 prefixEnd_2265433 := by exact prefixLift 2265433
  have htrace : WordTrace (prefixWord ++ tailWord_2265433) baseStart_2265433 baseEnd_2265433 := by
    simpa [prefixWord, tailWord_2265433, baseEnd_2265433] using wordTrace_append hprefix tailTrace_2265433
  have hstable : (prefixWord ++ tailWord_2265433).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265433).length < 2 ^ (prefixWord ++ tailWord_2265433).sum := by decide
  have hdescent : baseEnd_2265433 < baseStart_2265433 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265447 : List Nat := [1, 1, 5, 1, 3, 3, 1, 1, 2, 5]
def baseStart_2265447 : Nat := 118140960795 + 2265447 * 2 ^ 59
def prefixEnd_2265447 : Nat := 4983230072969 + 3 ^ 40 * 2265447 * 2
def baseEnd_2265447 : Nat := 387754402762101053964635

theorem tailTrace_2265447 : CollatzResearch.WordTrace tailWord_2265447 prefixEnd_2265447 387754402762101053964635 := by
  unfold tailWord_2265447
  simp only [CollatzResearch.WordTrace]
  refine ⟨82627640223679901389426595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55085093482453267592951063 82627640223679901389426595)
  ·
    refine ⟨123941460335519852084139893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82627640223679901389426595 123941460335519852084139893)
    ·
      refine ⟨11619511906454986132888115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 123941460335519852084139893 11619511906454986132888115)
      ·
        refine ⟨17429267859682479199332173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11619511906454986132888115 17429267859682479199332173)
        ·
          refine ⟨6535975447380929699749565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17429267859682479199332173 6535975447380929699749565)
          ·
            refine ⟨2450990792767848637406087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6535975447380929699749565 2450990792767848637406087)
            ·
              refine ⟨3676486189151772956109131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2450990792767848637406087 3676486189151772956109131)
              ·
                refine ⟨5514729283727659434163697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3676486189151772956109131 5514729283727659434163697)
                ·
                  refine ⟨4136046962795744575622773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5514729283727659434163697 4136046962795744575622773)
                  ·
                    refine ⟨387754402762101053964635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4136046962795744575622773 387754402762101053964635)
                    ·
                      rfl

theorem cell23_2265447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 3, 1, 1, 2, 5].length) (baseStart_2265447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265447 prefixEnd_2265447 := by exact prefixLift 2265447
  have htrace : WordTrace (prefixWord ++ tailWord_2265447) baseStart_2265447 baseEnd_2265447 := by
    simpa [prefixWord, tailWord_2265447, baseEnd_2265447] using wordTrace_append hprefix tailTrace_2265447
  have hstable : (prefixWord ++ tailWord_2265447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265447).length < 2 ^ (prefixWord ++ tailWord_2265447).sum := by decide
  have hdescent : baseEnd_2265447 < baseStart_2265447 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265493 : List Nat := [1, 3, 2, 1, 1, 2, 1, 1, 3, 2, 6]
def baseStart_2265493 : Nat := 118140960795 + 2265493 * 2 ^ 59
def prefixEnd_2265493 : Nat := 4983230072969 + 3 ^ 40 * 2265493 * 2
def baseEnd_2265493 : Nat := 1163286828396409981918693

theorem tailTrace_2265493 : CollatzResearch.WordTrace tailWord_2265493 prefixEnd_2265493 1163286828396409981918693 := by
  unfold tailWord_2265493
  simp only [CollatzResearch.WordTrace]
  refine ⟨82629317981513251245601133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55086211987675500830400755 82629317981513251245601133)
  ·
    refine ⟨30985994243067469217100425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82629317981513251245601133 30985994243067469217100425)
    ·
      refine ⟨23239495682300601912825319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30985994243067469217100425 23239495682300601912825319)
      ·
        refine ⟨34859243523450902869237979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23239495682300601912825319 34859243523450902869237979)
        ·
          refine ⟨52288865285176354303856969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34859243523450902869237979 52288865285176354303856969)
          ·
            refine ⟨39216648963882265727892727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52288865285176354303856969 39216648963882265727892727)
            ·
              refine ⟨58824973445823398591839091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39216648963882265727892727 58824973445823398591839091)
              ·
                refine ⟨88237460168735097887758637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58824973445823398591839091 88237460168735097887758637)
                ·
                  refine ⟨33089047563275661707909489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88237460168735097887758637 33089047563275661707909489)
                  ·
                    refine ⟨24816785672456746280932117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33089047563275661707909489 24816785672456746280932117)
                    ·
                      refine ⟨1163286828396409981918693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24816785672456746280932117 1163286828396409981918693)
                      ·
                        rfl

theorem cell23_2265493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 1, 3, 2, 6].length) (baseStart_2265493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265493 prefixEnd_2265493 := by exact prefixLift 2265493
  have htrace : WordTrace (prefixWord ++ tailWord_2265493) baseStart_2265493 baseEnd_2265493 := by
    simpa [prefixWord, tailWord_2265493, baseEnd_2265493] using wordTrace_append hprefix tailTrace_2265493
  have hstable : (prefixWord ++ tailWord_2265493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265493).length < 2 ^ (prefixWord ++ tailWord_2265493).sum := by decide
  have hdescent : baseEnd_2265493 < baseStart_2265493 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265511 : List Nat := [1, 1, 6, 1, 1, 4, 1, 3, 1, 4]
def baseStart_2265511 : Nat := 118140960795 + 2265511 * 2 ^ 59
def prefixEnd_2265511 : Nat := 4983230072969 + 3 ^ 40 * 2265511 * 2
def baseEnd_2265511 : Nat := 387765357016063637164537

theorem tailTrace_2265511 : CollatzResearch.WordTrace tailWord_2265511 prefixEnd_2265511 387765357016063637164537 := by
  unfold tailWord_2265511
  simp only [CollatzResearch.WordTrace]
  refine ⟨82629974495448040319756387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55086649663632026879837591 82629974495448040319756387)
  ·
    refine ⟨123944961743172060479634581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82629974495448040319756387 123944961743172060479634581)
    ·
      refine ⟨5809920081711190334982871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 123944961743172060479634581 5809920081711190334982871)
      ·
        refine ⟨8714880122566785502474307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5809920081711190334982871 8714880122566785502474307)
        ·
          refine ⟨13072320183850178253711461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8714880122566785502474307 13072320183850178253711461)
          ·
            refine ⟨2451060034471908422570899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13072320183850178253711461 2451060034471908422570899)
            ·
              refine ⟨3676590051707862633856349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2451060034471908422570899 3676590051707862633856349)
              ·
                refine ⟨1378721269390448487696131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3676590051707862633856349 1378721269390448487696131)
                ·
                  refine ⟨2068081904085672731544197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1378721269390448487696131 2068081904085672731544197)
                  ·
                    refine ⟨387765357016063637164537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2068081904085672731544197 387765357016063637164537)
                    ·
                      rfl

theorem cell23_2265511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 3, 1, 4].length) (baseStart_2265511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265511 prefixEnd_2265511 := by exact prefixLift 2265511
  have htrace : WordTrace (prefixWord ++ tailWord_2265511) baseStart_2265511 baseEnd_2265511 := by
    simpa [prefixWord, tailWord_2265511, baseEnd_2265511] using wordTrace_append hprefix tailTrace_2265511
  have hstable : (prefixWord ++ tailWord_2265511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265511).length < 2 ^ (prefixWord ++ tailWord_2265511).sum := by decide
  have hdescent : baseEnd_2265511 < baseStart_2265511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265527 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 4, 3, 2]
def baseStart_2265527 : Nat := 118140960795 + 2265527 * 2 ^ 59
def prefixEnd_2265527 : Nat := 4983230072969 + 3 ^ 40 * 2265527 * 2
def baseEnd_2265527 : Nat := 1163304286738662848893537

theorem tailTrace_2265527 : CollatzResearch.WordTrace tailWord_2265527 prefixEnd_2265527 1163304286738662848893537 := by
  unfold tailWord_2265527
  simp only [CollatzResearch.WordTrace]
  refine ⟨82630558063390075052338835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55087038708926716701559223 82630558063390075052338835)
  ·
    refine ⟨123945837095085112578508253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82630558063390075052338835 123945837095085112578508253)
    ·
      refine ⟨46479688910656917216940595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123945837095085112578508253 46479688910656917216940595)
      ·
        refine ⟨69719533365985375825410893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46479688910656917216940595 69719533365985375825410893)
        ·
          refine ⟨26144825012244515934529085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69719533365985375825410893 26144825012244515934529085)
          ·
            refine ⟨9804309379591693475448407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26144825012244515934529085 9804309379591693475448407)
            ·
              refine ⟨14706464069387540213172611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9804309379591693475448407 14706464069387540213172611)
              ·
                refine ⟨22059696104081310319758917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14706464069387540213172611 22059696104081310319758917)
                ·
                  refine ⟨4136193019515245684954797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22059696104081310319758917 4136193019515245684954797)
                  ·
                    refine ⟨1551072382318217131858049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4136193019515245684954797 1551072382318217131858049)
                    ·
                      refine ⟨1163304286738662848893537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1551072382318217131858049 1163304286738662848893537)
                      ·
                        rfl

theorem cell23_2265527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 4, 3, 2].length) (baseStart_2265527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265527 prefixEnd_2265527 := by exact prefixLift 2265527
  have htrace : WordTrace (prefixWord ++ tailWord_2265527) baseStart_2265527 baseEnd_2265527 := by
    simpa [prefixWord, tailWord_2265527, baseEnd_2265527] using wordTrace_append hprefix tailTrace_2265527
  have hstable : (prefixWord ++ tailWord_2265527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265527).length < 2 ^ (prefixWord ++ tailWord_2265527).sum := by decide
  have hdescent : baseEnd_2265527 < baseStart_2265527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265534 : List Nat := [4, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3]
def baseStart_2265534 : Nat := 118140960795 + 2265534 * 2 ^ 59
def prefixEnd_2265534 : Nat := 4983230072969 + 3 ^ 40 * 2265534 * 2
def baseEnd_2265534 : Nat := 1163307881103244321506005

theorem tailTrace_2265534 : CollatzResearch.WordTrace tailWord_2265534 prefixEnd_2265534 1163307881103244321506005 := by
  unfold tailWord_2265534
  simp only [CollatzResearch.WordTrace]
  refine ⟨10328851671795589405980457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55087208916243143498562437 10328851671795589405980457)
  ·
    refine ⟨7746638753846692054485343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10328851671795589405980457 7746638753846692054485343)
    ·
      refine ⟨11619958130770038081728015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7746638753846692054485343 11619958130770038081728015)
      ·
        refine ⟨17429937196155057122592023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11619958130770038081728015 17429937196155057122592023)
        ·
          refine ⟨26144905794232585683888035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17429937196155057122592023 26144905794232585683888035)
          ·
            refine ⟨39217358691348878525832053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26144905794232585683888035 39217358691348878525832053)
            ·
              refine ⟨3676627377313957361796755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39217358691348878525832053 3676627377313957361796755)
              ·
                refine ⟨5514941065970936042695133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3676627377313957361796755 5514941065970936042695133)
                ·
                  refine ⟨2068102899739101016010675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5514941065970936042695133 2068102899739101016010675)
                  ·
                    refine ⟨3102154349608651524016013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2068102899739101016010675 3102154349608651524016013)
                    ·
                      refine ⟨1163307881103244321506005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3102154349608651524016013 1163307881103244321506005)
                      ·
                        rfl

theorem cell23_2265534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 3, 1, 3].length) (baseStart_2265534 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265534 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265534 prefixEnd_2265534 := by exact prefixLift 2265534
  have htrace : WordTrace (prefixWord ++ tailWord_2265534) baseStart_2265534 baseEnd_2265534 := by
    simpa [prefixWord, tailWord_2265534, baseEnd_2265534] using wordTrace_append hprefix tailTrace_2265534
  have hstable : (prefixWord ++ tailWord_2265534).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265534).length < 2 ^ (prefixWord ++ tailWord_2265534).sum := by decide
  have hdescent : baseEnd_2265534 < baseStart_2265534 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265550 : List Nat := [4, 1, 1, 1, 2, 1, 1, 5, 1, 6]
def baseStart_2265550 : Nat := 118140960795 + 2265550 * 2 ^ 59
def prefixEnd_2265550 : Nat := 4983230072969 + 3 ^ 40 * 2265550 * 2
def baseEnd_2265550 : Nat := 387772032264572086301977

theorem tailTrace_2265550 : CollatzResearch.WordTrace tailWord_2265550 prefixEnd_2265550 387772032264572086301977 := by
  unfold tailWord_2265550
  simp only [CollatzResearch.WordTrace]
  refine ⟨10328924617788343747553263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55087597961537833320284069 10328924617788343747553263)
  ·
    refine ⟨15493386926682515621329895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10328924617788343747553263 15493386926682515621329895)
    ·
      refine ⟨23240080390023773431994843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15493386926682515621329895 23240080390023773431994843)
      ·
        refine ⟨34860120585035660147992265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23240080390023773431994843 34860120585035660147992265)
        ·
          refine ⟨26145090438776745110994199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34860120585035660147992265 26145090438776745110994199)
          ·
            refine ⟨39217635658165117666491299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26145090438776745110994199 39217635658165117666491299)
            ·
              refine ⟨58826453487247676499736949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39217635658165117666491299 58826453487247676499736949)
              ·
                refine ⟨5514980014429469671850339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58826453487247676499736949 5514980014429469671850339)
                ·
                  refine ⟨8272470021644204507775509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5514980014429469671850339 8272470021644204507775509)
                  ·
                    refine ⟨387772032264572086301977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8272470021644204507775509 387772032264572086301977)
                    ·
                      rfl

theorem cell23_2265550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 1, 5, 1, 6].length) (baseStart_2265550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265550 prefixEnd_2265550 := by exact prefixLift 2265550
  have htrace : WordTrace (prefixWord ++ tailWord_2265550) baseStart_2265550 baseEnd_2265550 := by
    simpa [prefixWord, tailWord_2265550, baseEnd_2265550] using wordTrace_append hprefix tailTrace_2265550
  have hstable : (prefixWord ++ tailWord_2265550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265550).length < 2 ^ (prefixWord ++ tailWord_2265550).sum := by decide
  have hdescent : baseEnd_2265550 < baseStart_2265550 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265554 : List Nat := [3, 2, 2, 4, 1, 1, 1, 1, 3, 5]
def baseStart_2265554 : Nat := 118140960795 + 2265554 * 2 ^ 59
def prefixEnd_2265554 : Nat := 4983230072969 + 3 ^ 40 * 2265554 * 2
def baseEnd_2265554 : Nat := 387772716905444747751971

theorem tailTrace_2265554 : CollatzResearch.WordTrace tailWord_2265554 prefixEnd_2265554 387772716905444747751971 := by
  unfold tailWord_2265554
  simp only [CollatzResearch.WordTrace]
  refine ⟨20657885708573064665892929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55087695222861505775714477 20657885708573064665892929)
  ·
    refine ⟨15493414281429798499419697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20657885708573064665892929 15493414281429798499419697)
    ·
      refine ⟨11620060711072348874564773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15493414281429798499419697 11620060711072348874564773)
      ·
        refine ⟨2178761383326065413980895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11620060711072348874564773 2178761383326065413980895)
        ·
          refine ⟨3268142074989098120971343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2178761383326065413980895 3268142074989098120971343)
          ·
            refine ⟨4902213112483647181457015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3268142074989098120971343 4902213112483647181457015)
            ·
              refine ⟨7353319668725470772185523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4902213112483647181457015 7353319668725470772185523)
              ·
                refine ⟨11029979503088206158278285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7353319668725470772185523 11029979503088206158278285)
                ·
                  refine ⟨4136242313658077309354357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11029979503088206158278285 4136242313658077309354357)
                  ·
                    refine ⟨387772716905444747751971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4136242313658077309354357 387772716905444747751971)
                    ·
                      rfl

theorem cell23_2265554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_2265554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265554 prefixEnd_2265554 := by exact prefixLift 2265554
  have htrace : WordTrace (prefixWord ++ tailWord_2265554) baseStart_2265554 baseEnd_2265554 := by
    simpa [prefixWord, tailWord_2265554, baseEnd_2265554] using wordTrace_append hprefix tailTrace_2265554
  have hstable : (prefixWord ++ tailWord_2265554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265554).length < 2 ^ (prefixWord ++ tailWord_2265554).sum := by decide
  have hdescent : baseEnd_2265554 < baseStart_2265554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265557 : List Nat := [1, 3, 2, 3, 1, 3, 1, 1, 3, 1, 4]
def baseStart_2265557 : Nat := 118140960795 + 2265557 * 2 ^ 59
def prefixEnd_2265557 : Nat := 4983230072969 + 3 ^ 40 * 2265557 * 2
def baseEnd_2265557 : Nat := 1163319691158297731518399

theorem tailTrace_2265557 : CollatzResearch.WordTrace tailWord_2265557 prefixEnd_2265557 1163319691158297731518399 := by
  unfold tailWord_2265557
  simp only [CollatzResearch.WordTrace]
  refine ⟨82631652253281390175930925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55087768168854260117287283 82631652253281390175930925)
  ·
    refine ⟨30986869594980521315974097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82631652253281390175930925 30986869594980521315974097)
    ·
      refine ⟨23240152196235390986980573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30986869594980521315974097 23240152196235390986980573)
      ·
        refine ⟨8715057073588271620117715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23240152196235390986980573 8715057073588271620117715)
        ·
          refine ⟨13072585610382407430176573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8715057073588271620117715 13072585610382407430176573)
          ·
            refine ⟨4902219603893402786316215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13072585610382407430176573 4902219603893402786316215)
            ·
              refine ⟨7353329405840104179474323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4902219603893402786316215 7353329405840104179474323)
              ·
                refine ⟨11029994108760156269211485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7353329405840104179474323 11029994108760156269211485)
                ·
                  refine ⟨4136247790785058600954307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11029994108760156269211485 4136247790785058600954307)
                  ·
                    refine ⟨6204371686177587901431461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4136247790785058600954307 6204371686177587901431461)
                    ·
                      refine ⟨1163319691158297731518399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6204371686177587901431461 1163319691158297731518399)
                      ·
                        rfl

theorem cell23_2265557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_2265557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265557 prefixEnd_2265557 := by exact prefixLift 2265557
  have htrace : WordTrace (prefixWord ++ tailWord_2265557) baseStart_2265557 baseEnd_2265557 := by
    simpa [prefixWord, tailWord_2265557, baseEnd_2265557] using wordTrace_append hprefix tailTrace_2265557
  have hstable : (prefixWord ++ tailWord_2265557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265557).length < 2 ^ (prefixWord ++ tailWord_2265557).sum := by decide
  have hdescent : baseEnd_2265557 < baseStart_2265557 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265604 : List Nat := [2, 3, 2, 3, 1, 2, 2, 1, 1, 2, 4]
def baseStart_2265604 : Nat := 118140960795 + 2265604 * 2 ^ 59
def prefixEnd_2265604 : Nat := 4983230072969 + 3 ^ 40 * 2265604 * 2
def baseEnd_2265604 : Nat := 1163343824749059047630683

theorem tailTrace_2265604 : CollatzResearch.WordTrace tailWord_2265604 prefixEnd_2265604 1163343824749059047630683 := by
  unfold tailWord_2265604
  simp only [CollatzResearch.WordTrace]
  refine ⟨41316683242055558601445933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55088910989407411468594577 41316683242055558601445933)
  ·
    refine ⟨15493756215770834475542225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41316683242055558601445933 15493756215770834475542225)
    ·
      refine ⟨11620317161828125856656669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15493756215770834475542225 11620317161828125856656669)
      ·
        refine ⟨4357618935685547196246251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11620317161828125856656669 4357618935685547196246251)
        ·
          refine ⟨6536428403528320794369377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4357618935685547196246251 6536428403528320794369377)
          ·
            refine ⟨4902321302646240595777033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6536428403528320794369377 4902321302646240595777033)
            ·
              refine ⟨3676740976984680446832775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4902321302646240595777033 3676740976984680446832775)
              ·
                refine ⟨5515111465477020670249163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3676740976984680446832775 5515111465477020670249163)
                ·
                  refine ⟨8272667198215531005373745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5515111465477020670249163 8272667198215531005373745)
                  ·
                    refine ⟨6204500398661648254030309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8272667198215531005373745 6204500398661648254030309)
                    ·
                      refine ⟨1163343824749059047630683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6204500398661648254030309 1163343824749059047630683)
                      ·
                        rfl

theorem cell23_2265604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 1, 1, 2, 4].length) (baseStart_2265604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265604 prefixEnd_2265604 := by exact prefixLift 2265604
  have htrace : WordTrace (prefixWord ++ tailWord_2265604) baseStart_2265604 baseEnd_2265604 := by
    simpa [prefixWord, tailWord_2265604, baseEnd_2265604] using wordTrace_append hprefix tailTrace_2265604
  have hstable : (prefixWord ++ tailWord_2265604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265604).length < 2 ^ (prefixWord ++ tailWord_2265604).sum := by decide
  have hdescent : baseEnd_2265604 < baseStart_2265604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265610 : List Nat := [3, 1, 2, 2, 2, 1, 1, 2, 2, 7]
def baseStart_2265610 : Nat := 118140960795 + 2265610 * 2 ^ 59
def prefixEnd_2265610 : Nat := 4983230072969 + 3 ^ 40 * 2265610 * 2
def baseEnd_2265610 : Nat := 387782301877662008051885

theorem tailTrace_2265610 : CollatzResearch.WordTrace tailWord_2265610 prefixEnd_2265610 387782301877662008051885 := by
  unfold tailWord_2265610
  simp only [CollatzResearch.WordTrace]
  refine ⟨20658396330522345056902571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55089056881392920151740189 20658396330522345056902571)
  ·
    refine ⟨30987594495783517585353857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20658396330522345056902571 30987594495783517585353857)
    ·
      refine ⟨23240695871837638189015393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30987594495783517585353857 23240695871837638189015393)
      ·
        refine ⟨17430521903878228641761545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23240695871837638189015393 17430521903878228641761545)
        ·
          refine ⟨13072891427908671481321159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17430521903878228641761545 13072891427908671481321159)
          ·
            refine ⟨19609337141863007221981739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13072891427908671481321159 19609337141863007221981739)
            ·
              refine ⟨29414005712794510832972609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19609337141863007221981739 29414005712794510832972609)
              ·
                refine ⟨22060504284595883124729457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29414005712794510832972609 22060504284595883124729457)
                ·
                  refine ⟨16545378213446912343547093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22060504284595883124729457 16545378213446912343547093)
                  ·
                    refine ⟨387782301877662008051885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16545378213446912343547093 387782301877662008051885)
                    ·
                      rfl

theorem cell23_2265610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 2, 7].length) (baseStart_2265610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265610 prefixEnd_2265610 := by exact prefixLift 2265610
  have htrace : WordTrace (prefixWord ++ tailWord_2265610) baseStart_2265610 baseEnd_2265610 := by
    simpa [prefixWord, tailWord_2265610, baseEnd_2265610] using wordTrace_append hprefix tailTrace_2265610
  have hstable : (prefixWord ++ tailWord_2265610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265610).length < 2 ^ (prefixWord ++ tailWord_2265610).sum := by decide
  have hdescent : baseEnd_2265610 < baseStart_2265610 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265664 : List Nat := [2, 1, 1, 2, 2, 2, 5, 1, 1, 4, 2]
def baseStart_2265664 : Nat := 118140960795 + 2265664 * 2 ^ 59
def prefixEnd_2265664 : Nat := 4983230072969 + 3 ^ 40 * 2265664 * 2
def baseEnd_2265664 : Nat := 1163374633588328812880407

theorem tailTrace_2265664 : CollatzResearch.WordTrace tailWord_2265664 prefixEnd_2265664 1163374633588328812880407 := by
  unfold tailWord_2265664
  simp only [CollatzResearch.WordTrace]
  refine ⟨41317777431946873725038023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55090369909262498300050697 41317777431946873725038023)
  ·
    refine ⟨61976666147920310587557035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41317777431946873725038023 61976666147920310587557035)
    ·
      refine ⟨92964999221880465881335553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61976666147920310587557035 92964999221880465881335553)
      ·
        refine ⟨69723749416410349411001665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92964999221880465881335553 69723749416410349411001665)
        ·
          refine ⟨52292812062307762058251249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69723749416410349411001665 52292812062307762058251249)
          ·
            refine ⟨39219609046730821543688437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52292812062307762058251249 39219609046730821543688437)
            ·
              refine ⟨3676838348131014519720791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39219609046730821543688437 3676838348131014519720791)
              ·
                refine ⟨5515257522196521779581187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3676838348131014519720791 5515257522196521779581187)
                ·
                  refine ⟨8272886283294782669371781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5515257522196521779581187 8272886283294782669371781)
                  ·
                    refine ⟨1551166178117771750507209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8272886283294782669371781 1551166178117771750507209)
                    ·
                      refine ⟨1163374633588328812880407, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1551166178117771750507209 1163374633588328812880407)
                      ·
                        rfl

theorem cell23_2265664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 5, 1, 1, 4, 2].length) (baseStart_2265664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265664 prefixEnd_2265664 := by exact prefixLift 2265664
  have htrace : WordTrace (prefixWord ++ tailWord_2265664) baseStart_2265664 baseEnd_2265664 := by
    simpa [prefixWord, tailWord_2265664, baseEnd_2265664] using wordTrace_append hprefix tailTrace_2265664
  have hstable : (prefixWord ++ tailWord_2265664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265664).length < 2 ^ (prefixWord ++ tailWord_2265664).sum := by decide
  have hdescent : baseEnd_2265664 < baseStart_2265664 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265690 : List Nat := [3, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6]
def baseStart_2265690 : Nat := 118140960795 + 2265690 * 2 ^ 59
def prefixEnd_2265690 : Nat := 4983230072969 + 3 ^ 40 * 2265690 * 2
def baseEnd_2265690 : Nat := 1163387984085345711155287

theorem tailTrace_2265690 : CollatzResearch.WordTrace tailWord_2265690 prefixEnd_2265690 1163387984085345711155287 := by
  unfold tailWord_2265690
  simp only [CollatzResearch.WordTrace]
  refine ⟨20659125790449888472630631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55091002107866369260348349 20659125790449888472630631)
  ·
    refine ⟨30988688685674832708945947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20659125790449888472630631 30988688685674832708945947)
    ·
      refine ⟨46483033028512249063418921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30988688685674832708945947 46483033028512249063418921)
      ·
        refine ⟨34862274771384186797564191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46483033028512249063418921 34862274771384186797564191)
        ·
          refine ⟨52293412157076280196346287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34862274771384186797564191 52293412157076280196346287)
          ·
            refine ⟨78440118235614420294519431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52293412157076280196346287 78440118235614420294519431)
            ·
              refine ⟨117660177353421630441779147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78440118235614420294519431 117660177353421630441779147)
              ·
                refine ⟨176490266030132445662668721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117660177353421630441779147 176490266030132445662668721)
                ·
                  refine ⟨132367699522599334247001541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 176490266030132445662668721 132367699522599334247001541)
                  ·
                    refine ⟨24818943660487375171312789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 132367699522599334247001541 24818943660487375171312789)
                    ·
                      refine ⟨1163387984085345711155287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24818943660487375171312789 1163387984085345711155287)
                      ·
                        rfl

theorem cell23_2265690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 1, 2, 4, 6].length) (baseStart_2265690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265690 prefixEnd_2265690 := by exact prefixLift 2265690
  have htrace : WordTrace (prefixWord ++ tailWord_2265690) baseStart_2265690 baseEnd_2265690 := by
    simpa [prefixWord, tailWord_2265690, baseEnd_2265690] using wordTrace_append hprefix tailTrace_2265690
  have hstable : (prefixWord ++ tailWord_2265690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265690).length < 2 ^ (prefixWord ++ tailWord_2265690).sum := by decide
  have hdescent : baseEnd_2265690 < baseStart_2265690 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265747 : List Nat := [1, 1, 1, 2, 1, 2, 2, 4, 5, 4]
def baseStart_2265747 : Nat := 118140960795 + 2265747 * 2 ^ 59
def prefixEnd_2265747 : Nat := 4983230072969 + 3 ^ 40 * 2265747 * 2
def baseEnd_2265747 : Nat := 387805750827550662714175

theorem tailTrace_2265747 : CollatzResearch.WordTrace tailWord_2265747 prefixEnd_2265747 387805750827550662714175 := by
  unfold tailWord_2265747
  simp only [CollatzResearch.WordTrace]
  refine ⟨82638582122593052625347495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55092388081728701750231663 82638582122593052625347495)
  ·
    refine ⟨123957873183889578938021243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82638582122593052625347495 123957873183889578938021243)
    ·
      refine ⟨185936809775834368407031865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123957873183889578938021243 185936809775834368407031865)
      ·
        refine ⟨139452607331875776305273899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185936809775834368407031865 139452607331875776305273899)
        ·
          refine ⟨209178910997813664457910849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139452607331875776305273899 209178910997813664457910849)
          ·
            refine ⟨156884183248360248343433137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209178910997813664457910849 156884183248360248343433137)
            ·
              refine ⟨117663137436270186257574853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156884183248360248343433137 117663137436270186257574853)
              ·
                refine ⟨22061838269300659923295285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117663137436270186257574853 22061838269300659923295285)
                ·
                  refine ⟨2068297337746936867808933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22061838269300659923295285 2068297337746936867808933)
                  ·
                    refine ⟨387805750827550662714175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2068297337746936867808933 387805750827550662714175)
                    ·
                      rfl

theorem cell23_2265747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 4, 5, 4].length) (baseStart_2265747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265747 prefixEnd_2265747 := by exact prefixLift 2265747
  have htrace : WordTrace (prefixWord ++ tailWord_2265747) baseStart_2265747 baseEnd_2265747 := by
    simpa [prefixWord, tailWord_2265747, baseEnd_2265747] using wordTrace_append hprefix tailTrace_2265747
  have hstable : (prefixWord ++ tailWord_2265747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265747).length < 2 ^ (prefixWord ++ tailWord_2265747).sum := by decide
  have hdescent : baseEnd_2265747 < baseStart_2265747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265764 : List Nat := [2, 3, 1, 2, 2, 1, 2, 3, 3, 4]
def baseStart_2265764 : Nat := 118140960795 + 2265764 * 2 ^ 59
def prefixEnd_2265764 : Nat := 4983230072969 + 3 ^ 40 * 2265764 * 2
def baseEnd_2265764 : Nat := 387808660551259473876649

theorem tailTrace_2265764 : CollatzResearch.WordTrace tailWord_2265764 prefixEnd_2265764 387808660551259473876649 := by
  unfold tailWord_2265764
  simp only [CollatzResearch.WordTrace]
  refine ⟨41319601081765732264358173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55092801442354309685810897 41319601081765732264358173)
  ·
    refine ⟨15494850405662149599134315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41319601081765732264358173 15494850405662149599134315)
    ·
      refine ⟨23242275608493224398701473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15494850405662149599134315 23242275608493224398701473)
      ·
        refine ⟨17431706706369918299026105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23242275608493224398701473 17431706706369918299026105)
        ·
          refine ⟨13073780029777438724269579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17431706706369918299026105 13073780029777438724269579)
          ·
            refine ⟨19610670044666158086404369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13073780029777438724269579 19610670044666158086404369)
            ·
              refine ⟨14708002533499618564803277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19610670044666158086404369 14708002533499618564803277)
              ·
                refine ⟨5515500950062356961801229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14708002533499618564803277 5515500950062356961801229)
                ·
                  refine ⟨2068312856273383860675461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5515500950062356961801229 2068312856273383860675461)
                  ·
                    refine ⟨387808660551259473876649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2068312856273383860675461 387808660551259473876649)
                    ·
                      rfl

theorem cell23_2265764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 3, 3, 4].length) (baseStart_2265764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265764 prefixEnd_2265764 := by exact prefixLift 2265764
  have htrace : WordTrace (prefixWord ++ tailWord_2265764) baseStart_2265764 baseEnd_2265764 := by
    simpa [prefixWord, tailWord_2265764, baseEnd_2265764] using wordTrace_append hprefix tailTrace_2265764
  have hstable : (prefixWord ++ tailWord_2265764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265764).length < 2 ^ (prefixWord ++ tailWord_2265764).sum := by decide
  have hdescent : baseEnd_2265764 < baseStart_2265764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265781 : List Nat := [1, 3, 3, 3, 1, 2, 1, 2, 3, 4]
def baseStart_2265781 : Nat := 118140960795 + 2265781 * 2 ^ 59
def prefixEnd_2265781 : Nat := 4983230072969 + 3 ^ 40 * 2265781 * 2
def baseEnd_2265781 : Nat := 387811570274968285039123

theorem tailTrace_2265781 : CollatzResearch.WordTrace tailWord_2265781 prefixEnd_2265781 387811570274968285039123 := by
  unfold tailWord_2265781
  simp only [CollatzResearch.WordTrace]
  refine ⟨82639822204469876432085197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55093214802979917621390131 82639822204469876432085197)
  ·
    refine ⟨30989933326676203662031949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82639822204469876432085197 30989933326676203662031949)
    ·
      refine ⟨11621224997503576373261981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30989933326676203662031949 11621224997503576373261981)
      ·
        refine ⟨4357959374063841139973243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11621224997503576373261981 4357959374063841139973243)
        ·
          refine ⟨6536939061095761709959865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4357959374063841139973243 6536939061095761709959865)
          ·
            refine ⟨4902704295821821282469899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6536939061095761709959865 4902704295821821282469899)
            ·
              refine ⟨7354056443732731923704849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4902704295821821282469899 7354056443732731923704849)
              ·
                refine ⟨5515542332799548942778637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7354056443732731923704849 5515542332799548942778637)
                ·
                  refine ⟨2068328374799830853541989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5515542332799548942778637 2068328374799830853541989)
                  ·
                    refine ⟨387811570274968285039123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2068328374799830853541989 387811570274968285039123)
                    ·
                      rfl

theorem cell23_2265781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 2, 3, 4].length) (baseStart_2265781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265781 prefixEnd_2265781 := by exact prefixLift 2265781
  have htrace : WordTrace (prefixWord ++ tailWord_2265781) baseStart_2265781 baseEnd_2265781 := by
    simpa [prefixWord, tailWord_2265781, baseEnd_2265781] using wordTrace_append hprefix tailTrace_2265781
  have hstable : (prefixWord ++ tailWord_2265781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265781).length < 2 ^ (prefixWord ++ tailWord_2265781).sum := by decide
  have hdescent : baseEnd_2265781 < baseStart_2265781 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265791 : List Nat := [1, 1, 2, 2, 2, 6, 1, 1, 2, 2, 3]
def baseStart_2265791 : Nat := 118140960795 + 2265791 * 2 ^ 59
def prefixEnd_2265791 : Nat := 4983230072969 + 3 ^ 40 * 2265791 * 2
def baseEnd_2265791 : Nat := 1163439845631449815992323

theorem tailTrace_2265791 : CollatzResearch.WordTrace tailWord_2265791 prefixEnd_2265791 1163439845631449815992323 := by
  unfold tailWord_2265791
  simp only [CollatzResearch.WordTrace]
  refine ⟨82640186934433648139949227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55093457956289098759966151 82640186934433648139949227)
  ·
    refine ⟨123960280401650472209923841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82640186934433648139949227 123960280401650472209923841)
    ·
      refine ⟨92970210301237854157442881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 123960280401650472209923841 92970210301237854157442881)
      ·
        refine ⟨69727657725928390618082161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92970210301237854157442881 69727657725928390618082161)
        ·
          refine ⟨52295743294446292963561621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69727657725928390618082161 52295743294446292963561621)
          ·
            refine ⟨2451362966927169982666951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 52295743294446292963561621 2451362966927169982666951)
            ·
              refine ⟨3677044450390754974000427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2451362966927169982666951 3677044450390754974000427)
              ·
                refine ⟨5515566675586132461000641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3677044450390754974000427 5515566675586132461000641)
                ·
                  refine ⟨4136675006689599345750481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5515566675586132461000641 4136675006689599345750481)
                  ·
                    refine ⟨3102506255017199509312861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4136675006689599345750481 3102506255017199509312861)
                    ·
                      refine ⟨1163439845631449815992323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3102506255017199509312861 1163439845631449815992323)
                      ·
                        rfl

theorem cell23_2265791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 1, 2, 2, 3].length) (baseStart_2265791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265791 prefixEnd_2265791 := by exact prefixLift 2265791
  have htrace : WordTrace (prefixWord ++ tailWord_2265791) baseStart_2265791 baseEnd_2265791 := by
    simpa [prefixWord, tailWord_2265791, baseEnd_2265791] using wordTrace_append hprefix tailTrace_2265791
  have hstable : (prefixWord ++ tailWord_2265791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265791).length < 2 ^ (prefixWord ++ tailWord_2265791).sum := by decide
  have hdescent : baseEnd_2265791 < baseStart_2265791 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265847 : List Nat := [1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 5]
def baseStart_2265847 : Nat := 118140960795 + 2265847 * 2 ^ 59
def prefixEnd_2265847 : Nat := 4983230072969 + 3 ^ 40 * 2265847 * 2
def baseEnd_2265847 : Nat := 1163468600548101596892065

theorem tailTrace_2265847 : CollatzResearch.WordTrace tailWord_2265847 prefixEnd_2265847 1163468600548101596892065 := by
  unfold tailWord_2265847
  simp only [CollatzResearch.WordTrace]
  refine ⟨82642229422230769703987795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55094819614820513135991863 82642229422230769703987795)
  ·
    refine ⟨123963344133346154555981693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82642229422230769703987795 123963344133346154555981693)
    ·
      refine ⟨46486254050004807958493135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123963344133346154555981693 46486254050004807958493135)
      ·
        refine ⟨69729381075007211937739703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46486254050004807958493135 69729381075007211937739703)
        ·
          refine ⟨104594071612510817906609555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69729381075007211937739703 104594071612510817906609555)
          ·
            refine ⟨156891107418766226859914333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104594071612510817906609555 156891107418766226859914333)
            ·
              refine ⟨58834165282037335072467875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 156891107418766226859914333 58834165282037335072467875)
              ·
                refine ⟨88251247923056002608701813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58834165282037335072467875 88251247923056002608701813)
                ·
                  refine ⟨8273554492786500244565795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88251247923056002608701813 8273554492786500244565795)
                  ·
                    refine ⟨12410331739179750366848693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8273554492786500244565795 12410331739179750366848693)
                    ·
                      refine ⟨1163468600548101596892065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12410331739179750366848693 1163468600548101596892065)
                      ·
                        rfl

theorem cell23_2265847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_2265847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265847 prefixEnd_2265847 := by exact prefixLift 2265847
  have htrace : WordTrace (prefixWord ++ tailWord_2265847) baseStart_2265847 baseEnd_2265847 := by
    simpa [prefixWord, tailWord_2265847, baseEnd_2265847] using wordTrace_append hprefix tailTrace_2265847
  have hstable : (prefixWord ++ tailWord_2265847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265847).length < 2 ^ (prefixWord ++ tailWord_2265847).sum := by decide
  have hdescent : baseEnd_2265847 < baseStart_2265847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265861 : List Nat := [1, 3, 1, 1, 2, 1, 1, 4, 5, 2, 2]
def baseStart_2265861 : Nat := 118140960795 + 2265861 * 2 ^ 59
def prefixEnd_2265861 : Nat := 4983230072969 + 3 ^ 40 * 2265861 * 2
def baseEnd_2265861 : Nat := 1163475789277264542117001

theorem tailTrace_2265861 : CollatzResearch.WordTrace tailWord_2265861 prefixEnd_2265861 1163475789277264542117001 := by
  unfold tailWord_2265861
  simp only [CollatzResearch.WordTrace]
  refine ⟨82642740044180050094997437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55095160029453366729998291 82642740044180050094997437)
  ·
    refine ⟨30991027516567518785624039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82642740044180050094997437 30991027516567518785624039)
    ·
      refine ⟨46486541274851278178436059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30991027516567518785624039 46486541274851278178436059)
      ·
        refine ⟨69729811912276917267654089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46486541274851278178436059 69729811912276917267654089)
        ·
          refine ⟨52297358934207687950740567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69729811912276917267654089 52297358934207687950740567)
          ·
            refine ⟨78446038401311531926110851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52297358934207687950740567 78446038401311531926110851)
            ·
              refine ⟨117669057601967297889166277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78446038401311531926110851 117669057601967297889166277)
              ·
                refine ⟨22062948300368868354218677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117669057601967297889166277 22062948300368868354218677)
                ·
                  refine ⟨2068401403159581408208001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22062948300368868354218677 2068401403159581408208001)
                  ·
                    refine ⟨1551301052369686056156001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2068401403159581408208001 1551301052369686056156001)
                    ·
                      refine ⟨1163475789277264542117001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1551301052369686056156001 1163475789277264542117001)
                      ·
                        rfl

theorem cell23_2265861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 4, 5, 2, 2].length) (baseStart_2265861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265861 prefixEnd_2265861 := by exact prefixLift 2265861
  have htrace : WordTrace (prefixWord ++ tailWord_2265861) baseStart_2265861 baseEnd_2265861 := by
    simpa [prefixWord, tailWord_2265861, baseEnd_2265861] using wordTrace_append hprefix tailTrace_2265861
  have hstable : (prefixWord ++ tailWord_2265861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265861).length < 2 ^ (prefixWord ++ tailWord_2265861).sum := by decide
  have hdescent : baseEnd_2265861 < baseStart_2265861 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265864 : List Nat := [2, 1, 3, 2, 2, 2, 1, 3, 1, 1, 5]
def baseStart_2265864 : Nat := 118140960795 + 2265864 * 2 ^ 59
def prefixEnd_2265864 : Nat := 4983230072969 + 3 ^ 40 * 2265864 * 2
def baseEnd_2265864 : Nat := 1163477329719228030379487

theorem tailTrace_2265864 : CollatzResearch.WordTrace tailWord_2265864 prefixEnd_2265864 1163477329719228030379487 := by
  unfold tailWord_2265864
  simp only [CollatzResearch.WordTrace]
  refine ⟨41321424731584590803678323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55095232975446121071571097 41321424731584590803678323)
  ·
    refine ⟨61982137097376886205517485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41321424731584590803678323 61982137097376886205517485)
    ·
      refine ⟨23243301411516332327069057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61982137097376886205517485 23243301411516332327069057)
      ·
        refine ⟨17432476058637249245301793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23243301411516332327069057 17432476058637249245301793)
        ·
          refine ⟨13074357043977936933976345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17432476058637249245301793 13074357043977936933976345)
          ·
            refine ⟨9805767782983452700482259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13074357043977936933976345 9805767782983452700482259)
            ·
              refine ⟨14708651674475179050723389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9805767782983452700482259 14708651674475179050723389)
              ·
                refine ⟨5515744377928192144021271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14708651674475179050723389 5515744377928192144021271)
                ·
                  refine ⟨8273616566892288216031907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5515744377928192144021271 8273616566892288216031907)
                  ·
                    refine ⟨12410424850338432324047861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8273616566892288216031907 12410424850338432324047861)
                    ·
                      refine ⟨1163477329719228030379487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12410424850338432324047861 1163477329719228030379487)
                      ·
                        rfl

theorem cell23_2265864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_2265864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265864 prefixEnd_2265864 := by exact prefixLift 2265864
  have htrace : WordTrace (prefixWord ++ tailWord_2265864) baseStart_2265864 baseEnd_2265864 := by
    simpa [prefixWord, tailWord_2265864, baseEnd_2265864] using wordTrace_append hprefix tailTrace_2265864
  have hstable : (prefixWord ++ tailWord_2265864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265864).length < 2 ^ (prefixWord ++ tailWord_2265864).sum := by decide
  have hdescent : baseEnd_2265864 < baseStart_2265864 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265884 : List Nat := [2, 2, 3, 1, 1, 4, 2, 8]
def baseStart_2265884 : Nat := 118140960795 + 2265884 * 2 ^ 59
def prefixEnd_2265884 : Nat := 4983230072969 + 3 ^ 40 * 2265884 * 2
def baseEnd_2265884 : Nat := 43092133308604368597385

theorem tailTrace_2265884 : CollatzResearch.WordTrace tailWord_2265884 prefixEnd_2265884 43092133308604368597385 := by
  unfold tailWord_2265884
  simp only [CollatzResearch.WordTrace]
  refine ⟨41321789461548362511542353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55095719282064483348723137 41321789461548362511542353)
  ·
    refine ⟨30991342096161271883656765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41321789461548362511542353 30991342096161271883656765)
    ·
      refine ⟨11621753286060476956371287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30991342096161271883656765 11621753286060476956371287)
      ·
        refine ⟨17432629929090715434556931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11621753286060476956371287 17432629929090715434556931)
        ·
          refine ⟨26148944893636073151835397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17432629929090715434556931 26148944893636073151835397)
          ·
            refine ⟨4902927167556763715969137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26148944893636073151835397 4902927167556763715969137)
            ·
              refine ⟨3677195375667572786976853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4902927167556763715969137 3677195375667572786976853)
              ·
                refine ⟨43092133308604368597385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3677195375667572786976853 43092133308604368597385)
                ·
                  rfl

theorem cell23_2265884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 2, 8].length) (baseStart_2265884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265884 prefixEnd_2265884 := by exact prefixLift 2265884
  have htrace : WordTrace (prefixWord ++ tailWord_2265884) baseStart_2265884 baseEnd_2265884 := by
    simpa [prefixWord, tailWord_2265884, baseEnd_2265884] using wordTrace_append hprefix tailTrace_2265884
  have hstable : (prefixWord ++ tailWord_2265884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265884).length < 2 ^ (prefixWord ++ tailWord_2265884).sum := by decide
  have hdescent : baseEnd_2265884 < baseStart_2265884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265888 : List Nat := [2, 1, 1, 5, 1, 2, 4, 1, 2, 4]
def baseStart_2265888 : Nat := 118140960795 + 2265888 * 2 ^ 59
def prefixEnd_2265888 : Nat := 4983230072969 + 3 ^ 40 * 2265888 * 2
def baseEnd_2265888 : Nat := 387829884418311978826459

theorem tailTrace_2265888 : CollatzResearch.WordTrace tailWord_2265888 prefixEnd_2265888 387829884418311978826459 := by
  unfold tailWord_2265888
  simp only [CollatzResearch.WordTrace]
  refine ⟨41321862407541116853115159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55095816543388155804153545 41321862407541116853115159)
  ·
    refine ⟨61982793611311675279672739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41321862407541116853115159 61982793611311675279672739)
    ·
      refine ⟨92974190416967512919509109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61982793611311675279672739 92974190416967512919509109)
      ·
        refine ⟨8716330351590704336203979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 92974190416967512919509109 8716330351590704336203979)
        ·
          refine ⟨13074495527386056504305969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8716330351590704336203979 13074495527386056504305969)
          ·
            refine ⟨9805871645539542378229477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13074495527386056504305969 9805871645539542378229477)
            ·
              refine ⟨1838600933538664195918027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9805871645539542378229477 1838600933538664195918027)
              ·
                refine ⟨2757901400307996293877041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1838600933538664195918027 2757901400307996293877041)
                ·
                  refine ⟨2068426050230997220407781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2757901400307996293877041 2068426050230997220407781)
                  ·
                    refine ⟨387829884418311978826459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2068426050230997220407781 387829884418311978826459)
                    ·
                      rfl

theorem cell23_2265888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4, 1, 2, 4].length) (baseStart_2265888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265888 prefixEnd_2265888 := by exact prefixLift 2265888
  have htrace : WordTrace (prefixWord ++ tailWord_2265888) baseStart_2265888 baseEnd_2265888 := by
    simpa [prefixWord, tailWord_2265888, baseEnd_2265888] using wordTrace_append hprefix tailTrace_2265888
  have hstable : (prefixWord ++ tailWord_2265888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265888).length < 2 ^ (prefixWord ++ tailWord_2265888).sum := by decide
  have hdescent : baseEnd_2265888 < baseStart_2265888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265897 : List Nat := [1, 2, 1, 1, 1, 1, 1, 6, 2, 7]
def baseStart_2265897 : Nat := 118140960795 + 2265897 * 2 ^ 59
def prefixEnd_2265897 : Nat := 4983230072969 + 3 ^ 40 * 2265897 * 2
def baseEnd_2265897 : Nat := 387831424860275467088945

theorem tailTrace_2265897 : CollatzResearch.WordTrace tailWord_2265897 prefixEnd_2265897 387831424860275467088945 := by
  unfold tailWord_2265897
  simp only [CollatzResearch.WordTrace]
  refine ⟨82644053072049628243307945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55096035381366418828871963 82644053072049628243307945)
  ·
    refine ⟨61983039804037221182480959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82644053072049628243307945 61983039804037221182480959)
    ·
      refine ⟨92974559706055831773721439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61983039804037221182480959 92974559706055831773721439)
      ·
        refine ⟨139461839559083747660582159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92974559706055831773721439 139461839559083747660582159)
        ·
          refine ⟨209192759338625621490873239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139461839559083747660582159 209192759338625621490873239)
          ·
            refine ⟨313789139007938432236309859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209192759338625621490873239 313789139007938432236309859)
            ·
              refine ⟨470683708511907648354464789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313789139007938432236309859 470683708511907648354464789)
              ·
                refine ⟨22063298836495671016615537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 470683708511907648354464789 22063298836495671016615537)
                ·
                  refine ⟨16547474127371753262461653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22063298836495671016615537 16547474127371753262461653)
                  ·
                    refine ⟨387831424860275467088945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16547474127371753262461653 387831424860275467088945)
                    ·
                      rfl

theorem cell23_2265897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 6, 2, 7].length) (baseStart_2265897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265897 prefixEnd_2265897 := by exact prefixLift 2265897
  have htrace : WordTrace (prefixWord ++ tailWord_2265897) baseStart_2265897 baseEnd_2265897 := by
    simpa [prefixWord, tailWord_2265897, baseEnd_2265897] using wordTrace_append hprefix tailTrace_2265897
  have hstable : (prefixWord ++ tailWord_2265897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265897).length < 2 ^ (prefixWord ++ tailWord_2265897).sum := by decide
  have hdescent : baseEnd_2265897 < baseStart_2265897 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265908 : List Nat := [2, 5, 1, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_2265908 : Nat := 118140960795 + 2265908 * 2 ^ 59
def prefixEnd_2265908 : Nat := 4983230072969 + 3 ^ 40 * 2265908 * 2
def baseEnd_2265908 : Nat := 1163499922868025858229285

theorem tailTrace_2265908 : CollatzResearch.WordTrace tailWord_2265908 prefixEnd_2265908 1163499922868025858229285 := by
  unfold tailWord_2265908
  simp only [CollatzResearch.WordTrace]
  refine ⟨41322227137504888560979189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55096302850006518081305585 41322227137504888560979189)
  ·
    refine ⟨3873958794141083302591799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41322227137504888560979189 3873958794141083302591799)
    ·
      refine ⟨5810938191211624953887699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3873958794141083302591799 5810938191211624953887699)
      ·
        refine ⟨8716407286817437430831549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5810938191211624953887699 8716407286817437430831549)
        ·
          refine ⟨3268652732556539036561831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8716407286817437430831549 3268652732556539036561831)
          ·
            refine ⟨4902979098834808554842747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3268652732556539036561831 4902979098834808554842747)
            ·
              refine ⟨7354468648252212832264121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4902979098834808554842747 7354468648252212832264121)
              ·
                refine ⟨5515851486189159624198091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7354468648252212832264121 5515851486189159624198091)
                ·
                  refine ⟨8273777229283739436297137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5515851486189159624198091 8273777229283739436297137)
                  ·
                    refine ⟨6205332921962804577222853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8273777229283739436297137 6205332921962804577222853)
                    ·
                      refine ⟨1163499922868025858229285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6205332921962804577222853 1163499922868025858229285)
                      ·
                        rfl

theorem cell23_2265908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_2265908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265908 prefixEnd_2265908 := by exact prefixLift 2265908
  have htrace : WordTrace (prefixWord ++ tailWord_2265908) baseStart_2265908 baseEnd_2265908 := by
    simpa [prefixWord, tailWord_2265908, baseEnd_2265908] using wordTrace_append hprefix tailTrace_2265908
  have hstable : (prefixWord ++ tailWord_2265908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265908).length < 2 ^ (prefixWord ++ tailWord_2265908).sum := by decide
  have hdescent : baseEnd_2265908 < baseStart_2265908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265928 : List Nat := [2, 1, 3, 1, 1, 3, 4, 2, 2, 1, 3]
def baseStart_2265928 : Nat := 118140960795 + 2265928 * 2 ^ 59
def prefixEnd_2265928 : Nat := 4983230072969 + 3 ^ 40 * 2265928 * 2
def baseEnd_2265928 : Nat := 1163510192481115779979193

theorem tailTrace_2265928 : CollatzResearch.WordTrace tailWord_2265928 prefixEnd_2265928 1163510192481115779979193 := by
  unfold tailWord_2265928
  simp only [CollatzResearch.WordTrace]
  refine ⟨41322591867468660268843219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55096789156624880358457625 41322591867468660268843219)
  ·
    refine ⟨61983887801202990403264829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41322591867468660268843219 61983887801202990403264829)
    ·
      refine ⟨23243957925451121401224311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61983887801202990403264829 23243957925451121401224311)
      ·
        refine ⟨34865936888176682101836467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23243957925451121401224311 34865936888176682101836467)
        ·
          refine ⟨52298905332265023152754701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34865936888176682101836467 52298905332265023152754701)
          ·
            refine ⟨19612089499599383682283013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52298905332265023152754701 19612089499599383682283013)
            ·
              refine ⟨3677266781174884440428065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19612089499599383682283013 3677266781174884440428065)
              ·
                refine ⟨2757950085881163330321049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3677266781174884440428065 2757950085881163330321049)
                ·
                  refine ⟨2068462564410872497740787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2757950085881163330321049 2068462564410872497740787)
                  ·
                    refine ⟨3102693846616308746611181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2068462564410872497740787 3102693846616308746611181)
                    ·
                      refine ⟨1163510192481115779979193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3102693846616308746611181 1163510192481115779979193)
                      ·
                        rfl

theorem cell23_2265928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 4, 2, 2, 1, 3].length) (baseStart_2265928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265928 prefixEnd_2265928 := by exact prefixLift 2265928
  have htrace : WordTrace (prefixWord ++ tailWord_2265928) baseStart_2265928 baseEnd_2265928 := by
    simpa [prefixWord, tailWord_2265928, baseEnd_2265928] using wordTrace_append hprefix tailTrace_2265928
  have hstable : (prefixWord ++ tailWord_2265928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265928).length < 2 ^ (prefixWord ++ tailWord_2265928).sum := by decide
  have hdescent : baseEnd_2265928 < baseStart_2265928 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265964 : List Nat := [2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 4]
def baseStart_2265964 : Nat := 118140960795 + 2265964 * 2 ^ 59
def prefixEnd_2265964 : Nat := 4983230072969 + 3 ^ 40 * 2265964 * 2
def baseEnd_2265964 : Nat := 1163528677784677639129027

theorem tailTrace_2265964 : CollatzResearch.WordTrace tailWord_2265964 prefixEnd_2265964 1163528677784677639129027 := by
  unfold tailWord_2265964
  simp only [CollatzResearch.WordTrace]
  refine ⟨41323248381403449342998473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55097664508537932457331297 41323248381403449342998473)
  ·
    refine ⟨30992436286052587007248855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41323248381403449342998473 30992436286052587007248855)
    ·
      refine ⟨46488654429078880510873283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30992436286052587007248855 46488654429078880510873283)
      ·
        refine ⟨69732981643618320766309925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46488654429078880510873283 69732981643618320766309925)
        ·
          refine ⟨13074934058178435143683111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69732981643618320766309925 13074934058178435143683111)
          ·
            refine ⟨19612401087267652715524667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13074934058178435143683111 19612401087267652715524667)
            ·
              refine ⟨29418601630901479073287001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19612401087267652715524667 29418601630901479073287001)
              ·
                refine ⟨22063951223176109304965251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29418601630901479073287001 22063951223176109304965251)
                ·
                  refine ⟨33095926834764163957447877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22063951223176109304965251 33095926834764163957447877)
                  ·
                    refine ⟨6205486281518280742021477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33095926834764163957447877 6205486281518280742021477)
                    ·
                      refine ⟨1163528677784677639129027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6205486281518280742021477 1163528677784677639129027)
                      ·
                        rfl

theorem cell23_2265964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 4].length) (baseStart_2265964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265964 prefixEnd_2265964 := by exact prefixLift 2265964
  have htrace : WordTrace (prefixWord ++ tailWord_2265964) baseStart_2265964 baseEnd_2265964 := by
    simpa [prefixWord, tailWord_2265964, baseEnd_2265964] using wordTrace_append hprefix tailTrace_2265964
  have hstable : (prefixWord ++ tailWord_2265964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265964).length < 2 ^ (prefixWord ++ tailWord_2265964).sum := by decide
  have hdescent : baseEnd_2265964 < baseStart_2265964 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2265991 : List Nat := [1, 1, 4, 2, 3, 2, 2, 1, 7]
def baseStart_2265991 : Nat := 118140960795 + 2265991 * 2 ^ 59
def prefixEnd_2265991 : Nat := 4983230072969 + 3 ^ 40 * 2265991 * 2
def baseEnd_2265991 : Nat := 129282504640261003721267

theorem tailTrace_2265991 : CollatzResearch.WordTrace tailWord_2265991 prefixEnd_2265991 129282504640261003721267 := by
  unfold tailWord_2265991
  simp only [CollatzResearch.WordTrace]
  refine ⟨82647481533709082297229827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55098321022472721531486551 82647481533709082297229827)
  ·
    refine ⟨123971222300563623445844741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82647481533709082297229827 123971222300563623445844741)
    ·
      refine ⟨23244604181355679396095889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 123971222300563623445844741 23244604181355679396095889)
      ·
        refine ⟨17433453136016759547071917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23244604181355679396095889 17433453136016759547071917)
        ·
          refine ⟨6537544926006284830151969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17433453136016759547071917 6537544926006284830151969)
          ·
            refine ⟨4903158694504713622613977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6537544926006284830151969 4903158694504713622613977)
            ·
              refine ⟨3677369020878535216960483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4903158694504713622613977 3677369020878535216960483)
              ·
                refine ⟨5516053531317802825440725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3677369020878535216960483 5516053531317802825440725)
                ·
                  refine ⟨129282504640261003721267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5516053531317802825440725 129282504640261003721267)
                  ·
                    rfl

theorem cell23_2265991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 2, 1, 7].length) (baseStart_2265991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2265991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2265991 prefixEnd_2265991 := by exact prefixLift 2265991
  have htrace : WordTrace (prefixWord ++ tailWord_2265991) baseStart_2265991 baseEnd_2265991 := by
    simpa [prefixWord, tailWord_2265991, baseEnd_2265991] using wordTrace_append hprefix tailTrace_2265991
  have hstable : (prefixWord ++ tailWord_2265991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2265991).length < 2 ^ (prefixWord ++ tailWord_2265991).sum := by decide
  have hdescent : baseEnd_2265991 < baseStart_2265991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2265991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266002 : List Nat := [3, 2, 3, 2, 2, 2, 1, 1, 1, 4, 2]
def baseStart_2266002 : Nat := 118140960795 + 2266002 * 2 ^ 59
def prefixEnd_2266002 : Nat := 4983230072969 + 3 ^ 40 * 2266002 * 2
def baseEnd_2266002 : Nat := 1163548190049548490453853

theorem tailTrace_2266002 : CollatzResearch.WordTrace tailWord_2266002 prefixEnd_2266002 1163548190049548490453853 := by
  unfold tailWord_2266002
  simp only [CollatzResearch.WordTrace]
  refine ⟨20661970684167307793970065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55098588491112820783920173 20661970684167307793970065)
  ·
    refine ⟨15496478013125480845477549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20661970684167307793970065 15496478013125480845477549)
    ·
      refine ⟨5811179254922055317054081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15496478013125480845477549 5811179254922055317054081)
      ·
        refine ⟨4358384441191541487790561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5811179254922055317054081 4358384441191541487790561)
        ·
          refine ⟨3268788330893656115842921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4358384441191541487790561 3268788330893656115842921)
          ·
            refine ⟨2451591248170242086882191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3268788330893656115842921 2451591248170242086882191)
            ·
              refine ⟨3677386872255363130323287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2451591248170242086882191 3677386872255363130323287)
              ·
                refine ⟨5516080308383044695484931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3677386872255363130323287 5516080308383044695484931)
                ·
                  refine ⟨8274120462574567043227397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5516080308383044695484931 8274120462574567043227397)
                  ·
                    refine ⟨1551397586732731320605137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8274120462574567043227397 1551397586732731320605137)
                    ·
                      refine ⟨1163548190049548490453853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1551397586732731320605137 1163548190049548490453853)
                      ·
                        rfl

theorem cell23_2266002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_2266002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266002 prefixEnd_2266002 := by exact prefixLift 2266002
  have htrace : WordTrace (prefixWord ++ tailWord_2266002) baseStart_2266002 baseEnd_2266002 := by
    simpa [prefixWord, tailWord_2266002, baseEnd_2266002] using wordTrace_append hprefix tailTrace_2266002
  have hstable : (prefixWord ++ tailWord_2266002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266002).length < 2 ^ (prefixWord ++ tailWord_2266002).sum := by decide
  have hdescent : baseEnd_2266002 < baseStart_2266002 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266041 : List Nat := [1, 2, 1, 4, 2, 2, 1, 1, 4, 1, 4]
def baseStart_2266041 : Nat := 118140960795 + 2266041 * 2 ^ 59
def prefixEnd_2266041 : Nat := 4983230072969 + 3 ^ 40 * 2266041 * 2
def baseEnd_2266041 : Nat := 1163568215795073837866173

theorem tailTrace_2266041 : CollatzResearch.WordTrace tailWord_2266041 prefixEnd_2266041 1163568215795073837866173 := by
  unfold tailWord_2266041
  simp only [CollatzResearch.WordTrace]
  refine ⟨82649305183527940836549977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55099536789018627224366651 82649305183527940836549977)
  ·
    refine ⟨61986978887645955627412483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82649305183527940836549977 61986978887645955627412483)
    ·
      refine ⟨92980468331468933441118725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61986978887645955627412483 92980468331468933441118725)
      ·
        refine ⟨17433837812150425020209761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 92980468331468933441118725 17433837812150425020209761)
        ·
          refine ⟨13075378359112818765157321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17433837812150425020209761 13075378359112818765157321)
          ·
            refine ⟨9806533769334614073867991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13075378359112818765157321 9806533769334614073867991)
            ·
              refine ⟨14709800654001921110801987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9806533769334614073867991 14709800654001921110801987)
              ·
                refine ⟨22064700981002881666202981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14709800654001921110801987 22064700981002881666202981)
                ·
                  refine ⟨4137131433938040312413059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22064700981002881666202981 4137131433938040312413059)
                  ·
                    refine ⟨6205697150907060468619589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4137131433938040312413059 6205697150907060468619589)
                    ·
                      refine ⟨1163568215795073837866173, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6205697150907060468619589 1163568215795073837866173)
                      ·
                        rfl

theorem cell23_2266041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_2266041 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266041 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266041 prefixEnd_2266041 := by exact prefixLift 2266041
  have htrace : WordTrace (prefixWord ++ tailWord_2266041) baseStart_2266041 baseEnd_2266041 := by
    simpa [prefixWord, tailWord_2266041, baseEnd_2266041] using wordTrace_append hprefix tailTrace_2266041
  have hstable : (prefixWord ++ tailWord_2266041).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266041).length < 2 ^ (prefixWord ++ tailWord_2266041).sum := by decide
  have hdescent : baseEnd_2266041 < baseStart_2266041 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266102 : List Nat := [5, 1, 1, 1, 3, 2, 1, 4, 1, 4]
def baseStart_2266102 : Nat := 118140960795 + 2266102 * 2 ^ 59
def prefixEnd_2266102 : Nat := 4983230072969 + 3 ^ 40 * 2266102 * 2
def baseEnd_2266102 : Nat := 387866512704999366401131

theorem tailTrace_2266102 : CollatzResearch.WordTrace tailWord_2266102 prefixEnd_2266102 387866512704999366401131 := by
  unfold tailWord_2266102
  simp only [CollatzResearch.WordTrace]
  refine ⟨5165720627269184265907535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55101020024204632169680373 5165720627269184265907535)
  ·
    refine ⟨7748580940903776398861303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5165720627269184265907535 7748580940903776398861303)
    ·
      refine ⟨11622871411355664598291955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7748580940903776398861303 11622871411355664598291955)
      ·
        refine ⟨17434307117033496897437933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11622871411355664598291955 17434307117033496897437933)
        ·
          refine ⟨6537865168887561336539225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17434307117033496897437933 6537865168887561336539225)
          ·
            refine ⟨4903398876665671002404419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6537865168887561336539225 4903398876665671002404419)
            ·
              refine ⟨7355098314998506503606629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4903398876665671002404419 7355098314998506503606629)
              ·
                refine ⟨1379080934062219969426243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7355098314998506503606629 1379080934062219969426243)
                ·
                  refine ⟨2068621401093329954139365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1379080934062219969426243 2068621401093329954139365)
                  ·
                    refine ⟨387866512704999366401131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2068621401093329954139365 387866512704999366401131)
                    ·
                      rfl

theorem cell23_2266102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 4, 1, 4].length) (baseStart_2266102 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266102 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266102 prefixEnd_2266102 := by exact prefixLift 2266102
  have htrace : WordTrace (prefixWord ++ tailWord_2266102) baseStart_2266102 baseEnd_2266102 := by
    simpa [prefixWord, tailWord_2266102, baseEnd_2266102] using wordTrace_append hprefix tailTrace_2266102
  have hstable : (prefixWord ++ tailWord_2266102).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266102).length < 2 ^ (prefixWord ++ tailWord_2266102).sum := by decide
  have hdescent : baseEnd_2266102 < baseStart_2266102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266135 : List Nat := [1, 1, 3, 5, 1, 2, 1, 1, 1, 5, 2]
def baseStart_2266135 : Nat := 118140960795 + 2266135 * 2 ^ 59
def prefixEnd_2266135 : Nat := 4983230072969 + 3 ^ 40 * 2266135 * 2
def baseEnd_2266135 : Nat := 1163616482976596470090741

theorem tailTrace_2266135 : CollatzResearch.WordTrace tailWord_2266135 prefixEnd_2266135 1163616482976596470090741 := by
  unfold tailWord_2266135
  simp only [CollatzResearch.WordTrace]
  refine ⟨82652733645187394890471859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55101822430124929926981239 82652733645187394890471859)
  ·
    refine ⟨123979100467781092335707789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82652733645187394890471859 123979100467781092335707789)
    ·
      refine ⟨46492162675417909625890421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123979100467781092335707789 46492162675417909625890421)
      ·
        refine ⟨4358640250820429027427227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46492162675417909625890421 4358640250820429027427227)
        ·
          refine ⟨6537960376230643541140841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4358640250820429027427227 6537960376230643541140841)
          ·
            refine ⟨4903470282172982655855631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6537960376230643541140841 4903470282172982655855631)
            ·
              refine ⟨7355205423259473983783447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4903470282172982655855631 7355205423259473983783447)
              ·
                refine ⟨11032808134889210975675171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7355205423259473983783447 11032808134889210975675171)
                ·
                  refine ⟨16549212202333816463512757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11032808134889210975675171 16549212202333816463512757)
                  ·
                    refine ⟨1551488643968795293454321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16549212202333816463512757 1551488643968795293454321)
                    ·
                      refine ⟨1163616482976596470090741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1551488643968795293454321 1163616482976596470090741)
                      ·
                        rfl

theorem cell23_2266135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 1, 5, 2].length) (baseStart_2266135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266135 prefixEnd_2266135 := by exact prefixLift 2266135
  have htrace : WordTrace (prefixWord ++ tailWord_2266135) baseStart_2266135 baseEnd_2266135 := by
    simpa [prefixWord, tailWord_2266135, baseEnd_2266135] using wordTrace_append hprefix tailTrace_2266135
  have hstable : (prefixWord ++ tailWord_2266135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266135).length < 2 ^ (prefixWord ++ tailWord_2266135).sum := by decide
  have hdescent : baseEnd_2266135 < baseStart_2266135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266145 : List Nat := [1, 2, 3, 2, 3, 1, 4, 1, 1, 5]
def baseStart_2266145 : Nat := 118140960795 + 2266145 * 2 ^ 59
def prefixEnd_2266145 : Nat := 4983230072969 + 3 ^ 40 * 2266145 * 2
def baseEnd_2266145 : Nat := 387873872594380476988565

theorem tailTrace_2266145 : CollatzResearch.WordTrace tailWord_2266145 prefixEnd_2266145 387873872594380476988565 := by
  unfold tailWord_2266145
  simp only [CollatzResearch.WordTrace]
  refine ⟨82653098375151166598335889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55102065583434111065557259 82653098375151166598335889)
  ·
    refine ⟨61989823781363374948751917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82653098375151166598335889 61989823781363374948751917)
    ·
      refine ⟨23246183918011265605781969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 61989823781363374948751917 23246183918011265605781969)
      ·
        refine ⟨17434637938508449204336477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23246183918011265605781969 17434637938508449204336477)
        ·
          refine ⟨6537989226940668451626179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17434637938508449204336477 6537989226940668451626179)
          ·
            refine ⟨9806983840411002677439269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6537989226940668451626179 9806983840411002677439269)
            ·
              refine ⟨1838809470077063002019863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9806983840411002677439269 1838809470077063002019863)
              ·
                refine ⟨2758214205115594503029795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1838809470077063002019863 2758214205115594503029795)
                ·
                  refine ⟨4137321307673391754544693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2758214205115594503029795 4137321307673391754544693)
                  ·
                    refine ⟨387873872594380476988565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4137321307673391754544693 387873872594380476988565)
                    ·
                      rfl

theorem cell23_2266145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 1, 4, 1, 1, 5].length) (baseStart_2266145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266145 prefixEnd_2266145 := by exact prefixLift 2266145
  have htrace : WordTrace (prefixWord ++ tailWord_2266145) baseStart_2266145 baseEnd_2266145 := by
    simpa [prefixWord, tailWord_2266145, baseEnd_2266145] using wordTrace_append hprefix tailTrace_2266145
  have hstable : (prefixWord ++ tailWord_2266145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266145).length < 2 ^ (prefixWord ++ tailWord_2266145).sum := by decide
  have hdescent : baseEnd_2266145 < baseStart_2266145 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266161 : List Nat := [1, 2, 2, 3, 1, 2, 2, 2, 1, 1, 6]
def baseStart_2266161 : Nat := 118140960795 + 2266161 * 2 ^ 59
def prefixEnd_2266161 : Nat := 4983230072969 + 3 ^ 40 * 2266161 * 2
def baseEnd_2266161 : Nat := 1163629833473613368365621

theorem tailTrace_2266161 : CollatzResearch.WordTrace tailWord_2266161 prefixEnd_2266161 1163629833473613368365621 := by
  unfold tailWord_2266161
  simp only [CollatzResearch.WordTrace]
  refine ⟨82653681943093201330918337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55102454628728800887278891 82653681943093201330918337)
  ·
    refine ⟨61990261457319900998188753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82653681943093201330918337 61990261457319900998188753)
    ·
      refine ⟨46492696092989925748641565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61990261457319900998188753 46492696092989925748641565)
      ·
        refine ⟨17434761034871222155740587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46492696092989925748641565 17434761034871222155740587)
        ·
          refine ⟨26152141552306833233610881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17434761034871222155740587 26152141552306833233610881)
          ·
            refine ⟨19614106164230124925208161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26152141552306833233610881 19614106164230124925208161)
            ·
              refine ⟨14710579623172593693906121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19614106164230124925208161 14710579623172593693906121)
              ·
                refine ⟨11032934717379445270429591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14710579623172593693906121 11032934717379445270429591)
                ·
                  refine ⟨16549402076069167905644387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11032934717379445270429591 16549402076069167905644387)
                  ·
                    refine ⟨24824103114103751858466581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16549402076069167905644387 24824103114103751858466581)
                    ·
                      refine ⟨1163629833473613368365621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24824103114103751858466581 1163629833473613368365621)
                      ·
                        rfl

theorem cell23_2266161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_2266161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266161 prefixEnd_2266161 := by exact prefixLift 2266161
  have htrace : WordTrace (prefixWord ++ tailWord_2266161) baseStart_2266161 baseEnd_2266161 := by
    simpa [prefixWord, tailWord_2266161, baseEnd_2266161] using wordTrace_append hprefix tailTrace_2266161
  have hstable : (prefixWord ++ tailWord_2266161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266161).length < 2 ^ (prefixWord ++ tailWord_2266161).sum := by decide
  have hdescent : baseEnd_2266161 < baseStart_2266161 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266168 : List Nat := [2, 1, 2, 1, 5, 2, 1, 2, 1, 1, 5]
def baseStart_2266168 : Nat := 118140960795 + 2266168 * 2 ^ 59
def prefixEnd_2266168 : Nat := 4983230072969 + 3 ^ 40 * 2266168 * 2
def baseEnd_2266168 : Nat := 1163633427838194840978089

theorem tailTrace_2266168 : CollatzResearch.WordTrace tailWord_2266168 prefixEnd_2266168 1163633427838194840978089 := by
  unfold tailWord_2266168
  simp only [CollatzResearch.WordTrace]
  refine ⟨41326968627033920763211579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55102624836045227684282105 41326968627033920763211579)
  ·
    refine ⟨61990452940550881144817369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41326968627033920763211579 61990452940550881144817369)
    ·
      refine ⟨46492839705413160858613027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61990452940550881144817369 46492839705413160858613027)
      ·
        refine ⟨69739259558119741287919541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46492839705413160858613027 69739259558119741287919541)
        ·
          refine ⟨6538055583573725745742457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69739259558119741287919541 6538055583573725745742457)
          ·
            refine ⟨4903541687680294309306843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6538055583573725745742457 4903541687680294309306843)
            ·
              refine ⟨7355312531520441463960265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4903541687680294309306843 7355312531520441463960265)
              ·
                refine ⟨5516484398640331097970199, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7355312531520441463960265 5516484398640331097970199)
                ·
                  refine ⟨8274726597960496646955299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5516484398640331097970199 8274726597960496646955299)
                  ·
                    refine ⟨12412089896940744970432949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8274726597960496646955299 12412089896940744970432949)
                    ·
                      refine ⟨1163633427838194840978089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12412089896940744970432949 1163633427838194840978089)
                      ·
                        rfl

theorem cell23_2266168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 2, 1, 2, 1, 1, 5].length) (baseStart_2266168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266168 prefixEnd_2266168 := by exact prefixLift 2266168
  have htrace : WordTrace (prefixWord ++ tailWord_2266168) baseStart_2266168 baseEnd_2266168 := by
    simpa [prefixWord, tailWord_2266168, baseEnd_2266168] using wordTrace_append hprefix tailTrace_2266168
  have hstable : (prefixWord ++ tailWord_2266168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266168).length < 2 ^ (prefixWord ++ tailWord_2266168).sum := by decide
  have hdescent : baseEnd_2266168 < baseStart_2266168 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266182 : List Nat := [6, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4]
def baseStart_2266182 : Nat := 118140960795 + 2266182 * 2 ^ 59
def prefixEnd_2266182 : Nat := 4983230072969 + 3 ^ 40 * 2266182 * 2
def baseEnd_2266182 : Nat := 1163640616567357786203025

theorem tailTrace_2266182 : CollatzResearch.WordTrace tailWord_2266182 prefixEnd_2266182 1163640616567357786203025 := by
  unfold tailWord_2266182
  simp only [CollatzResearch.WordTrace]
  refine ⟨2582951496125535059919775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55102965250678081278288533 2582951496125535059919775)
  ·
    refine ⟨3874427244188302589879663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2582951496125535059919775 3874427244188302589879663)
    ·
      refine ⟨5811640866282453884819495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3874427244188302589879663 5811640866282453884819495)
      ·
        refine ⟨8717461299423680827229243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5811640866282453884819495 8717461299423680827229243)
        ·
          refine ⟨13076191949135521240843865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8717461299423680827229243 13076191949135521240843865)
          ·
            refine ⟨9807143961851640930632899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13076191949135521240843865 9807143961851640930632899)
            ·
              refine ⟨14710715942777461395949349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9807143961851640930632899 14710715942777461395949349)
              ·
                refine ⟨2758259239270774011740503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14710715942777461395949349 2758259239270774011740503)
                ·
                  refine ⟨4137388858906161017610755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2758259239270774011740503 4137388858906161017610755)
                  ·
                    refine ⟨6206083288359241526416133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4137388858906161017610755 6206083288359241526416133)
                    ·
                      refine ⟨1163640616567357786203025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6206083288359241526416133 1163640616567357786203025)
                      ·
                        rfl

theorem cell23_2266182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_2266182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266182 prefixEnd_2266182 := by exact prefixLift 2266182
  have htrace : WordTrace (prefixWord ++ tailWord_2266182) baseStart_2266182 baseEnd_2266182 := by
    simpa [prefixWord, tailWord_2266182, baseEnd_2266182] using wordTrace_append hprefix tailTrace_2266182
  have hstable : (prefixWord ++ tailWord_2266182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266182).length < 2 ^ (prefixWord ++ tailWord_2266182).sum := by decide
  have hdescent : baseEnd_2266182 < baseStart_2266182 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266205 : List Nat := [1, 4, 4, 1, 2, 2, 9]
def baseStart_2266205 : Nat := 118140960795 + 2266205 * 2 ^ 59
def prefixEnd_2266205 : Nat := 4983230072969 + 3 ^ 40 * 2266205 * 2
def baseEnd_2266205 : Nat := 14366079341017422175499

theorem tailTrace_2266205 : CollatzResearch.WordTrace tailWord_2266205 prefixEnd_2266205 14366079341017422175499 := by
  unfold tailWord_2266205
  simp only [CollatzResearch.WordTrace]
  refine ⟨82655286754933796845520069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55103524503289197897013379 82655286754933796845520069)
  ·
    refine ⟨15497866266550086908535013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82655286754933796845520069 15497866266550086908535013)
    ·
      refine ⟨2905849924978141295350315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15497866266550086908535013 2905849924978141295350315)
      ·
        refine ⟨4358774887467211943025473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2905849924978141295350315 4358774887467211943025473)
        ·
          refine ⟨3269081165600408957269105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4358774887467211943025473 3269081165600408957269105)
          ·
            refine ⟨2451810874200306717951829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3269081165600408957269105 2451810874200306717951829)
            ·
              refine ⟨14366079341017422175499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 2451810874200306717951829 14366079341017422175499)
              ·
                rfl

theorem cell23_2266205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 9].length) (baseStart_2266205 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266205 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266205 prefixEnd_2266205 := by exact prefixLift 2266205
  have htrace : WordTrace (prefixWord ++ tailWord_2266205) baseStart_2266205 baseEnd_2266205 := by
    simpa [prefixWord, tailWord_2266205, baseEnd_2266205] using wordTrace_append hprefix tailTrace_2266205
  have hstable : (prefixWord ++ tailWord_2266205).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266205).length < 2 ^ (prefixWord ++ tailWord_2266205).sum := by decide
  have hdescent : baseEnd_2266205 < baseStart_2266205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266211 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 5]
def baseStart_2266211 : Nat := 118140960795 + 2266211 * 2 ^ 59
def prefixEnd_2266211 : Nat := 4983230072969 + 3 ^ 40 * 2266211 * 2
def baseEnd_2266211 : Nat := 1163655507506338172740391

theorem tailTrace_2266211 : CollatzResearch.WordTrace tailWord_2266211 prefixEnd_2266211 1163655507506338172740391 := by
  unfold tailWord_2266211
  simp only [CollatzResearch.WordTrace]
  refine ⟨82655505592912059870238487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55103670395274706580158991 82655505592912059870238487)
  ·
    refine ⟨123983258389368089805357731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82655505592912059870238487 123983258389368089805357731)
    ·
      refine ⟨185974887584052134708036597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123983258389368089805357731 185974887584052134708036597)
      ·
        refine ⟨17435145711004887628878431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 185974887584052134708036597 17435145711004887628878431)
        ·
          refine ⟨26152718566507331443317647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17435145711004887628878431 26152718566507331443317647)
          ·
            refine ⟨39229077849760997164976471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26152718566507331443317647 39229077849760997164976471)
            ·
              refine ⟨58843616774641495747464707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39229077849760997164976471 58843616774641495747464707)
              ·
                refine ⟨88265425161962243621197061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58843616774641495747464707 88265425161962243621197061)
                ·
                  refine ⟨16549767217867920678974449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88265425161962243621197061 16549767217867920678974449)
                  ·
                    refine ⟨12412325413400940509230837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16549767217867920678974449 12412325413400940509230837)
                    ·
                      refine ⟨1163655507506338172740391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12412325413400940509230837 1163655507506338172740391)
                      ·
                        rfl

theorem cell23_2266211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_2266211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266211 prefixEnd_2266211 := by exact prefixLift 2266211
  have htrace : WordTrace (prefixWord ++ tailWord_2266211) baseStart_2266211 baseEnd_2266211 := by
    simpa [prefixWord, tailWord_2266211, baseEnd_2266211] using wordTrace_append hprefix tailTrace_2266211
  have hstable : (prefixWord ++ tailWord_2266211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266211).length < 2 ^ (prefixWord ++ tailWord_2266211).sum := by decide
  have hdescent : baseEnd_2266211 < baseStart_2266211 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266215 : List Nat := [1, 1, 5, 1, 1, 3, 2, 1, 4, 1, 3]
def baseStart_2266215 : Nat := 118140960795 + 2266215 * 2 ^ 59
def prefixEnd_2266215 : Nat := 4983230072969 + 3 ^ 40 * 2266215 * 2
def baseEnd_2266215 : Nat := 1163657561428956157090373

theorem tailTrace_2266215 : CollatzResearch.WordTrace tailWord_2266215 prefixEnd_2266215 1163657561428956157090373 := by
  unfold tailWord_2266215
  simp only [CollatzResearch.WordTrace]
  refine ⟨82655651484897568553384099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55103767656598379035589399 82655651484897568553384099)
  ·
    refine ⟨123983477227346352830076149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82655651484897568553384099 123983477227346352830076149)
    ·
      refine ⟨11623450990063720577819639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 123983477227346352830076149 11623450990063720577819639)
      ·
        refine ⟨17435176485095580866729459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11623450990063720577819639 17435176485095580866729459)
        ·
          refine ⟨26152764727643371300094189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17435176485095580866729459 26152764727643371300094189)
          ·
            refine ⟨9807286772866264237535321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26152764727643371300094189 9807286772866264237535321)
            ·
              refine ⟨7355465079649698178151491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9807286772866264237535321 7355465079649698178151491)
              ·
                refine ⟨11033197619474547267227237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7355465079649698178151491 11033197619474547267227237)
                ·
                  refine ⟨2068724553651477612605107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11033197619474547267227237 2068724553651477612605107)
                  ·
                    refine ⟨3103086830477216418907661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2068724553651477612605107 3103086830477216418907661)
                    ·
                      refine ⟨1163657561428956157090373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3103086830477216418907661 1163657561428956157090373)
                      ·
                        rfl

theorem cell23_2266215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 4, 1, 3].length) (baseStart_2266215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266215 prefixEnd_2266215 := by exact prefixLift 2266215
  have htrace : WordTrace (prefixWord ++ tailWord_2266215) baseStart_2266215 baseEnd_2266215 := by
    simpa [prefixWord, tailWord_2266215, baseEnd_2266215] using wordTrace_append hprefix tailTrace_2266215
  have hstable : (prefixWord ++ tailWord_2266215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266215).length < 2 ^ (prefixWord ++ tailWord_2266215).sum := by decide
  have hdescent : baseEnd_2266215 < baseStart_2266215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266216 : List Nat := [2, 1, 4, 4, 1, 2, 1, 1, 3, 2, 2]
def baseStart_2266216 : Nat := 118140960795 + 2266216 * 2 ^ 59
def prefixEnd_2266216 : Nat := 4983230072969 + 3 ^ 40 * 2266216 * 2
def baseEnd_2266216 : Nat := 1163658074909610653177869

theorem tailTrace_2266216 : CollatzResearch.WordTrace tailWord_2266216 prefixEnd_2266216 1163658074909610653177869 := by
  unfold tailWord_2266216
  simp only [CollatzResearch.WordTrace]
  refine ⟨41327843978946972862085251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55103791971929297149447001 41327843978946972862085251)
  ·
    refine ⟨61991765968420459293127877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41327843978946972862085251 61991765968420459293127877)
    ·
      refine ⟨11623456119078836117461477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 61991765968420459293127877 11623456119078836117461477)
      ·
        refine ⟨2179398022327281772024027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11623456119078836117461477 2179398022327281772024027)
        ·
          refine ⟨3269097033490922658036041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2179398022327281772024027 3269097033490922658036041)
          ·
            refine ⟨2451822775118191993527031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3269097033490922658036041 2451822775118191993527031)
            ·
              refine ⟨3677734162677287990290547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2451822775118191993527031 3677734162677287990290547)
              ·
                refine ⟨5516601244015931985435821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3677734162677287990290547 5516601244015931985435821)
                ·
                  refine ⟨2068725466505974494538433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5516601244015931985435821 2068725466505974494538433)
                  ·
                    refine ⟨1551544099879480870903825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2068725466505974494538433 1551544099879480870903825)
                    ·
                      refine ⟨1163658074909610653177869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1551544099879480870903825 1163658074909610653177869)
                      ·
                        rfl

theorem cell23_2266216_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 2, 1, 1, 3, 2, 2].length) (baseStart_2266216 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266216 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266216 prefixEnd_2266216 := by exact prefixLift 2266216
  have htrace : WordTrace (prefixWord ++ tailWord_2266216) baseStart_2266216 baseEnd_2266216 := by
    simpa [prefixWord, tailWord_2266216, baseEnd_2266216] using wordTrace_append hprefix tailTrace_2266216
  have hstable : (prefixWord ++ tailWord_2266216).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266216).length < 2 ^ (prefixWord ++ tailWord_2266216).sum := by decide
  have hdescent : baseEnd_2266216 < baseStart_2266216 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266216) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266231 : List Nat := [1, 1, 3, 1, 1, 4, 2, 1, 1, 8]
def baseStart_2266231 : Nat := 118140960795 + 2266231 * 2 ^ 59
def prefixEnd_2266231 : Nat := 4983230072969 + 3 ^ 40 * 2266231 * 2
def baseEnd_2266231 : Nat := 387888592373142698163433

theorem tailTrace_2266231 : CollatzResearch.WordTrace tailWord_2266231 prefixEnd_2266231 387888592373142698163433 := by
  unfold tailWord_2266231
  simp only [CollatzResearch.WordTrace]
  refine ⟨82656235052839603285966547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55104156701893068857311031 82656235052839603285966547)
  ·
    refine ⟨123984352579259404928949821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82656235052839603285966547 123984352579259404928949821)
    ·
      refine ⟨46494132217222276848356183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 123984352579259404928949821 46494132217222276848356183)
      ·
        refine ⟨69741198325833415272534275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46494132217222276848356183 69741198325833415272534275)
        ·
          refine ⟨104611797488750122908801413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69741198325833415272534275 104611797488750122908801413)
          ·
            refine ⟨19614712029140648045400265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104611797488750122908801413 19614712029140648045400265)
            ·
              refine ⟨14711034021855486034050199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19614712029140648045400265 14711034021855486034050199)
              ·
                refine ⟨22066551032783229051075299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14711034021855486034050199 22066551032783229051075299)
                ·
                  refine ⟨33099826549174843576612949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22066551032783229051075299 33099826549174843576612949)
                  ·
                    refine ⟨387888592373142698163433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33099826549174843576612949 387888592373142698163433)
                    ·
                      rfl

theorem cell23_2266231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_2266231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266231 prefixEnd_2266231 := by exact prefixLift 2266231
  have htrace : WordTrace (prefixWord ++ tailWord_2266231) baseStart_2266231 baseEnd_2266231 := by
    simpa [prefixWord, tailWord_2266231, baseEnd_2266231] using wordTrace_append hprefix tailTrace_2266231
  have hstable : (prefixWord ++ tailWord_2266231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266231).length < 2 ^ (prefixWord ++ tailWord_2266231).sum := by decide
  have hdescent : baseEnd_2266231 < baseStart_2266231 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266232 : List Nat := [2, 1, 2, 1, 1, 1, 8, 1, 2, 1, 3]
def baseStart_2266232 : Nat := 118140960795 + 2266232 * 2 ^ 59
def prefixEnd_2266232 : Nat := 4983230072969 + 3 ^ 40 * 2266232 * 2
def baseEnd_2266232 : Nat := 1163666290600082590577795

theorem tailTrace_2266232 : CollatzResearch.WordTrace tailWord_2266232 prefixEnd_2266232 1163666290600082590577795 := by
  unfold tailWord_2266232
  simp only [CollatzResearch.WordTrace]
  refine ⟨41328135762917990228376475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55104181017223986971168633 41328135762917990228376475)
  ·
    refine ⟨61992203644376985342564713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41328135762917990228376475 61992203644376985342564713)
    ·
      refine ⟨46494152733282739006923535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61992203644376985342564713 46494152733282739006923535)
      ·
        refine ⟨69741229099924108510385303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46494152733282739006923535 69741229099924108510385303)
        ·
          refine ⟨104611843649886162765577955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69741229099924108510385303 104611843649886162765577955)
          ·
            refine ⟨156917765474829244148366933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104611843649886162765577955 156917765474829244148366933)
            ·
              refine ⟨1838880064158155204863675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 156917765474829244148366933 1838880064158155204863675)
              ·
                refine ⟨2758320096237232807295513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1838880064158155204863675 2758320096237232807295513)
                ·
                  refine ⟨2068740072177924605471635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2758320096237232807295513 2068740072177924605471635)
                  ·
                    refine ⟨3103110108266886908207453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2068740072177924605471635 3103110108266886908207453)
                    ·
                      refine ⟨1163666290600082590577795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3103110108266886908207453 1163666290600082590577795)
                      ·
                        rfl

theorem cell23_2266232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 8, 1, 2, 1, 3].length) (baseStart_2266232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266232 prefixEnd_2266232 := by exact prefixLift 2266232
  have htrace : WordTrace (prefixWord ++ tailWord_2266232) baseStart_2266232 baseEnd_2266232 := by
    simpa [prefixWord, tailWord_2266232, baseEnd_2266232] using wordTrace_append hprefix tailTrace_2266232
  have hstable : (prefixWord ++ tailWord_2266232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266232).length < 2 ^ (prefixWord ++ tailWord_2266232).sum := by decide
  have hdescent : baseEnd_2266232 < baseStart_2266232 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266261 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 11]
def baseStart_2266261 : Nat := 118140960795 + 2266261 * 2 ^ 59
def prefixEnd_2266261 : Nat := 4983230072969 + 3 ^ 40 * 2266261 * 2
def baseEnd_2266261 : Nat := 129297909059895886346129

theorem tailTrace_2266261 : CollatzResearch.WordTrace tailWord_2266261 prefixEnd_2266261 129297909059895886346129 := by
  unfold tailWord_2266261
  simp only [CollatzResearch.WordTrace]
  refine ⟨82657329242730918409558637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55104886161820612273039091 82657329242730918409558637)
  ·
    refine ⟨30996498466024094403584489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82657329242730918409558637 30996498466024094403584489)
    ·
      refine ⟨23247373849518070802688367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30996498466024094403584489 23247373849518070802688367)
      ·
        refine ⟨34871060774277106204032551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23247373849518070802688367 34871060774277106204032551)
        ·
          refine ⟨52306591161415659306048827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34871060774277106204032551 52306591161415659306048827)
          ·
            refine ⟨78459886742123488959073241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52306591161415659306048827 78459886742123488959073241)
            ·
              refine ⟨58844915056592616719304931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78459886742123488959073241 58844915056592616719304931)
              ·
                refine ⟨88267372584888925078957397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58844915056592616719304931 88267372584888925078957397)
                ·
                  refine ⟨129297909059895886346129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 88267372584888925078957397 129297909059895886346129)
                  ·
                    rfl

theorem cell23_2266261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 11].length) (baseStart_2266261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266261 prefixEnd_2266261 := by exact prefixLift 2266261
  have htrace : WordTrace (prefixWord ++ tailWord_2266261) baseStart_2266261 baseEnd_2266261 := by
    simpa [prefixWord, tailWord_2266261, baseEnd_2266261] using wordTrace_append hprefix tailTrace_2266261
  have hstable : (prefixWord ++ tailWord_2266261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266261).length < 2 ^ (prefixWord ++ tailWord_2266261).sum := by decide
  have hdescent : baseEnd_2266261 < baseStart_2266261 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266288 : List Nat := [2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 3]
def baseStart_2266288 : Nat := 118140960795 + 2266288 * 2 ^ 59
def prefixEnd_2266288 : Nat := 4983230072969 + 3 ^ 40 * 2266288 * 2
def baseEnd_2266288 : Nat := 1163695045516734371477537

theorem tailTrace_2266288 : CollatzResearch.WordTrace tailWord_2266288 prefixEnd_2266288 1163695045516734371477537 := by
  unfold tailWord_2266288
  simp only [CollatzResearch.WordTrace]
  refine ⟨41329157006816551010395759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55105542675755401347194345 41329157006816551010395759)
  ·
    refine ⟨61993735510224826515593639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41329157006816551010395759 61993735510224826515593639)
    ·
      refine ⟨92990603265337239773390459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61993735510224826515593639 92990603265337239773390459)
      ·
        refine ⟨139485904898005859660085689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 92990603265337239773390459 139485904898005859660085689)
        ·
          refine ⟨104614428673504394745064267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139485904898005859660085689 104614428673504394745064267)
          ·
            refine ⟨156921643010256592117596401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104614428673504394745064267 156921643010256592117596401)
            ·
              refine ⟨117691232257692444088197301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 156921643010256592117596401 117691232257692444088197301)
              ·
                refine ⟨11033553024158666633268497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 117691232257692444088197301 11033553024158666633268497)
                ·
                  refine ⟨8275164768118999974951373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11033553024158666633268497 8275164768118999974951373)
                  ·
                    refine ⟨3103186788044624990606765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8275164768118999974951373 3103186788044624990606765)
                    ·
                      refine ⟨1163695045516734371477537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3103186788044624990606765 1163695045516734371477537)
                      ·
                        rfl

theorem cell23_2266288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 5, 2, 3, 3].length) (baseStart_2266288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266288 prefixEnd_2266288 := by exact prefixLift 2266288
  have htrace : WordTrace (prefixWord ++ tailWord_2266288) baseStart_2266288 baseEnd_2266288 := by
    simpa [prefixWord, tailWord_2266288, baseEnd_2266288] using wordTrace_append hprefix tailTrace_2266288
  have hstable : (prefixWord ++ tailWord_2266288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266288).length < 2 ^ (prefixWord ++ tailWord_2266288).sum := by decide
  have hdescent : baseEnd_2266288 < baseStart_2266288 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266289 : List Nat := [1, 2, 2, 5, 1, 1, 2, 3, 2, 2, 2]
def baseStart_2266289 : Nat := 118140960795 + 2266289 * 2 ^ 59
def prefixEnd_2266289 : Nat := 4983230072969 + 3 ^ 40 * 2266289 * 2
def baseEnd_2266289 : Nat := 1163695558997388867565033

theorem tailTrace_2266289 : CollatzResearch.WordTrace tailWord_2266289 prefixEnd_2266289 1163695558997388867565033 := by
  unfold tailWord_2266289
  simp only [CollatzResearch.WordTrace]
  refine ⟨82658350486629479191577921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55105566991086319461051947 82658350486629479191577921)
  ·
    refine ⟨61993762864972109393683441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82658350486629479191577921 61993762864972109393683441)
    ·
      refine ⟨46495322148729082045262581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 61993762864972109393683441 46495322148729082045262581)
      ·
        refine ⟨4358936451443351441743367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46495322148729082045262581 4358936451443351441743367)
        ·
          refine ⟨6538404677165027162615051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4358936451443351441743367 6538404677165027162615051)
          ·
            refine ⟨9807607015747540743922577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6538404677165027162615051 9807607015747540743922577)
            ·
              refine ⟨7355705261810655557941933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9807607015747540743922577 7355705261810655557941933)
              ·
                refine ⟨2758389473178995834228225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7355705261810655557941933 2758389473178995834228225)
                ·
                  refine ⟨2068792104884246875671169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2758389473178995834228225 2068792104884246875671169)
                  ·
                    refine ⟨1551594078663185156753377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2068792104884246875671169 1551594078663185156753377)
                    ·
                      refine ⟨1163695558997388867565033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1551594078663185156753377 1163695558997388867565033)
                      ·
                        rfl

theorem cell23_2266289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_2266289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266289 prefixEnd_2266289 := by exact prefixLift 2266289
  have htrace : WordTrace (prefixWord ++ tailWord_2266289) baseStart_2266289 baseEnd_2266289 := by
    simpa [prefixWord, tailWord_2266289, baseEnd_2266289] using wordTrace_append hprefix tailTrace_2266289
  have hstable : (prefixWord ++ tailWord_2266289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266289).length < 2 ^ (prefixWord ++ tailWord_2266289).sum := by decide
  have hdescent : baseEnd_2266289 < baseStart_2266289 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266355 : List Nat := [1, 1, 1, 2, 2, 5, 2, 2, 3, 4]
def baseStart_2266355 : Nat := 118140960795 + 2266355 * 2 ^ 59
def prefixEnd_2266355 : Nat := 4983230072969 + 3 ^ 40 * 2266355 * 2
def baseEnd_2266355 : Nat := 387909816240195203113243

theorem tailTrace_2266355 : CollatzResearch.WordTrace tailWord_2266355 prefixEnd_2266355 387909816240195203113243 := by
  unfold tailWord_2266355
  simp only [CollatzResearch.WordTrace]
  refine ⟨82660757704390372463480519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55107171802926914975653679 82660757704390372463480519)
  ·
    refine ⟨123991136556585558695220779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82660757704390372463480519 123991136556585558695220779)
    ·
      refine ⟨185986704834878338042831169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 123991136556585558695220779 185986704834878338042831169)
      ·
        refine ⟨139490028626158753532123377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 185986704834878338042831169 139490028626158753532123377)
        ·
          refine ⟨104617521469619065149092533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139490028626158753532123377 104617521469619065149092533)
          ·
            refine ⟨9807892637776787357727425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 104617521469619065149092533 9807892637776787357727425)
            ·
              refine ⟨7355919478332590518295569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9807892637776787357727425 7355919478332590518295569)
              ·
                refine ⟨5516939608749442888721677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7355919478332590518295569 5516939608749442888721677)
                ·
                  refine ⟨2068852353281041083270629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5516939608749442888721677 2068852353281041083270629)
                  ·
                    refine ⟨387909816240195203113243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2068852353281041083270629 387909816240195203113243)
                    ·
                      rfl

theorem cell23_2266355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 2, 3, 4].length) (baseStart_2266355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266355 prefixEnd_2266355 := by exact prefixLift 2266355
  have htrace : WordTrace (prefixWord ++ tailWord_2266355) baseStart_2266355 baseEnd_2266355 := by
    simpa [prefixWord, tailWord_2266355, baseEnd_2266355] using wordTrace_append hprefix tailTrace_2266355
  have hstable : (prefixWord ++ tailWord_2266355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266355).length < 2 ^ (prefixWord ++ tailWord_2266355).sum := by decide
  have hdescent : baseEnd_2266355 < baseStart_2266355 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266382 : List Nat := [4, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3]
def baseStart_2266382 : Nat := 118140960795 + 2266382 * 2 ^ 59
def prefixEnd_2266382 : Nat := 4983230072969 + 3 ^ 40 * 2266382 * 2
def baseEnd_2266382 : Nat := 1163743312698257003702105

theorem tailTrace_2266382 : CollatzResearch.WordTrace tailWord_2266382 prefixEnd_2266382 1163743312698257003702105 := by
  unfold tailWord_2266382
  simp only [CollatzResearch.WordTrace]
  refine ⟨10332717809411569509339175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55107828316861704049808933 10332717809411569509339175)
  ·
    refine ⟨15499076714117354264008763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10332717809411569509339175 15499076714117354264008763)
    ·
      refine ⟨23248615071176031396013145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15499076714117354264008763 23248615071176031396013145)
      ·
        refine ⟨17436461303382023547009859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23248615071176031396013145 17436461303382023547009859)
        ·
          refine ⟨26154691955073035320514789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17436461303382023547009859 26154691955073035320514789)
          ·
            refine ⟨4904004741576194122596523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26154691955073035320514789 4904004741576194122596523)
            ·
              refine ⟨7356007112364291183894785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4904004741576194122596523 7356007112364291183894785)
              ·
                refine ⟨5517005334273218387921089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7356007112364291183894785 5517005334273218387921089)
                ·
                  refine ⟨4137754000704913790940817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5517005334273218387921089 4137754000704913790940817)
                  ·
                    refine ⟨3103315500528685343205613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4137754000704913790940817 3103315500528685343205613)
                    ·
                      refine ⟨1163743312698257003702105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3103315500528685343205613 1163743312698257003702105)
                      ·
                        rfl

theorem cell23_2266382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 2, 2, 2, 3].length) (baseStart_2266382 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266382 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266382 prefixEnd_2266382 := by exact prefixLift 2266382
  have htrace : WordTrace (prefixWord ++ tailWord_2266382) baseStart_2266382 baseEnd_2266382 := by
    simpa [prefixWord, tailWord_2266382, baseEnd_2266382] using wordTrace_append hprefix tailTrace_2266382
  have hstable : (prefixWord ++ tailWord_2266382).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266382).length < 2 ^ (prefixWord ++ tailWord_2266382).sum := by decide
  have hdescent : baseEnd_2266382 < baseStart_2266382 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266402 : List Nat := [3, 3, 1, 1, 4, 1, 1, 3, 6]
def baseStart_2266402 : Nat := 118140960795 + 2266402 * 2 ^ 59
def prefixEnd_2266402 : Nat := 4983230072969 + 3 ^ 40 * 2266402 * 2
def baseEnd_2266402 : Nat := 129305953590149658383557

theorem tailTrace_2266402 : CollatzResearch.WordTrace tailWord_2266402 prefixEnd_2266402 129305953590149658383557 := by
  unfold tailWord_2266402
  simp only [CollatzResearch.WordTrace]
  refine ⟨20665617983805024872610365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55108314623480066326960973 20665617983805024872610365)
  ·
    refine ⟨7749606743926884327228887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20665617983805024872610365 7749606743926884327228887)
    ·
      refine ⟨11624410115890326490843331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7749606743926884327228887 11624410115890326490843331)
      ·
        refine ⟨17436615173835489736264997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11624410115890326490843331 17436615173835489736264997)
        ·
          refine ⟨3269365345094154325549687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17436615173835489736264997 3269365345094154325549687)
          ·
            refine ⟨4904048017641231488324531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3269365345094154325549687 4904048017641231488324531)
            ·
              refine ⟨7356072026461847232486797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4904048017641231488324531 7356072026461847232486797)
              ·
                refine ⟨2758527009923192712182549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7356072026461847232486797 2758527009923192712182549)
                ·
                  refine ⟨129305953590149658383557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2758527009923192712182549 129305953590149658383557)
                  ·
                    rfl

theorem cell23_2266402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 3, 6].length) (baseStart_2266402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266402 prefixEnd_2266402 := by exact prefixLift 2266402
  have htrace : WordTrace (prefixWord ++ tailWord_2266402) baseStart_2266402 baseEnd_2266402 := by
    simpa [prefixWord, tailWord_2266402, baseEnd_2266402] using wordTrace_append hprefix tailTrace_2266402
  have hstable : (prefixWord ++ tailWord_2266402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266402).length < 2 ^ (prefixWord ++ tailWord_2266402).sum := by decide
  have hdescent : baseEnd_2266402 < baseStart_2266402 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266432 : List Nat := [2, 1, 1, 2, 2, 1, 7, 1, 1, 5]
def baseStart_2266432 : Nat := 118140960795 + 2266432 * 2 ^ 59
def prefixEnd_2266432 : Nat := 4983230072969 + 3 ^ 40 * 2266432 * 2
def baseEnd_2266432 : Nat := 387922995576993936025625

theorem tailTrace_2266432 : CollatzResearch.WordTrace tailWord_2266432 prefixEnd_2266432 387922995576993936025625 := by
  unfold tailWord_2266432
  simp only [CollatzResearch.WordTrace]
  refine ⟨41331783062555707307016775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55109044083407609742689033 41331783062555707307016775)
  ·
    refine ⟨61997674593833560960525163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41331783062555707307016775 61997674593833560960525163)
    ·
      refine ⟨92996511890750341440787745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61997674593833560960525163 92996511890750341440787745)
      ·
        refine ⟨69747383918062756080590809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 92996511890750341440787745 69747383918062756080590809)
        ·
          refine ⟨52310537938547067060443107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69747383918062756080590809 52310537938547067060443107)
          ·
            refine ⟨78465806907820600590664661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52310537938547067060443107 78465806907820600590664661)
            ·
              refine ⟨1839042349402045326343703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 78465806907820600590664661 1839042349402045326343703)
              ·
                refine ⟨2758563524103067989515555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1839042349402045326343703 2758563524103067989515555)
                ·
                  refine ⟨4137845286154601984273333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2758563524103067989515555 4137845286154601984273333)
                  ·
                    refine ⟨387922995576993936025625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4137845286154601984273333 387922995576993936025625)
                    ·
                      rfl

theorem cell23_2266432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 7, 1, 1, 5].length) (baseStart_2266432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266432 prefixEnd_2266432 := by exact prefixLift 2266432
  have htrace : WordTrace (prefixWord ++ tailWord_2266432) baseStart_2266432 baseEnd_2266432 := by
    simpa [prefixWord, tailWord_2266432, baseEnd_2266432] using wordTrace_append hprefix tailTrace_2266432
  have hstable : (prefixWord ++ tailWord_2266432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266432).length < 2 ^ (prefixWord ++ tailWord_2266432).sum := by decide
  have hdescent : baseEnd_2266432 < baseStart_2266432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266469 : List Nat := [1, 3, 1, 3, 1, 2, 3, 2, 3, 2, 2]
def baseStart_2266469 : Nat := 118140960795 + 2266469 * 2 ^ 59
def prefixEnd_2266469 : Nat := 4983230072969 + 3 ^ 40 * 2266469 * 2
def baseEnd_2266469 : Nat := 1163787985515198163314205

theorem tailTrace_2266469 : CollatzResearch.WordTrace tailWord_2266469 prefixEnd_2266469 1163787985515198163314205 := by
  unfold tailWord_2266469
  simp only [CollatzResearch.WordTrace]
  refine ⟨82664915625977369933130461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55109943750651579955420307 82664915625977369933130461)
  ·
    refine ⟨30999343359741513724923923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82664915625977369933130461 30999343359741513724923923)
    ·
      refine ⟨46499015039612270587385885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30999343359741513724923923 46499015039612270587385885)
      ·
        refine ⟨17437130639854601470269707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46499015039612270587385885 17437130639854601470269707)
        ·
          refine ⟨26155695959781902205404561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17437130639854601470269707 26155695959781902205404561)
          ·
            refine ⟨19616771969836426654053421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26155695959781902205404561 19616771969836426654053421)
            ·
              refine ⟨7356289488688659995270033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19616771969836426654053421 7356289488688659995270033)
              ·
                refine ⟨5517217116516494996452525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7356289488688659995270033 5517217116516494996452525)
                ·
                  refine ⟨2068956418693685623669697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5517217116516494996452525 2068956418693685623669697)
                  ·
                    refine ⟨1551717314020264217752273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2068956418693685623669697 1551717314020264217752273)
                    ·
                      refine ⟨1163787985515198163314205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1551717314020264217752273 1163787985515198163314205)
                      ·
                        rfl

theorem cell23_2266469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 3, 2, 3, 2, 2].length) (baseStart_2266469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266469 prefixEnd_2266469 := by exact prefixLift 2266469
  have htrace : WordTrace (prefixWord ++ tailWord_2266469) baseStart_2266469 baseEnd_2266469 := by
    simpa [prefixWord, tailWord_2266469, baseEnd_2266469] using wordTrace_append hprefix tailTrace_2266469
  have hstable : (prefixWord ++ tailWord_2266469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266469).length < 2 ^ (prefixWord ++ tailWord_2266469).sum := by decide
  have hdescent : baseEnd_2266469 < baseStart_2266469 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266489 : List Nat := [1, 2, 1, 3, 2, 1, 6, 1, 1, 2, 3]
def baseStart_2266489 : Nat := 118140960795 + 2266489 * 2 ^ 59
def prefixEnd_2266489 : Nat := 4983230072969 + 3 ^ 40 * 2266489 * 2
def baseEnd_2266489 : Nat := 1163798255128288085064113

theorem tailTrace_2266489 : CollatzResearch.WordTrace tailWord_2266489 prefixEnd_2266489 1163798255128288085064113 := by
  unfold tailWord_2266489
  simp only [CollatzResearch.WordTrace]
  refine ⟨82665645085904913348858521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55110430057269942232572347 82665645085904913348858521)
  ·
    refine ⟨61999233814428685011643891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82665645085904913348858521 61999233814428685011643891)
    ·
      refine ⟨92998850721643027517465837, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 61999233814428685011643891 92998850721643027517465837)
      ·
        refine ⟨34874569020616135319049689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 92998850721643027517465837 34874569020616135319049689)
        ·
          refine ⟨26155926765462101489287267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34874569020616135319049689 26155926765462101489287267)
          ·
            refine ⟨39233890148193152233930901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26155926765462101489287267 39233890148193152233930901)
            ·
              refine ⟨1839088600696554010965511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39233890148193152233930901 1839088600696554010965511)
              ·
                refine ⟨2758632901044831016448267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1839088600696554010965511 2758632901044831016448267)
                ·
                  refine ⟨4137949351567246524672401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2758632901044831016448267 4137949351567246524672401)
                  ·
                    refine ⟨3103462013675434893504301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4137949351567246524672401 3103462013675434893504301)
                    ·
                      refine ⟨1163798255128288085064113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3103462013675434893504301 1163798255128288085064113)
                      ·
                        rfl

theorem cell23_2266489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 6, 1, 1, 2, 3].length) (baseStart_2266489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266489 prefixEnd_2266489 := by exact prefixLift 2266489
  have htrace : WordTrace (prefixWord ++ tailWord_2266489) baseStart_2266489 baseEnd_2266489 := by
    simpa [prefixWord, tailWord_2266489, baseEnd_2266489] using wordTrace_append hprefix tailTrace_2266489
  have hstable : (prefixWord ++ tailWord_2266489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266489).length < 2 ^ (prefixWord ++ tailWord_2266489).sum := by decide
  have hdescent : baseEnd_2266489 < baseStart_2266489 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266526 : List Nat := [4, 3, 1, 2, 2, 2, 2, 7]
def baseStart_2266526 : Nat := 118140960795 + 2266526 * 2 ^ 59
def prefixEnd_2266526 : Nat := 4983230072969 + 3 ^ 40 * 2266526 * 2
def baseEnd_2266526 : Nat := 43104342737500164455609

theorem tailTrace_2266526 : CollatzResearch.WordTrace tailWord_2266526 prefixEnd_2266526 43104342737500164455609 := by
  unfold tailWord_2266526
  simp only [CollatzResearch.WordTrace]
  refine ⟨10333374323346358583494429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55111329724513912445303621 10333374323346358583494429)
  ·
    refine ⟨3875015371254884468810411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10333374323346358583494429 3875015371254884468810411)
    ·
      refine ⟨5812523056882326703215617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3875015371254884468810411 5812523056882326703215617)
      ·
        refine ⟨4359392292661745027411713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5812523056882326703215617 4359392292661745027411713)
        ·
          refine ⟨3269544219496308770558785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4359392292661745027411713 3269544219496308770558785)
          ·
            refine ⟨2452158164622231577919089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3269544219496308770558785 2452158164622231577919089)
            ·
              refine ⟨1839118623466673683439317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2452158164622231577919089 1839118623466673683439317)
              ·
                refine ⟨43104342737500164455609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1839118623466673683439317 43104342737500164455609)
                ·
                  rfl

theorem cell23_2266526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 7].length) (baseStart_2266526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266526 prefixEnd_2266526 := by exact prefixLift 2266526
  have htrace : WordTrace (prefixWord ++ tailWord_2266526) baseStart_2266526 baseEnd_2266526 := by
    simpa [prefixWord, tailWord_2266526, baseEnd_2266526] using wordTrace_append hprefix tailTrace_2266526
  have hstable : (prefixWord ++ tailWord_2266526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266526).length < 2 ^ (prefixWord ++ tailWord_2266526).sum := by decide
  have hdescent : baseEnd_2266526 < baseStart_2266526 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266580 : List Nat := [2, 4, 1, 2, 4, 1, 1, 2, 1, 3, 2]
def baseStart_2266580 : Nat := 118140960795 + 2266580 * 2 ^ 59
def prefixEnd_2266580 : Nat := 4983230072969 + 3 ^ 40 * 2266580 * 2
def baseEnd_2266580 : Nat := 1163844981867847229026195

theorem tailTrace_2266580 : CollatzResearch.WordTrace tailWord_2266580 prefixEnd_2266580 1163844981867847229026195 := by
  unfold tailWord_2266580
  simp only [CollatzResearch.WordTrace]
  refine ⟨41334482064287617945210597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55112642752383490593614129 41334482064287617945210597)
  ·
    refine ⟨7750215387053928364726987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41334482064287617945210597 7750215387053928364726987)
    ·
      refine ⟨11625323080580892547090481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7750215387053928364726987 11625323080580892547090481)
      ·
        refine ⟨8718992310435669410317861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11625323080580892547090481 8718992310435669410317861)
        ·
          refine ⟨1634811058206688014434599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8718992310435669410317861 1634811058206688014434599)
          ·
            refine ⟨2452216587310032021651899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1634811058206688014434599 2452216587310032021651899)
            ·
              refine ⟨3678324880965048032477849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2452216587310032021651899 3678324880965048032477849)
              ·
                refine ⟨2758743660723786024358387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3678324880965048032477849 2758743660723786024358387)
                ·
                  refine ⟨4138115491085679036537581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2758743660723786024358387 4138115491085679036537581)
                  ·
                    refine ⟨1551793309157129638701593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4138115491085679036537581 1551793309157129638701593)
                    ·
                      refine ⟨1163844981867847229026195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1551793309157129638701593 1163844981867847229026195)
                      ·
                        rfl

theorem cell23_2266580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 4, 1, 1, 2, 1, 3, 2].length) (baseStart_2266580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266580 prefixEnd_2266580 := by exact prefixLift 2266580
  have htrace : WordTrace (prefixWord ++ tailWord_2266580) baseStart_2266580 baseEnd_2266580 := by
    simpa [prefixWord, tailWord_2266580, baseEnd_2266580] using wordTrace_append hprefix tailTrace_2266580
  have hstable : (prefixWord ++ tailWord_2266580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266580).length < 2 ^ (prefixWord ++ tailWord_2266580).sum := by decide
  have hdescent : baseEnd_2266580 < baseStart_2266580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266616 : List Nat := [2, 1, 2, 1, 1, 7, 2, 2, 5]
def baseStart_2266616 : Nat := 118140960795 + 2266616 * 2 ^ 59
def prefixEnd_2266616 : Nat := 4983230072969 + 3 ^ 40 * 2266616 * 2
def baseEnd_2266616 : Nat := 129318163019045454241781

theorem tailTrace_2266616 : CollatzResearch.WordTrace tailWord_2266616 prefixEnd_2266616 129318163019045454241781 := by
  unfold tailWord_2266616
  simp only [CollatzResearch.WordTrace]
  refine ⟨41335138578222407019365851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55113518104296542692487801 41335138578222407019365851)
  ·
    refine ⟨62002707867333610529048777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41335138578222407019365851 62002707867333610529048777)
    ·
      refine ⟨46502030900500207896786583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62002707867333610529048777 46502030900500207896786583)
      ·
        refine ⟨69753046350750311845179875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46502030900500207896786583 69753046350750311845179875)
        ·
          refine ⟨104629569526125467767769813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69753046350750311845179875 104629569526125467767769813)
          ·
            refine ⟨2452255535768565650807105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 104629569526125467767769813 2452255535768565650807105)
            ·
              refine ⟨1839191651826424238105329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2452255535768565650807105 1839191651826424238105329)
              ·
                refine ⟨1379393738869818178578997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1839191651826424238105329 1379393738869818178578997)
                ·
                  refine ⟨129318163019045454241781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1379393738869818178578997 129318163019045454241781)
                  ·
                    rfl

theorem cell23_2266616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 7, 2, 2, 5].length) (baseStart_2266616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266616 prefixEnd_2266616 := by exact prefixLift 2266616
  have htrace : WordTrace (prefixWord ++ tailWord_2266616) baseStart_2266616 baseEnd_2266616 := by
    simpa [prefixWord, tailWord_2266616, baseEnd_2266616] using wordTrace_append hprefix tailTrace_2266616
  have hstable : (prefixWord ++ tailWord_2266616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266616).length < 2 ^ (prefixWord ++ tailWord_2266616).sum := by decide
  have hdescent : baseEnd_2266616 < baseStart_2266616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266626 : List Nat := [3, 4, 1, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_2266626 : Nat := 118140960795 + 2266626 * 2 ^ 59
def prefixEnd_2266626 : Nat := 4983230072969 + 3 ^ 40 * 2266626 * 2
def baseEnd_2266626 : Nat := 1163868601977954049050983

theorem tailTrace_2266626 : CollatzResearch.WordTrace tailWord_2266626 prefixEnd_2266626 1163868601977954049050983 := by
  unfold tailWord_2266626
  simp only [CollatzResearch.WordTrace]
  refine ⟨20667660471602146436648933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55113761257605723831063821 20667660471602146436648933)
  ·
    refine ⟨3875186338425402456871675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20667660471602146436648933 3875186338425402456871675)
    ·
      refine ⟨5812779507638103685307513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3875186338425402456871675 5812779507638103685307513)
      ·
        refine ⟨4359584630728577763980635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5812779507638103685307513 4359584630728577763980635)
        ·
          refine ⟨6539376946092866645970953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4359584630728577763980635 6539376946092866645970953)
          ·
            refine ⟨4904532709569649984478215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6539376946092866645970953 4904532709569649984478215)
            ·
              refine ⟨7356799064354474976717323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4904532709569649984478215 7356799064354474976717323)
              ·
                refine ⟨11035198596531712465075985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7356799064354474976717323 11035198596531712465075985)
                ·
                  refine ⟨8276398947398784348806989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11035198596531712465075985 8276398947398784348806989)
                  ·
                    refine ⟨3103649605274544130802621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8276398947398784348806989 3103649605274544130802621)
                    ·
                      refine ⟨1163868601977954049050983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3103649605274544130802621 1163868601977954049050983)
                      ·
                        rfl

theorem cell23_2266626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_2266626 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266626 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266626 prefixEnd_2266626 := by exact prefixLift 2266626
  have htrace : WordTrace (prefixWord ++ tailWord_2266626) baseStart_2266626 baseEnd_2266626 := by
    simpa [prefixWord, tailWord_2266626, baseEnd_2266626] using wordTrace_append hprefix tailTrace_2266626
  have hstable : (prefixWord ++ tailWord_2266626).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266626).length < 2 ^ (prefixWord ++ tailWord_2266626).sum := by decide
  have hdescent : baseEnd_2266626 < baseStart_2266626 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266632 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 4, 1, 4]
def baseStart_2266632 : Nat := 118140960795 + 2266632 * 2 ^ 59
def prefixEnd_2266632 : Nat := 4983230072969 + 3 ^ 40 * 2266632 * 2
def baseEnd_2266632 : Nat := 1163871682861881025575955

theorem tailTrace_2266632 : CollatzResearch.WordTrace tailWord_2266632 prefixEnd_2266632 1163871682861881025575955 := by
  unfold tailWord_2266632
  simp only [CollatzResearch.WordTrace]
  refine ⟨41335430362193424385657075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55113907149591232514209433 41335430362193424385657075)
  ·
    refine ⟨62003145543290136578485613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41335430362193424385657075 62003145543290136578485613)
    ·
      refine ⟨23251179578733801216932105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62003145543290136578485613 23251179578733801216932105)
      ·
        refine ⟨17438384684050350912699079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23251179578733801216932105 17438384684050350912699079)
        ·
          refine ⟨26157577026075526369048619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17438384684050350912699079 26157577026075526369048619)
          ·
            refine ⟨39236365539113289553572929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26157577026075526369048619 39236365539113289553572929)
            ·
              refine ⟨29427274154334967165179697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39236365539113289553572929 29427274154334967165179697)
              ·
                refine ⟨22070455615751225373884773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29427274154334967165179697 22070455615751225373884773)
                ·
                  refine ⟨4138210427953354757603395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22070455615751225373884773 4138210427953354757603395)
                  ·
                    refine ⟨6207315641930032136405093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4138210427953354757603395 6207315641930032136405093)
                    ·
                      refine ⟨1163871682861881025575955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6207315641930032136405093 1163871682861881025575955)
                      ·
                        rfl

theorem cell23_2266632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_2266632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266632 prefixEnd_2266632 := by exact prefixLift 2266632
  have htrace : WordTrace (prefixWord ++ tailWord_2266632) baseStart_2266632 baseEnd_2266632 := by
    simpa [prefixWord, tailWord_2266632, baseEnd_2266632] using wordTrace_append hprefix tailTrace_2266632
  have hstable : (prefixWord ++ tailWord_2266632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266632).length < 2 ^ (prefixWord ++ tailWord_2266632).sum := by decide
  have hdescent : baseEnd_2266632 < baseStart_2266632 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266665 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 7]
def baseStart_2266665 : Nat := 118140960795 + 2266665 * 2 ^ 59
def prefixEnd_2266665 : Nat := 4983230072969 + 3 ^ 40 * 2266665 * 2
def baseEnd_2266665 : Nat := 1163888627723479396463303

theorem tailTrace_2266665 : CollatzResearch.WordTrace tailWord_2266665 prefixEnd_2266665 1163888627723479396463303 := by
  unfold tailWord_2266665
  simp only [CollatzResearch.WordTrace]
  refine ⟨82672064333267295407265449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55114709555511530271510299 82672064333267295407265449)
  ·
    refine ⟨62004048249950471555449087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82672064333267295407265449 62004048249950471555449087)
    ·
      refine ⟨93006072374925707333173631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62004048249950471555449087 93006072374925707333173631)
      ·
        refine ⟨139509108562388560999760447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93006072374925707333173631 139509108562388560999760447)
        ·
          refine ⟨209263662843582841499640671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139509108562388560999760447 209263662843582841499640671)
          ·
            refine ⟨313895494265374262249461007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209263662843582841499640671 313895494265374262249461007)
            ·
              refine ⟨470843241398061393374191511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 313895494265374262249461007 470843241398061393374191511)
              ·
                refine ⟨706264862097092090061287267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 470843241398061393374191511 706264862097092090061287267)
                ·
                  refine ⟨1059397293145638135091930901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 706264862097092090061287267 1059397293145638135091930901)
                  ·
                    refine ⟨49659248116201787582434261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1059397293145638135091930901 49659248116201787582434261)
                    ·
                      refine ⟨1163888627723479396463303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49659248116201787582434261 1163888627723479396463303)
                      ·
                        rfl

theorem cell23_2266665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 6, 7].length) (baseStart_2266665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266665 prefixEnd_2266665 := by exact prefixLift 2266665
  have htrace : WordTrace (prefixWord ++ tailWord_2266665) baseStart_2266665 baseEnd_2266665 := by
    simpa [prefixWord, tailWord_2266665, baseEnd_2266665] using wordTrace_append hprefix tailTrace_2266665
  have hstable : (prefixWord ++ tailWord_2266665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266665).length < 2 ^ (prefixWord ++ tailWord_2266665).sum := by decide
  have hdescent : baseEnd_2266665 < baseStart_2266665 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266752 : List Nat := [2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 6]
def baseStart_2266752 : Nat := 118140960795 + 2266752 * 2 ^ 59
def prefixEnd_2266752 : Nat := 4983230072969 + 3 ^ 40 * 2266752 * 2
def baseEnd_2266752 : Nat := 1163933300540420556075403

theorem tailTrace_2266752 : CollatzResearch.WordTrace tailWord_2266752 prefixEnd_2266752 1163933300540420556075403 := by
  unfold tailWord_2266752
  simp only [CollatzResearch.WordTrace]
  refine ⟨41337618741976054632841255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55116824989301406177121673 41337618741976054632841255)
  ·
    refine ⟨62006428112964081949261883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41337618741976054632841255 62006428112964081949261883)
    ·
      refine ⟨93009642169446122923892825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62006428112964081949261883 93009642169446122923892825)
      ·
        refine ⟨69757231627084592192919619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93009642169446122923892825 69757231627084592192919619)
        ·
          refine ⟨104635847440626888289379429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69757231627084592192919619 104635847440626888289379429)
          ·
            refine ⟨19619221395117541554258643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104635847440626888289379429 19619221395117541554258643)
            ·
              refine ⟨29428832092676312331387965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19619221395117541554258643 29428832092676312331387965)
              ·
                refine ⟨11035812034753617124270487, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29428832092676312331387965 11035812034753617124270487)
                ·
                  refine ⟨16553718052130425686405731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11035812034753617124270487 16553718052130425686405731)
                  ·
                    refine ⟨24830577078195638529608597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16553718052130425686405731 24830577078195638529608597)
                    ·
                      refine ⟨1163933300540420556075403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24830577078195638529608597 1163933300540420556075403)
                      ·
                        rfl

theorem cell23_2266752_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 1, 1, 6].length) (baseStart_2266752 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266752 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266752 prefixEnd_2266752 := by exact prefixLift 2266752
  have htrace : WordTrace (prefixWord ++ tailWord_2266752) baseStart_2266752 baseEnd_2266752 := by
    simpa [prefixWord, tailWord_2266752, baseEnd_2266752] using wordTrace_append hprefix tailTrace_2266752
  have hstable : (prefixWord ++ tailWord_2266752).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266752).length < 2 ^ (prefixWord ++ tailWord_2266752).sum := by decide
  have hdescent : baseEnd_2266752 < baseStart_2266752 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266752) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266756 : List Nat := [2, 3, 2, 1, 4, 1, 1, 1, 3, 1, 4]
def baseStart_2266756 : Nat := 118140960795 + 2266756 * 2 ^ 59
def prefixEnd_2266756 : Nat := 4983230072969 + 3 ^ 40 * 2266756 * 2
def baseEnd_2266756 : Nat := 1163935354463038540425385

theorem tailTrace_2266756 : CollatzResearch.WordTrace tailWord_2266756 prefixEnd_2266756 1163935354463038540425385 := by
  unfold tailWord_2266756
  simp only [CollatzResearch.WordTrace]
  refine ⟨41337691687968808974414061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55116922250625078632552081 41337691687968808974414061)
  ·
    refine ⟨15501634382988303365405273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41337691687968808974414061 15501634382988303365405273)
    ·
      refine ⟨11626225787241227524053955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15501634382988303365405273 11626225787241227524053955)
      ·
        refine ⟨17439338680861841286080933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11626225787241227524053955 17439338680861841286080933)
        ·
          refine ⟨3269876002661595241140175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17439338680861841286080933 3269876002661595241140175)
          ·
            refine ⟨4904814003992392861710263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3269876002661595241140175 4904814003992392861710263)
            ·
              refine ⟨7357221005988589292565395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4904814003992392861710263 7357221005988589292565395)
              ·
                refine ⟨11035831508982883938848093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7357221005988589292565395 11035831508982883938848093)
                ·
                  refine ⟨4138436815868581477068035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11035831508982883938848093 4138436815868581477068035)
                  ·
                    refine ⟨6207655223802872215602053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4138436815868581477068035 6207655223802872215602053)
                    ·
                      refine ⟨1163935354463038540425385, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6207655223802872215602053 1163935354463038540425385)
                      ·
                        rfl

theorem cell23_2266756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 3, 1, 4].length) (baseStart_2266756 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266756 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266756 prefixEnd_2266756 := by exact prefixLift 2266756
  have htrace : WordTrace (prefixWord ++ tailWord_2266756) baseStart_2266756 baseEnd_2266756 := by
    simpa [prefixWord, tailWord_2266756, baseEnd_2266756] using wordTrace_append hprefix tailTrace_2266756
  have hstable : (prefixWord ++ tailWord_2266756).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266756).length < 2 ^ (prefixWord ++ tailWord_2266756).sum := by decide
  have hdescent : baseEnd_2266756 < baseStart_2266756 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266760 : List Nat := [2, 1, 3, 5, 1, 1, 2, 1, 2, 3, 2]
def baseStart_2266760 : Nat := 118140960795 + 2266760 * 2 ^ 59
def prefixEnd_2266760 : Nat := 4983230072969 + 3 ^ 40 * 2266760 * 2
def baseEnd_2266760 : Nat := 1163937408385656524775367

theorem tailTrace_2266760 : CollatzResearch.WordTrace tailWord_2266760 prefixEnd_2266760 1163937408385656524775367 := by
  unfold tailWord_2266760
  simp only [CollatzResearch.WordTrace]
  refine ⟨41337764633961563315986867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55117019511948751087982489 41337764633961563315986867)
  ·
    refine ⟨62006646950942344973980301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41337764633961563315986867 62006646950942344973980301)
    ·
      refine ⟨23252492606603379365242613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62006646950942344973980301 23252492606603379365242613)
      ·
        refine ⟨2179921181869066815491495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23252492606603379365242613 2179921181869066815491495)
        ·
          refine ⟨3269881772803600223237243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2179921181869066815491495 3269881772803600223237243)
          ·
            refine ⟨4904822659205400334855865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3269881772803600223237243 4904822659205400334855865)
            ·
              refine ⟨3678616994404050251141899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4904822659205400334855865 3678616994404050251141899)
              ·
                refine ⟨5517925491606075376712849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3678616994404050251141899 5517925491606075376712849)
                ·
                  refine ⟨4138444118704556532534637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5517925491606075376712849 4138444118704556532534637)
                  ·
                    refine ⟨1551916544514208699700489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4138444118704556532534637 1551916544514208699700489)
                    ·
                      refine ⟨1163937408385656524775367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1551916544514208699700489 1163937408385656524775367)
                      ·
                        rfl

theorem cell23_2266760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_2266760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266760 prefixEnd_2266760 := by exact prefixLift 2266760
  have htrace : WordTrace (prefixWord ++ tailWord_2266760) baseStart_2266760 baseEnd_2266760 := by
    simpa [prefixWord, tailWord_2266760, baseEnd_2266760] using wordTrace_append hprefix tailTrace_2266760
  have hstable : (prefixWord ++ tailWord_2266760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266760).length < 2 ^ (prefixWord ++ tailWord_2266760).sum := by decide
  have hdescent : baseEnd_2266760 < baseStart_2266760 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266776 : List Nat := [2, 1, 2, 4, 1, 4, 1, 1, 1, 1, 5]
def baseStart_2266776 : Nat := 118140960795 + 2266776 * 2 ^ 59
def prefixEnd_2266776 : Nat := 4983230072969 + 3 ^ 40 * 2266776 * 2
def baseEnd_2266776 : Nat := 1163945624076128462175293

theorem tailTrace_2266776 : CollatzResearch.WordTrace tailWord_2266776 prefixEnd_2266776 1163945624076128462175293 := by
  unfold tailWord_2266776
  simp only [CollatzResearch.WordTrace]
  refine ⟨41338056417932580682278091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55117408557243440909704121 41338056417932580682278091)
  ·
    refine ⟨62007084626898871023417137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41338056417932580682278091 62007084626898871023417137)
    ·
      refine ⟨46505313470174153267562853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62007084626898871023417137 46505313470174153267562853)
      ·
        refine ⟨8719746275657653737668035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46505313470174153267562853 8719746275657653737668035)
        ·
          refine ⟨13079619413486480606502053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8719746275657653737668035 13079619413486480606502053)
          ·
            refine ⟨2452428640028715113719135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13079619413486480606502053 2452428640028715113719135)
            ·
              refine ⟨3678642960043072670578703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2452428640028715113719135 3678642960043072670578703)
              ·
                refine ⟨5517964440064609005868055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3678642960043072670578703 5517964440064609005868055)
                ·
                  refine ⟨8276946660096913508802083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5517964440064609005868055 8276946660096913508802083)
                  ·
                    refine ⟨12415419990145370263203125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8276946660096913508802083 12415419990145370263203125)
                    ·
                      refine ⟨1163945624076128462175293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12415419990145370263203125 1163945624076128462175293)
                      ·
                        rfl

theorem cell23_2266776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 4, 1, 1, 1, 1, 5].length) (baseStart_2266776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266776 prefixEnd_2266776 := by exact prefixLift 2266776
  have htrace : WordTrace (prefixWord ++ tailWord_2266776) baseStart_2266776 baseEnd_2266776 := by
    simpa [prefixWord, tailWord_2266776, baseEnd_2266776] using wordTrace_append hprefix tailTrace_2266776
  have hstable : (prefixWord ++ tailWord_2266776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266776).length < 2 ^ (prefixWord ++ tailWord_2266776).sum := by decide
  have hdescent : baseEnd_2266776 < baseStart_2266776 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266816 : List Nat := [2, 1, 1, 2, 4, 1, 1, 3, 3, 3, 2]
def baseStart_2266816 : Nat := 118140960795 + 2266816 * 2 ^ 59
def prefixEnd_2266816 : Nat := 4983230072969 + 3 ^ 40 * 2266816 * 2
def baseEnd_2266816 : Nat := 1163966163302308305675109

theorem tailTrace_2266816 : CollatzResearch.WordTrace tailWord_2266816 prefixEnd_2266816 1163966163302308305675109 := by
  unfold tailWord_2266816
  simp only [CollatzResearch.WordTrace]
  refine ⟨41338785877860124098006151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55118381170480165464008201 41338785877860124098006151)
  ·
    refine ⟨62008178816790186147009227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41338785877860124098006151 62008178816790186147009227)
    ·
      refine ⟨93012268225185279220513841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62008178816790186147009227 93012268225185279220513841)
      ·
        refine ⟨69759201168888959415385381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93012268225185279220513841 69759201168888959415385381)
        ·
          refine ⟨13079850219166679890384759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 69759201168888959415385381 13079850219166679890384759)
          ·
            refine ⟨19619775328750019835577139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13079850219166679890384759 19619775328750019835577139)
            ·
              refine ⟨29429662993125029753365709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19619775328750019835577139 29429662993125029753365709)
              ·
                refine ⟨11036123622421886157512141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29429662993125029753365709 11036123622421886157512141)
                ·
                  refine ⟨4138546358408207309067053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11036123622421886157512141 4138546358408207309067053)
                  ·
                    refine ⟨1551954884403077740900145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4138546358408207309067053 1551954884403077740900145)
                    ·
                      refine ⟨1163966163302308305675109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1551954884403077740900145 1163966163302308305675109)
                      ·
                        rfl

theorem cell23_2266816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 3, 3, 3, 2].length) (baseStart_2266816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266816 prefixEnd_2266816 := by exact prefixLift 2266816
  have htrace : WordTrace (prefixWord ++ tailWord_2266816) baseStart_2266816 baseEnd_2266816 := by
    simpa [prefixWord, tailWord_2266816, baseEnd_2266816] using wordTrace_append hprefix tailTrace_2266816
  have hstable : (prefixWord ++ tailWord_2266816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266816).length < 2 ^ (prefixWord ++ tailWord_2266816).sum := by decide
  have hdescent : baseEnd_2266816 < baseStart_2266816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266833 : List Nat := [1, 2, 2, 1, 2, 5, 1, 3, 1, 3, 2]
def baseStart_2266833 : Nat := 118140960795 + 2266833 * 2 ^ 59
def prefixEnd_2266833 : Nat := 4983230072969 + 3 ^ 40 * 2266833 * 2
def baseEnd_2266833 : Nat := 1163974892473434739162531

theorem tailTrace_2266833 : CollatzResearch.WordTrace tailWord_2266833 prefixEnd_2266833 1163974892473434739162531 := by
  unfold tailWord_2266833
  simp only [CollatzResearch.WordTrace]
  refine ⟨82678191796658660099381153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55118794531105773399587435 82678191796658660099381153)
  ·
    refine ⟨62008643847493995074535865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82678191796658660099381153 62008643847493995074535865)
    ·
      refine ⟨46506482885620496305901899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62008643847493995074535865 46506482885620496305901899)
      ·
        refine ⟨69759724328430744458852849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46506482885620496305901899 69759724328430744458852849)
        ·
          refine ⟨52319793246323058344139637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69759724328430744458852849 52319793246323058344139637)
          ·
            refine ⟨4904980616842786719763091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52319793246323058344139637 4904980616842786719763091)
            ·
              refine ⟨7357470925264180079644637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4904980616842786719763091 7357470925264180079644637)
              ·
                refine ⟨2759051596974067529866739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7357470925264180079644637 2759051596974067529866739)
                ·
                  refine ⟨4138577395461101294800109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2759051596974067529866739 4138577395461101294800109)
                  ·
                    refine ⟨1551966523297912985550041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4138577395461101294800109 1551966523297912985550041)
                    ·
                      refine ⟨1163974892473434739162531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1551966523297912985550041 1163974892473434739162531)
                      ·
                        rfl

theorem cell23_2266833_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 1, 3, 1, 3, 2].length) (baseStart_2266833 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266833 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266833 prefixEnd_2266833 := by exact prefixLift 2266833
  have htrace : WordTrace (prefixWord ++ tailWord_2266833) baseStart_2266833 baseEnd_2266833 := by
    simpa [prefixWord, tailWord_2266833, baseEnd_2266833] using wordTrace_append hprefix tailTrace_2266833
  have hstable : (prefixWord ++ tailWord_2266833).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266833).length < 2 ^ (prefixWord ++ tailWord_2266833).sum := by decide
  have hdescent : baseEnd_2266833 < baseStart_2266833 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266833) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266859 : List Nat := [1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 4]
def baseStart_2266859 : Nat := 118140960795 + 2266859 * 2 ^ 59
def prefixEnd_2266859 : Nat := 4983230072969 + 3 ^ 40 * 2266859 * 2
def baseEnd_2266859 : Nat := 1163988242970451637437411

theorem tailTrace_2266859 : CollatzResearch.WordTrace tailWord_2266859 prefixEnd_2266859 1163988242970451637437411 := by
  unfold tailWord_2266859
  simp only [CollatzResearch.WordTrace]
  refine ⟨82679140094564466539827631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55119426729709644359885087 82679140094564466539827631)
  ·
    refine ⟨124018710141846699809741447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82679140094564466539827631 124018710141846699809741447)
    ·
      refine ⟨186028065212770049714612171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124018710141846699809741447 186028065212770049714612171)
      ·
        refine ⟨279042097819155074571918257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186028065212770049714612171 279042097819155074571918257)
        ·
          refine ⟨209281573364366305928938693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279042097819155074571918257 209281573364366305928938693)
          ·
            refine ⟨39240295005818682361676005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 209281573364366305928938693 39240295005818682361676005)
            ·
              refine ⟨7357555313591002942814251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39240295005818682361676005 7357555313591002942814251)
              ·
                refine ⟨11036332970386504414221377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7357555313591002942814251 11036332970386504414221377)
                ·
                  refine ⟨8277249727789878310666033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11036332970386504414221377 8277249727789878310666033)
                  ·
                    refine ⟨6207937295842408732999525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8277249727789878310666033 6207937295842408732999525)
                    ·
                      refine ⟨1163988242970451637437411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6207937295842408732999525 1163988242970451637437411)
                      ·
                        rfl

theorem cell23_2266859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 4].length) (baseStart_2266859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266859 prefixEnd_2266859 := by exact prefixLift 2266859
  have htrace : WordTrace (prefixWord ++ tailWord_2266859) baseStart_2266859 baseEnd_2266859 := by
    simpa [prefixWord, tailWord_2266859, baseEnd_2266859] using wordTrace_append hprefix tailTrace_2266859
  have hstable : (prefixWord ++ tailWord_2266859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266859).length < 2 ^ (prefixWord ++ tailWord_2266859).sum := by decide
  have hdescent : baseEnd_2266859 < baseStart_2266859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266879 : List Nat := [1, 1, 2, 2, 1, 3, 2, 2, 1, 5, 3]
def baseStart_2266879 : Nat := 118140960795 + 2266879 * 2 ^ 59
def prefixEnd_2266879 : Nat := 4983230072969 + 3 ^ 40 * 2266879 * 2
def baseEnd_2266879 : Nat := 1163998512583541559187319

theorem tailTrace_2266879 : CollatzResearch.WordTrace tailWord_2266879 prefixEnd_2266879 1163998512583541559187319 := by
  unfold tailWord_2266879
  simp only [CollatzResearch.WordTrace]
  refine ⟨82679869554492009955555691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55119913036328006637037127 82679869554492009955555691)
  ·
    refine ⟨124019804331738014933333537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82679869554492009955555691 124019804331738014933333537)
    ·
      refine ⟨93014853248803511200000153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124019804331738014933333537 93014853248803511200000153)
      ·
        refine ⟨69761139936602633400000115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93014853248803511200000153 69761139936602633400000115)
        ·
          refine ⟨104641709904903950100000173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69761139936602633400000115 104641709904903950100000173)
          ·
            refine ⟨39240641214338981287500065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104641709904903950100000173 39240641214338981287500065)
            ·
              refine ⟨29430480910754235965625049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39240641214338981287500065 29430480910754235965625049)
              ·
                refine ⟨22072860683065676974218787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29430480910754235965625049 22072860683065676974218787)
                ·
                  refine ⟨33109291024598515461328181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22072860683065676974218787 33109291024598515461328181)
                  ·
                    refine ⟨3103996033556110824499517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 33109291024598515461328181 3103996033556110824499517)
                    ·
                      refine ⟨1163998512583541559187319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3103996033556110824499517 1163998512583541559187319)
                      ·
                        rfl

theorem cell23_2266879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5, 3].length) (baseStart_2266879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266879 prefixEnd_2266879 := by exact prefixLift 2266879
  have htrace : WordTrace (prefixWord ++ tailWord_2266879) baseStart_2266879 baseEnd_2266879 := by
    simpa [prefixWord, tailWord_2266879, baseEnd_2266879] using wordTrace_append hprefix tailTrace_2266879
  have hstable : (prefixWord ++ tailWord_2266879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266879).length < 2 ^ (prefixWord ++ tailWord_2266879).sum := by decide
  have hdescent : baseEnd_2266879 < baseStart_2266879 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266933 : List Nat := [1, 3, 3, 1, 4, 1, 2, 1, 2, 5]
def baseStart_2266933 : Nat := 118140960795 + 2266933 * 2 ^ 59
def prefixEnd_2266933 : Nat := 4983230072969 + 3 ^ 40 * 2266933 * 2
def baseEnd_2266933 : Nat := 388008746846294782637357

theorem tailTrace_2266933 : CollatzResearch.WordTrace tailWord_2266933 prefixEnd_2266933 388008746846294782637357 := by
  unfold tailWord_2266933
  simp only [CollatzResearch.WordTrace]
  refine ⟨82681839096296377178021453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55121226064197584785347635 82681839096296377178021453)
  ·
    refine ⟨31005689661111141441758045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82681839096296377178021453 31005689661111141441758045)
    ·
      refine ⟨11627133622916678040659267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31005689661111141441758045 11627133622916678040659267)
      ·
        refine ⟨17440700434375017060988901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11627133622916678040659267 17440700434375017060988901)
        ·
          refine ⟨3270131331445315698935419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17440700434375017060988901 3270131331445315698935419)
          ·
            refine ⟨4905196997167973548403129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3270131331445315698935419 4905196997167973548403129)
            ·
              refine ⟨3678897747875980161302347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4905196997167973548403129 3678897747875980161302347)
              ·
                refine ⟨5518346621813970241953521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3678897747875980161302347 5518346621813970241953521)
                ·
                  refine ⟨4138759966360477681465141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5518346621813970241953521 4138759966360477681465141)
                  ·
                    refine ⟨388008746846294782637357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4138759966360477681465141 388008746846294782637357)
                    ·
                      rfl

theorem cell23_2266933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 2, 1, 2, 5].length) (baseStart_2266933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266933 prefixEnd_2266933 := by exact prefixLift 2266933
  have htrace : WordTrace (prefixWord ++ tailWord_2266933) baseStart_2266933 baseEnd_2266933 := by
    simpa [prefixWord, tailWord_2266933, baseEnd_2266933] using wordTrace_append hprefix tailTrace_2266933
  have hstable : (prefixWord ++ tailWord_2266933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266933).length < 2 ^ (prefixWord ++ tailWord_2266933).sum := by decide
  have hdescent : baseEnd_2266933 < baseStart_2266933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266936 : List Nat := [2, 1, 2, 1, 3, 3, 1, 3, 2, 1, 4]
def baseStart_2266936 : Nat := 118140960795 + 2266936 * 2 ^ 59
def prefixEnd_2266936 : Nat := 4983230072969 + 3 ^ 40 * 2266936 * 2
def baseEnd_2266936 : Nat := 1164027780980847836174557

theorem tailTrace_2266936 : CollatzResearch.WordTrace tailWord_2266936 prefixEnd_2266936 1164027780980847836174557 := by
  unfold tailWord_2266936
  simp only [CollatzResearch.WordTrace]
  refine ⟨41340974257642754345190331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55121299010190339126920441 41340974257642754345190331)
  ·
    refine ⟨62011461386464131517785497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41340974257642754345190331 62011461386464131517785497)
    ·
      refine ⟨46508596039848098638339123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62011461386464131517785497 46508596039848098638339123)
      ·
        refine ⟨69762894059772147957508685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46508596039848098638339123 69762894059772147957508685)
        ·
          refine ⟨26161085272414555484065757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69762894059772147957508685 26161085272414555484065757)
          ·
            refine ⟨9810406977155458306524659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26161085272414555484065757 9810406977155458306524659)
            ·
              refine ⟨14715610465733187459786989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9810406977155458306524659 14715610465733187459786989)
              ·
                refine ⟨5518353924649945297420121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14715610465733187459786989 5518353924649945297420121)
                ·
                  refine ⟨4138765443487458973065091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5518353924649945297420121 4138765443487458973065091)
                  ·
                    refine ⟨6208148165231188459597637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4138765443487458973065091 6208148165231188459597637)
                    ·
                      refine ⟨1164027780980847836174557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6208148165231188459597637 1164027780980847836174557)
                      ·
                        rfl

theorem cell23_2266936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 2, 1, 4].length) (baseStart_2266936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266936 prefixEnd_2266936 := by exact prefixLift 2266936
  have htrace : WordTrace (prefixWord ++ tailWord_2266936) baseStart_2266936 baseEnd_2266936 := by
    simpa [prefixWord, tailWord_2266936, baseEnd_2266936] using wordTrace_append hprefix tailTrace_2266936
  have hstable : (prefixWord ++ tailWord_2266936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266936).length < 2 ^ (prefixWord ++ tailWord_2266936).sum := by decide
  have hdescent : baseEnd_2266936 < baseStart_2266936 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266949 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 2, 1, 6]
def baseStart_2266949 : Nat := 118140960795 + 2266949 * 2 ^ 59
def prefixEnd_2266949 : Nat := 4983230072969 + 3 ^ 40 * 2266949 * 2
def baseEnd_2266949 : Nat := 1164034456229356285311997

theorem tailTrace_2266949 : CollatzResearch.WordTrace tailWord_2266949 prefixEnd_2266949 1164034456229356285311997 := by
  unfold tailWord_2266949
  simp only [CollatzResearch.WordTrace]
  refine ⟨82682422664238411910603901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55121615109492274607069267 82682422664238411910603901)
  ·
    refine ⟨31005908499089404466476463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82682422664238411910603901 31005908499089404466476463)
    ·
      refine ⟨46508862748634106699714695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31005908499089404466476463 46508862748634106699714695)
      ·
        refine ⟨69763294122951160049572043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46508862748634106699714695 69763294122951160049572043)
        ·
          refine ⟨104644941184426740074358065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69763294122951160049572043 104644941184426740074358065)
          ·
            refine ⟨78483705888320055055768549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104644941184426740074358065 78483705888320055055768549)
            ·
              refine ⟨14715694854060010322956603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78483705888320055055768549 14715694854060010322956603)
              ·
                refine ⟨22073542281090015484434905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14715694854060010322956603 22073542281090015484434905)
                ·
                  refine ⟨16555156710817511613326179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22073542281090015484434905 16555156710817511613326179)
                  ·
                    refine ⟨24832735066226267419989269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16555156710817511613326179 24832735066226267419989269)
                    ·
                      refine ⟨1164034456229356285311997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24832735066226267419989269 1164034456229356285311997)
                      ·
                        rfl

theorem cell23_2266949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 2, 1, 6].length) (baseStart_2266949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266949 prefixEnd_2266949 := by exact prefixLift 2266949
  have htrace : WordTrace (prefixWord ++ tailWord_2266949) baseStart_2266949 baseEnd_2266949 := by
    simpa [prefixWord, tailWord_2266949, baseEnd_2266949] using wordTrace_append hprefix tailTrace_2266949
  have hstable : (prefixWord ++ tailWord_2266949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266949).length < 2 ^ (prefixWord ++ tailWord_2266949).sum := by decide
  have hdescent : baseEnd_2266949 < baseStart_2266949 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266950 : List Nat := [6, 1, 1, 2, 1, 1, 2, 2, 2, 5]
def baseStart_2266950 : Nat := 118140960795 + 2266950 * 2 ^ 59
def prefixEnd_2266950 : Nat := 4983230072969 + 3 ^ 40 * 2266950 * 2
def baseEnd_2266950 : Nat := 388011656570003593799831

theorem tailTrace_2266950 : CollatzResearch.WordTrace tailWord_2266950 prefixEnd_2266950 388011656570003593799831 := by
  unfold tailWord_2266950
  simp only [CollatzResearch.WordTrace]
  refine ⟨2583826848038587158793447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55121639424823192720926869 2583826848038587158793447)
  ·
    refine ⟨3875740272057880738190171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2583826848038587158793447 3875740272057880738190171)
    ·
      refine ⟨5813610408086821107285257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3875740272057880738190171 5813610408086821107285257)
      ·
        refine ⟨4360207806065115830463943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5813610408086821107285257 4360207806065115830463943)
        ·
          refine ⟨6540311709097673745695915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4360207806065115830463943 6540311709097673745695915)
          ·
            refine ⟨9810467563646510618543873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6540311709097673745695915 9810467563646510618543873)
            ·
              refine ⟨7357850672734882963907905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9810467563646510618543873 7357850672734882963907905)
              ·
                refine ⟨5518388004551162222930929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7357850672734882963907905 5518388004551162222930929)
                ·
                  refine ⟨4138791003413371667198197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5518388004551162222930929 4138791003413371667198197)
                  ·
                    refine ⟨388011656570003593799831, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4138791003413371667198197 388011656570003593799831)
                    ·
                      rfl

theorem cell23_2266950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 1, 2, 2, 2, 5].length) (baseStart_2266950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266950 prefixEnd_2266950 := by exact prefixLift 2266950
  have htrace : WordTrace (prefixWord ++ tailWord_2266950) baseStart_2266950 baseEnd_2266950 := by
    simpa [prefixWord, tailWord_2266950, baseEnd_2266950] using wordTrace_append hprefix tailTrace_2266950
  have hstable : (prefixWord ++ tailWord_2266950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266950).length < 2 ^ (prefixWord ++ tailWord_2266950).sum := by decide
  have hdescent : baseEnd_2266950 < baseStart_2266950 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266976 : List Nat := [2, 1, 1, 3, 3, 2, 2, 3, 6]
def baseStart_2266976 : Nat := 118140960795 + 2266976 * 2 ^ 59
def prefixEnd_2266976 : Nat := 4983230072969 + 3 ^ 40 * 2266976 * 2
def baseEnd_2266976 : Nat := 129338702245225297741597

theorem tailTrace_2266976 : CollatzResearch.WordTrace tailWord_2266976 prefixEnd_2266976 129338702245225297741597 := by
  unfold tailWord_2266976
  simp only [CollatzResearch.WordTrace]
  refine ⟨41341703717570297760918391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55122271623427063681224521 41341703717570297760918391)
  ·
    refine ⟨62012555576355446641377587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41341703717570297760918391 62012555576355446641377587)
    ·
      refine ⟨93018833364533169962066381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62012555576355446641377587 93018833364533169962066381)
      ·
        refine ⟨34882062511699938735774893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93018833364533169962066381 34882062511699938735774893)
        ·
          refine ⟨13080773441887477025915585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34882062511699938735774893 13080773441887477025915585)
          ·
            refine ⟨9810580081415607769436689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13080773441887477025915585 9810580081415607769436689)
            ·
              refine ⟨7357935061061705827077517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9810580081415607769436689 7357935061061705827077517)
              ·
                refine ⟨2759225647898139685154069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7357935061061705827077517 2759225647898139685154069)
                ·
                  refine ⟨129338702245225297741597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2759225647898139685154069 129338702245225297741597)
                  ·
                    rfl

theorem cell23_2266976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 3, 6].length) (baseStart_2266976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266976 prefixEnd_2266976 := by exact prefixLift 2266976
  have htrace : WordTrace (prefixWord ++ tailWord_2266976) baseStart_2266976 baseEnd_2266976 := by
    simpa [prefixWord, tailWord_2266976, baseEnd_2266976] using wordTrace_append hprefix tailTrace_2266976
  have hstable : (prefixWord ++ tailWord_2266976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266976).length < 2 ^ (prefixWord ++ tailWord_2266976).sum := by decide
  have hdescent : baseEnd_2266976 < baseStart_2266976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266990 : List Nat := [4, 1, 2, 3, 1, 1, 3, 1, 2, 2, 3]
def baseStart_2266990 : Nat := 118140960795 + 2266990 * 2 ^ 59
def prefixEnd_2266990 : Nat := 4983230072969 + 3 ^ 40 * 2266990 * 2
def baseEnd_2266990 : Nat := 1164055508936190624899309

theorem tailTrace_2266990 : CollatzResearch.WordTrace tailWord_2266990 prefixEnd_2266990 1164055508936190624899309 := by
  unfold tailWord_2266990
  simp only [CollatzResearch.WordTrace]
  refine ⟨10335489757136234489105803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55122612038059917275230949 10335489757136234489105803)
  ·
    refine ⟨15503234635704351733658705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10335489757136234489105803 15503234635704351733658705)
    ·
      refine ⟨11627425976778263800244029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15503234635704351733658705 11627425976778263800244029)
      ·
        refine ⟨4360284741291848925091511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11627425976778263800244029 4360284741291848925091511)
        ·
          refine ⟨6540427111937773387637267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4360284741291848925091511 6540427111937773387637267)
          ·
            refine ⟨9810640667906660081455901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6540427111937773387637267 9810640667906660081455901)
            ·
              refine ⟨3678990250464997530545963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9810640667906660081455901 3678990250464997530545963)
              ·
                refine ⟨5518485375697496295818945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3678990250464997530545963 5518485375697496295818945)
                ·
                  refine ⟨4138864031773122221864209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5518485375697496295818945 4138864031773122221864209)
                  ·
                    refine ⟨3104148023829841666398157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4138864031773122221864209 3104148023829841666398157)
                    ·
                      refine ⟨1164055508936190624899309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3104148023829841666398157 1164055508936190624899309)
                      ·
                        rfl

theorem cell23_2266990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 1, 2, 2, 3].length) (baseStart_2266990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266990 prefixEnd_2266990 := by exact prefixLift 2266990
  have htrace : WordTrace (prefixWord ++ tailWord_2266990) baseStart_2266990 baseEnd_2266990 := by
    simpa [prefixWord, tailWord_2266990, baseEnd_2266990] using wordTrace_append hprefix tailTrace_2266990
  have hstable : (prefixWord ++ tailWord_2266990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266990).length < 2 ^ (prefixWord ++ tailWord_2266990).sum := by decide
  have hdescent : baseEnd_2266990 < baseStart_2266990 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2266999 : List Nat := [1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 5]
def baseStart_2266999 : Nat := 118140960795 + 2266999 * 2 ^ 59
def prefixEnd_2266999 : Nat := 4983230072969 + 3 ^ 40 * 2266999 * 2
def baseEnd_2266999 : Nat := 1164060130262081089686767

theorem tailTrace_2266999 : CollatzResearch.WordTrace tailWord_2266999 prefixEnd_2266999 1164060130262081089686767 := by
  unfold tailWord_2266999
  simp only [CollatzResearch.WordTrace]
  refine ⟨82684246314057270449924051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55122830876038180299949367 82684246314057270449924051)
  ·
    refine ⟨124026369471085905674886077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82684246314057270449924051 124026369471085905674886077)
    ·
      refine ⟨46509888551657214628082279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124026369471085905674886077 46509888551657214628082279)
      ·
        refine ⟨69764832827485821942123419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46509888551657214628082279 69764832827485821942123419)
        ·
          refine ⟨104647249241228732913185129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69764832827485821942123419 104647249241228732913185129)
          ·
            refine ⟨78485436930921549684888847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104647249241228732913185129 78485436930921549684888847)
            ·
              refine ⟨117728155396382324527333271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78485436930921549684888847 117728155396382324527333271)
              ·
                refine ⟨176592233094573486790999907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117728155396382324527333271 176592233094573486790999907)
                ·
                  refine ⟨264888349641860230186499861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 176592233094573486790999907 264888349641860230186499861)
                  ·
                    refine ⟨12416641389462198289992181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 264888349641860230186499861 12416641389462198289992181)
                    ·
                      refine ⟨1164060130262081089686767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12416641389462198289992181 1164060130262081089686767)
                      ·
                        rfl

theorem cell23_2266999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_2266999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2266999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2266999 prefixEnd_2266999 := by exact prefixLift 2266999
  have htrace : WordTrace (prefixWord ++ tailWord_2266999) baseStart_2266999 baseEnd_2266999 := by
    simpa [prefixWord, tailWord_2266999, baseEnd_2266999] using wordTrace_append hprefix tailTrace_2266999
  have hstable : (prefixWord ++ tailWord_2266999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2266999).length < 2 ^ (prefixWord ++ tailWord_2266999).sum := by decide
  have hdescent : baseEnd_2266999 < baseStart_2266999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2266999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267013 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 4, 3, 2]
def baseStart_2267013 : Nat := 118140960795 + 2267013 * 2 ^ 59
def prefixEnd_2267013 : Nat := 4983230072969 + 3 ^ 40 * 2267013 * 2
def baseEnd_2267013 : Nat := 1164067318991244034911703

theorem tailTrace_2267013 : CollatzResearch.WordTrace tailWord_2267013 prefixEnd_2267013 1164067318991244034911703 := by
  unfold tailWord_2267013
  simp only [CollatzResearch.WordTrace]
  refine ⟨82684756936006550840933693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55123171290671033893955795 82684756936006550840933693)
  ·
    refine ⟨31006783851002456565350135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82684756936006550840933693 31006783851002456565350135)
    ·
      refine ⟨46510175776503684848025203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31006783851002456565350135 46510175776503684848025203)
      ·
        refine ⟨69765263664755527272037805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46510175776503684848025203 69765263664755527272037805)
        ·
          refine ⟨26161973874283322727014177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69765263664755527272037805 26161973874283322727014177)
          ·
            refine ⟨19621480405712492045260633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26161973874283322727014177 19621480405712492045260633)
            ·
              refine ⟨14716110304284369033945475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19621480405712492045260633 14716110304284369033945475)
              ·
                refine ⟨22074165456426553550918213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14716110304284369033945475 22074165456426553550918213)
                ·
                  refine ⟨4138906023079978790797165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22074165456426553550918213 4138906023079978790797165)
                  ·
                    refine ⟨1552089758654992046548937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4138906023079978790797165 1552089758654992046548937)
                    ·
                      refine ⟨1164067318991244034911703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1552089758654992046548937 1164067318991244034911703)
                      ·
                        rfl

theorem cell23_2267013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 4, 3, 2].length) (baseStart_2267013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267013 prefixEnd_2267013 := by exact prefixLift 2267013
  have htrace : WordTrace (prefixWord ++ tailWord_2267013) baseStart_2267013 baseEnd_2267013 := by
    simpa [prefixWord, tailWord_2267013, baseEnd_2267013] using wordTrace_append hprefix tailTrace_2267013
  have hstable : (prefixWord ++ tailWord_2267013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267013).length < 2 ^ (prefixWord ++ tailWord_2267013).sum := by decide
  have hdescent : baseEnd_2267013 < baseStart_2267013 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267086 : List Nat := [4, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6]
def baseStart_2267086 : Nat := 118140960795 + 2267086 * 2 ^ 59
def prefixEnd_2267086 : Nat := 4983230072969 + 3 ^ 40 * 2267086 * 2
def baseEnd_2267086 : Nat := 1164104803079022249298867

theorem tailTrace_2267086 : CollatzResearch.WordTrace tailWord_2267086 prefixEnd_2267086 1164104803079022249298867 := by
  unfold tailWord_2267086
  simp only [CollatzResearch.WordTrace]
  refine ⟨10335927433092760538542639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55124946309828056205560741 10335927433092760538542639)
  ·
    refine ⟨15503891149639140807813959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10335927433092760538542639 15503891149639140807813959)
    ·
      refine ⟨23255836724458711211720939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15503891149639140807813959 23255836724458711211720939)
      ·
        refine ⟨34883755086688066817581409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23255836724458711211720939 34883755086688066817581409)
        ·
          refine ⟨26162816315016050113186057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34883755086688066817581409 26162816315016050113186057)
          ·
            refine ⟨19622112236262037584889543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26162816315016050113186057 19622112236262037584889543)
            ·
              refine ⟨29433168354393056377334315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19622112236262037584889543 29433168354393056377334315)
              ·
                refine ⟨44149752531589584566001473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29433168354393056377334315 44149752531589584566001473)
                ·
                  refine ⟨33112314398692188424501105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44149752531589584566001473 33112314398692188424501105)
                  ·
                    refine ⟨24834235799019141318375829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33112314398692188424501105 24834235799019141318375829)
                    ·
                      refine ⟨1164104803079022249298867, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24834235799019141318375829 1164104803079022249298867)
                      ·
                        rfl

theorem cell23_2267086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 2, 1, 1, 2, 2, 6].length) (baseStart_2267086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267086 prefixEnd_2267086 := by exact prefixLift 2267086
  have htrace : WordTrace (prefixWord ++ tailWord_2267086) baseStart_2267086 baseEnd_2267086 := by
    simpa [prefixWord, tailWord_2267086, baseEnd_2267086] using wordTrace_append hprefix tailTrace_2267086
  have hstable : (prefixWord ++ tailWord_2267086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267086).length < 2 ^ (prefixWord ++ tailWord_2267086).sum := by decide
  have hdescent : baseEnd_2267086 < baseStart_2267086 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267094 : List Nat := [5, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4]
def baseStart_2267094 : Nat := 118140960795 + 2267094 * 2 ^ 59
def prefixEnd_2267094 : Nat := 4983230072969 + 3 ^ 40 * 2267094 * 2
def baseEnd_2267094 : Nat := 1164108910924258217998831

theorem tailTrace_2267094 : CollatzResearch.WordTrace tailWord_2267094 prefixEnd_2267094 1164108910924258217998831 := by
  unfold tailWord_2267094
  simp only [CollatzResearch.WordTrace]
  refine ⟨5167981953044568854664521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55125140832475401116421557 5167981953044568854664521)
  ·
    refine ⟨3875986464783426640998391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5167981953044568854664521 3875986464783426640998391)
    ·
      refine ⟨5813979697175139961497587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3875986464783426640998391 5813979697175139961497587)
      ·
        refine ⟨8720969545762709942246381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5813979697175139961497587 8720969545762709942246381)
        ·
          refine ⟨3270363579661016228342393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8720969545762709942246381 3270363579661016228342393)
          ·
            refine ⟨2452772684745762171256795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3270363579661016228342393 2452772684745762171256795)
            ·
              refine ⟨3679159027118643256885193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2452772684745762171256795 3679159027118643256885193)
              ·
                refine ⟨2759369270338982442663895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3679159027118643256885193 2759369270338982442663895)
                ·
                  refine ⟨4139053905508473663995843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2759369270338982442663895 4139053905508473663995843)
                  ·
                    refine ⟨6208580858262710495993765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4139053905508473663995843 6208580858262710495993765)
                    ·
                      refine ⟨1164108910924258217998831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6208580858262710495993765 1164108910924258217998831)
                      ·
                        rfl

theorem cell23_2267094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 1, 1, 4].length) (baseStart_2267094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267094 prefixEnd_2267094 := by exact prefixLift 2267094
  have htrace : WordTrace (prefixWord ++ tailWord_2267094) baseStart_2267094 baseEnd_2267094 := by
    simpa [prefixWord, tailWord_2267094, baseEnd_2267094] using wordTrace_append hprefix tailTrace_2267094
  have hstable : (prefixWord ++ tailWord_2267094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267094).length < 2 ^ (prefixWord ++ tailWord_2267094).sum := by decide
  have hdescent : baseEnd_2267094 < baseStart_2267094 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267097 : List Nat := [1, 2, 1, 2, 6, 2, 1, 2, 1, 2, 3]
def baseStart_2267097 : Nat := 118140960795 + 2267097 * 2 ^ 59
def prefixEnd_2267097 : Nat := 4983230072969 + 3 ^ 40 * 2267097 * 2
def baseEnd_2267097 : Nat := 1164110451366221706261317

theorem tailTrace_2267097 : CollatzResearch.WordTrace tailWord_2267097 prefixEnd_2267097 1164110451366221706261317 := by
  unfold tailWord_2267097
  simp only [CollatzResearch.WordTrace]
  refine ⟨82687820667702233186991545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55125213778468155457994363 82687820667702233186991545)
  ·
    refine ⟨62015865500776674890243659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82687820667702233186991545 62015865500776674890243659)
    ·
      refine ⟨93023798251165012335365489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62015865500776674890243659 93023798251165012335365489)
      ·
        refine ⟨69767848688373759251524117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93023798251165012335365489 69767848688373759251524117)
        ·
          refine ⟨3270367907267519964915193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69767848688373759251524117 3270367907267519964915193)
          ·
            refine ⟨2452775930450639973686395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3270367907267519964915193 2452775930450639973686395)
            ·
              refine ⟨3679163895675959960529593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2452775930450639973686395 3679163895675959960529593)
              ·
                refine ⟨2759372921756969970397195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3679163895675959960529593 2759372921756969970397195)
                ·
                  refine ⟨4139059382635454955595793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2759372921756969970397195 4139059382635454955595793)
                  ·
                    refine ⟨3104294536976591216696845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4139059382635454955595793 3104294536976591216696845)
                    ·
                      refine ⟨1164110451366221706261317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3104294536976591216696845 1164110451366221706261317)
                      ·
                        rfl

theorem cell23_2267097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 6, 2, 1, 2, 1, 2, 3].length) (baseStart_2267097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267097 prefixEnd_2267097 := by exact prefixLift 2267097
  have htrace : WordTrace (prefixWord ++ tailWord_2267097) baseStart_2267097 baseEnd_2267097 := by
    simpa [prefixWord, tailWord_2267097, baseEnd_2267097] using wordTrace_append hprefix tailTrace_2267097
  have hstable : (prefixWord ++ tailWord_2267097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267097).length < 2 ^ (prefixWord ++ tailWord_2267097).sum := by decide
  have hdescent : baseEnd_2267097 < baseStart_2267097 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267116 : List Nat := [2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 4]
def baseStart_2267116 : Nat := 118140960795 + 2267116 * 2 ^ 59
def prefixEnd_2267116 : Nat := 4983230072969 + 3 ^ 40 * 2267116 * 2
def baseEnd_2267116 : Nat := 1164120207498657131923729

theorem tailTrace_2267116 : CollatzResearch.WordTrace tailWord_2267116 prefixEnd_2267116 1164120207498657131923729 := by
  unfold tailWord_2267116
  simp only [CollatzResearch.WordTrace]
  refine ⟨41344256827316699715966601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55125675769755599621288801 41344256827316699715966601)
  ·
    refine ⟨31008192620487524786974951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41344256827316699715966601 31008192620487524786974951)
    ·
      refine ⟨46512288930731287180462427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31008192620487524786974951 46512288930731287180462427)
      ·
        refine ⟨69768433396096930770693641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46512288930731287180462427 69768433396096930770693641)
        ·
          refine ⟨52326325047072698078020231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69768433396096930770693641 52326325047072698078020231)
          ·
            refine ⟨78489487570609047117030347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52326325047072698078020231 78489487570609047117030347)
            ·
              refine ⟨117734231355913570675545521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78489487570609047117030347 117734231355913570675545521)
              ·
                refine ⟨88300673516935178006659141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117734231355913570675545521 88300673516935178006659141)
                ·
                  refine ⟨16556376284425345876248589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88300673516935178006659141 16556376284425345876248589)
                  ·
                    refine ⟨6208641106659504703593221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16556376284425345876248589 6208641106659504703593221)
                    ·
                      refine ⟨1164120207498657131923729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6208641106659504703593221 1164120207498657131923729)
                      ·
                        rfl

theorem cell23_2267116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 3, 4].length) (baseStart_2267116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267116 prefixEnd_2267116 := by exact prefixLift 2267116
  have htrace : WordTrace (prefixWord ++ tailWord_2267116) baseStart_2267116 baseEnd_2267116 := by
    simpa [prefixWord, tailWord_2267116, baseEnd_2267116] using wordTrace_append hprefix tailTrace_2267116
  have hstable : (prefixWord ++ tailWord_2267116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267116).length < 2 ^ (prefixWord ++ tailWord_2267116).sum := by decide
  have hdescent : baseEnd_2267116 < baseStart_2267116 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267120 : List Nat := [2, 1, 1, 1, 3, 2, 2, 5, 1, 3, 2]
def baseStart_2267120 : Nat := 118140960795 + 2267120 * 2 ^ 59
def prefixEnd_2267120 : Nat := 4983230072969 + 3 ^ 40 * 2267120 * 2
def baseEnd_2267120 : Nat := 1164122261421275116273711

theorem tailTrace_2267120 : CollatzResearch.WordTrace tailWord_2267120 prefixEnd_2267120 1164122261421275116273711 := by
  unfold tailWord_2267120
  simp only [CollatzResearch.WordTrace]
  refine ⟨41344329773309454057539407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55125773031079272076719209 41344329773309454057539407)
  ·
    refine ⟨62016494659964181086309111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41344329773309454057539407 62016494659964181086309111)
    ·
      refine ⟨93024741989946271629463667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62016494659964181086309111 93024741989946271629463667)
      ·
        refine ⟨139537112984919407444195501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93024741989946271629463667 139537112984919407444195501)
        ·
          refine ⟨52326417369344777791573313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139537112984919407444195501 52326417369344777791573313)
          ·
            refine ⟨39244813027008583343679985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52326417369344777791573313 39244813027008583343679985)
            ·
              refine ⟨29433609770256437507759989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39244813027008583343679985 29433609770256437507759989)
              ·
                refine ⟨2759400915961541016352499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29433609770256437507759989 2759400915961541016352499)
                ·
                  refine ⟨4139101373942311524528749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2759400915961541016352499 4139101373942311524528749)
                  ·
                    refine ⟨1552163015228366821698281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4139101373942311524528749 1552163015228366821698281)
                    ·
                      refine ⟨1164122261421275116273711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1552163015228366821698281 1164122261421275116273711)
                      ·
                        rfl

theorem cell23_2267120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5, 1, 3, 2].length) (baseStart_2267120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267120 prefixEnd_2267120 := by exact prefixLift 2267120
  have htrace : WordTrace (prefixWord ++ tailWord_2267120) baseStart_2267120 baseEnd_2267120 := by
    simpa [prefixWord, tailWord_2267120, baseEnd_2267120] using wordTrace_append hprefix tailTrace_2267120
  have hstable : (prefixWord ++ tailWord_2267120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267120).length < 2 ^ (prefixWord ++ tailWord_2267120).sum := by decide
  have hdescent : baseEnd_2267120 < baseStart_2267120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267136 : List Nat := [2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 5]
def baseStart_2267136 : Nat := 118140960795 + 2267136 * 2 ^ 59
def prefixEnd_2267136 : Nat := 4983230072969 + 3 ^ 40 * 2267136 * 2
def baseEnd_2267136 : Nat := 1164130477111747053673637

theorem tailTrace_2267136 : CollatzResearch.WordTrace tailWord_2267136 prefixEnd_2267136 1164130477111747053673637 := by
  unfold tailWord_2267136
  simp only [CollatzResearch.WordTrace]
  refine ⟨41344621557280471423830631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55126162076373961898440841 41344621557280471423830631)
  ·
    refine ⟨62016932335920707135745947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41344621557280471423830631 62016932335920707135745947)
    ·
      refine ⟨93025398503881060703618921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62016932335920707135745947 93025398503881060703618921)
      ·
        refine ⟨69769048877910795527714191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93025398503881060703618921 69769048877910795527714191)
        ·
          refine ⟨104653573316866193291571287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69769048877910795527714191 104653573316866193291571287)
          ·
            refine ⟨156980359975299289937356931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104653573316866193291571287 156980359975299289937356931)
            ·
              refine ⟨235470539962948934906035397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 156980359975299289937356931 235470539962948934906035397)
              ·
                refine ⟨44150726243052925294881637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 235470539962948934906035397 44150726243052925294881637)
                ·
                  refine ⟨8278261170572423492790307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44150726243052925294881637 8278261170572423492790307)
                  ·
                    refine ⟨12417391755858635239185461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8278261170572423492790307 12417391755858635239185461)
                    ·
                      refine ⟨1164130477111747053673637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12417391755858635239185461 1164130477111747053673637)
                      ·
                        rfl

theorem cell23_2267136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 4, 4, 1, 5].length) (baseStart_2267136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267136 prefixEnd_2267136 := by exact prefixLift 2267136
  have htrace : WordTrace (prefixWord ++ tailWord_2267136) baseStart_2267136 baseEnd_2267136 := by
    simpa [prefixWord, tailWord_2267136, baseEnd_2267136] using wordTrace_append hprefix tailTrace_2267136
  have hstable : (prefixWord ++ tailWord_2267136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267136).length < 2 ^ (prefixWord ++ tailWord_2267136).sum := by decide
  have hdescent : baseEnd_2267136 < baseStart_2267136 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267143 : List Nat := [1, 1, 4, 3, 1, 3, 1, 1, 2, 6]
def baseStart_2267143 : Nat := 118140960795 + 2267143 * 2 ^ 59
def prefixEnd_2267143 : Nat := 4983230072969 + 3 ^ 40 * 2267143 * 2
def baseEnd_2267143 : Nat := 388044690492109508762035

theorem tailTrace_2267143 : CollatzResearch.WordTrace tailWord_2267143 prefixEnd_2267143 388044690492109508762035 := by
  unfold tailWord_2267143
  simp only [CollatzResearch.WordTrace]
  refine ⟨82689498425535583043166083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55126332283690388695444055 82689498425535583043166083)
  ·
    refine ⟨124034247638303374564749125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82689498425535583043166083 124034247638303374564749125)
    ·
      refine ⟨23256421432181882730890461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124034247638303374564749125 23256421432181882730890461)
      ·
        refine ⟨8721158037068206024083923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23256421432181882730890461 8721158037068206024083923)
        ·
          refine ⟨13081737055602309036125885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8721158037068206024083923 13081737055602309036125885)
          ·
            refine ⟨4905651395850865888547207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13081737055602309036125885 4905651395850865888547207)
            ·
              refine ⟨7358477093776298832820811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4905651395850865888547207 7358477093776298832820811)
              ·
                refine ⟨11037715640664448249231217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7358477093776298832820811 11037715640664448249231217)
                ·
                  refine ⟨8278286730498336186923413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11037715640664448249231217 8278286730498336186923413)
                  ·
                    refine ⟨388044690492109508762035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8278286730498336186923413 388044690492109508762035)
                    ·
                      rfl

theorem cell23_2267143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_2267143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267143 prefixEnd_2267143 := by exact prefixLift 2267143
  have htrace : WordTrace (prefixWord ++ tailWord_2267143) baseStart_2267143 baseEnd_2267143 := by
    simpa [prefixWord, tailWord_2267143, baseEnd_2267143] using wordTrace_append hprefix tailTrace_2267143
  have hstable : (prefixWord ++ tailWord_2267143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267143).length < 2 ^ (prefixWord ++ tailWord_2267143).sum := by decide
  have hdescent : baseEnd_2267143 < baseStart_2267143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267184 : List Nat := [2, 1, 1, 1, 2, 7, 1, 2, 2, 2, 2]
def baseStart_2267184 : Nat := 118140960795 + 2267184 * 2 ^ 59
def prefixEnd_2267184 : Nat := 4983230072969 + 3 ^ 40 * 2267184 * 2
def baseEnd_2267184 : Nat := 1164155124183162865873417

theorem tailTrace_2267184 : CollatzResearch.WordTrace tailWord_2267184 prefixEnd_2267184 1164155124183162865873417 := by
  unfold tailWord_2267184
  simp only [CollatzResearch.WordTrace]
  refine ⟨41345496909193523522704303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55127329212258031363605737 41345496909193523522704303)
  ·
    refine ⟨62018245363790285284056455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41345496909193523522704303 62018245363790285284056455)
    ·
      refine ⟨93027368045685427926084683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62018245363790285284056455 93027368045685427926084683)
      ·
        refine ⟨139541052068528141889127025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93027368045685427926084683 139541052068528141889127025)
        ·
          refine ⟨104655789051396106416845269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139541052068528141889127025 104655789051396106416845269)
          ·
            refine ⟨2452870055892096244144811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 104655789051396106416845269 2452870055892096244144811)
            ·
              refine ⟨3679305083838144366217217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2452870055892096244144811 3679305083838144366217217)
              ·
                refine ⟨2759478812878608274662913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3679305083838144366217217 2759478812878608274662913)
                ·
                  refine ⟨2069609109658956205997185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2759478812878608274662913 2069609109658956205997185)
                  ·
                    refine ⟨1552206832244217154497889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2069609109658956205997185 1552206832244217154497889)
                    ·
                      refine ⟨1164155124183162865873417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1552206832244217154497889 1164155124183162865873417)
                      ·
                        rfl

theorem cell23_2267184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 1, 2, 2, 2, 2].length) (baseStart_2267184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267184 prefixEnd_2267184 := by exact prefixLift 2267184
  have htrace : WordTrace (prefixWord ++ tailWord_2267184) baseStart_2267184 baseEnd_2267184 := by
    simpa [prefixWord, tailWord_2267184, baseEnd_2267184] using wordTrace_append hprefix tailTrace_2267184
  have hstable : (prefixWord ++ tailWord_2267184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267184).length < 2 ^ (prefixWord ++ tailWord_2267184).sum := by decide
  have hdescent : baseEnd_2267184 < baseStart_2267184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267190 : List Nat := [5, 1, 2, 1, 1, 1, 4, 1, 7]
def baseStart_2267190 : Nat := 118140960795 + 2267190 * 2 ^ 59
def prefixEnd_2267190 : Nat := 4983230072969 + 3 ^ 40 * 2267190 * 2
def baseEnd_2267190 : Nat := 129350911674121093599821

theorem tailTrace_2267190 : CollatzResearch.WordTrace tailWord_2267190 prefixEnd_2267190 129350911674121093599821 := by
  unfold tailWord_2267190
  simp only [CollatzResearch.WordTrace]
  refine ⟨5168200791022831879382939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55127475104243540046751349 5168200791022831879382939)
  ·
    refine ⟨7752301186534247819074409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5168200791022831879382939 7752301186534247819074409)
    ·
      refine ⟨5814225889900685864305807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7752301186534247819074409 5814225889900685864305807)
      ·
        refine ⟨8721338834851028796458711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5814225889900685864305807 8721338834851028796458711)
        ·
          refine ⟨13082008252276543194688067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8721338834851028796458711 13082008252276543194688067)
          ·
            refine ⟨19623012378414814792032101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13082008252276543194688067 19623012378414814792032101)
            ·
              refine ⟨3679314820952777773506019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19623012378414814792032101 3679314820952777773506019)
              ·
                refine ⟨5518972231429166660259029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3679314820952777773506019 5518972231429166660259029)
                ·
                  refine ⟨129350911674121093599821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5518972231429166660259029 129350911674121093599821)
                  ·
                    rfl

theorem cell23_2267190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 4, 1, 7].length) (baseStart_2267190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267190 prefixEnd_2267190 := by exact prefixLift 2267190
  have htrace : WordTrace (prefixWord ++ tailWord_2267190) baseStart_2267190 baseEnd_2267190 := by
    simpa [prefixWord, tailWord_2267190, baseEnd_2267190] using wordTrace_append hprefix tailTrace_2267190
  have hstable : (prefixWord ++ tailWord_2267190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267190).length < 2 ^ (prefixWord ++ tailWord_2267190).sum := by decide
  have hdescent : baseEnd_2267190 < baseStart_2267190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267201 : List Nat := [1, 2, 5, 1, 2, 2, 3, 1, 2, 2, 2]
def baseStart_2267201 : Nat := 118140960795 + 2267201 * 2 ^ 59
def prefixEnd_2267201 : Nat := 4983230072969 + 3 ^ 40 * 2267201 * 2
def baseEnd_2267201 : Nat := 1164163853354289299360839

theorem tailTrace_2267201 : CollatzResearch.WordTrace tailWord_2267201 prefixEnd_2267201 1164163853354289299360839 := by
  unfold tailWord_2267201
  simp only [CollatzResearch.WordTrace]
  refine ⟨82691613859325458948777457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55127742572883639299184971 82691613859325458948777457)
  ·
    refine ⟨62018710394494094211583093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82691613859325458948777457 62018710394494094211583093)
    ·
      refine ⟨5814254099483821332335915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62018710394494094211583093 5814254099483821332335915)
      ·
        refine ⟨8721381149225731998503873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5814254099483821332335915 8721381149225731998503873)
        ·
          refine ⟨6541035861919298998877905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8721381149225731998503873 6541035861919298998877905)
          ·
            refine ⟨4905776896439474249158429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6541035861919298998877905 4905776896439474249158429)
            ·
              refine ⟨1839666336164802843434411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4905776896439474249158429 1839666336164802843434411)
              ·
                refine ⟨2759499504247204265151617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1839666336164802843434411 2759499504247204265151617)
                ·
                  refine ⟨2069624628185403198863713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2759499504247204265151617 2069624628185403198863713)
                  ·
                    refine ⟨1552218471139052399147785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2069624628185403198863713 1552218471139052399147785)
                    ·
                      refine ⟨1164163853354289299360839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1552218471139052399147785 1164163853354289299360839)
                      ·
                        rfl

theorem cell23_2267201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 3, 1, 2, 2, 2].length) (baseStart_2267201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267201 prefixEnd_2267201 := by exact prefixLift 2267201
  have htrace : WordTrace (prefixWord ++ tailWord_2267201) baseStart_2267201 baseEnd_2267201 := by
    simpa [prefixWord, tailWord_2267201, baseEnd_2267201] using wordTrace_append hprefix tailTrace_2267201
  have hstable : (prefixWord ++ tailWord_2267201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267201).length < 2 ^ (prefixWord ++ tailWord_2267201).sum := by decide
  have hdescent : baseEnd_2267201 < baseStart_2267201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267223 : List Nat := [1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 4]
def baseStart_2267223 : Nat := 118140960795 + 2267223 * 2 ^ 59
def prefixEnd_2267223 : Nat := 4983230072969 + 3 ^ 40 * 2267223 * 2
def baseEnd_2267223 : Nat := 1164175149928688213285737

theorem tailTrace_2267223 : CollatzResearch.WordTrace tailWord_2267223 prefixEnd_2267223 1164175149928688213285737 := by
  unfold tailWord_2267223
  simp only [CollatzResearch.WordTrace]
  refine ⟨82692416265245756706078323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55128277510163837804052215 82692416265245756706078323)
  ·
    refine ⟨124038624397868635059117485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82692416265245756706078323 124038624397868635059117485)
    ·
      refine ⟨46514484149200738147169057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124038624397868635059117485 46514484149200738147169057)
      ·
        refine ⟨34885863111900553610376793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46514484149200738147169057 34885863111900553610376793)
        ·
          refine ⟨26164397333925415207782595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34885863111900553610376793 26164397333925415207782595)
          ·
            refine ⟨39246596000888122811673893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26164397333925415207782595 39246596000888122811673893)
            ·
              refine ⟨7358736750166523027188855, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39246596000888122811673893 7358736750166523027188855)
              ·
                refine ⟨11038105125249784540783283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7358736750166523027188855 11038105125249784540783283)
                ·
                  refine ⟨16557157687874676811174925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11038105125249784540783283 16557157687874676811174925)
                  ·
                    refine ⟨6208934132953003804190597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16557157687874676811174925 6208934132953003804190597)
                    ·
                      refine ⟨1164175149928688213285737, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6208934132953003804190597 1164175149928688213285737)
                      ·
                        rfl

theorem cell23_2267223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_2267223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267223 prefixEnd_2267223 := by exact prefixLift 2267223
  have htrace : WordTrace (prefixWord ++ tailWord_2267223) baseStart_2267223 baseEnd_2267223 := by
    simpa [prefixWord, tailWord_2267223, baseEnd_2267223] using wordTrace_append hprefix tailTrace_2267223
  have hstable : (prefixWord ++ tailWord_2267223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267223).length < 2 ^ (prefixWord ++ tailWord_2267223).sum := by decide
  have hdescent : baseEnd_2267223 < baseStart_2267223 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267324 : List Nat := [2, 2, 2, 3, 3, 1, 1, 2, 3, 1, 3]
def baseStart_2267324 : Nat := 118140960795 + 2267324 * 2 ^ 59
def prefixEnd_2267324 : Nat := 4983230072969 + 3 ^ 40 * 2267324 * 2
def baseEnd_2267324 : Nat := 1164227011474792318122773

theorem tailTrace_2267324 : CollatzResearch.WordTrace tailWord_2267324 prefixEnd_2267324 1164227011474792318122773 := by
  unfold tailWord_2267324
  simp only [CollatzResearch.WordTrace]
  refine ⟨41348050018939925477752513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55130733358586567303670017 41348050018939925477752513)
  ·
    refine ⟨31011037514204944108314385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41348050018939925477752513 31011037514204944108314385)
    ·
      refine ⟨23258278135653708081235789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31011037514204944108314385 23258278135653708081235789)
      ·
        refine ⟨8721854300870140530463421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23258278135653708081235789 8721854300870140530463421)
        ·
          refine ⟨3270695362826302698923783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8721854300870140530463421 3270695362826302698923783)
          ·
            refine ⟨4906043044239454048385675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3270695362826302698923783 4906043044239454048385675)
            ·
              refine ⟨7359064566359181072578513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4906043044239454048385675 7359064566359181072578513)
              ·
                refine ⟨5519298424769385804433885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7359064566359181072578513 5519298424769385804433885)
                ·
                  refine ⟨2069736909288519676662707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5519298424769385804433885 2069736909288519676662707)
                  ·
                    refine ⟨3104605363932779514994061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2069736909288519676662707 3104605363932779514994061)
                    ·
                      refine ⟨1164227011474792318122773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3104605363932779514994061 1164227011474792318122773)
                      ·
                        rfl

theorem cell23_2267324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 3, 1, 3].length) (baseStart_2267324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267324 prefixEnd_2267324 := by exact prefixLift 2267324
  have htrace : WordTrace (prefixWord ++ tailWord_2267324) baseStart_2267324 baseEnd_2267324 := by
    simpa [prefixWord, tailWord_2267324, baseEnd_2267324] using wordTrace_append hprefix tailTrace_2267324
  have hstable : (prefixWord ++ tailWord_2267324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267324).length < 2 ^ (prefixWord ++ tailWord_2267324).sum := by decide
  have hdescent : baseEnd_2267324 < baseStart_2267324 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267367 : List Nat := [1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_2267367 : Nat := 118140960795 + 2267367 * 2 ^ 59
def prefixEnd_2267367 : Nat := 4983230072969 + 3 ^ 40 * 2267367 * 2
def baseEnd_2267367 : Nat := 1164249091142935649885075

theorem tailTrace_2267367 : CollatzResearch.WordTrace tailWord_2267367 prefixEnd_2267367 1164249091142935649885075 := by
  unfold tailWord_2267367
  simp only [CollatzResearch.WordTrace]
  refine ⟨82697668376724069299320355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55131778917816046199546903 82697668376724069299320355)
  ·
    refine ⟨124046502565086103948980533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82697668376724069299320355 124046502565086103948980533)
    ·
      refine ⟨11629359615476822245216925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124046502565086103948980533 11629359615476822245216925)
      ·
        refine ⟨4361009855803808341956347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11629359615476822245216925 4361009855803808341956347)
        ·
          refine ⟨6541514783705712512934521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4361009855803808341956347 6541514783705712512934521)
          ·
            refine ⟨4906136087779284384700891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6541514783705712512934521 4906136087779284384700891)
            ·
              refine ⟨7359204131668926577051337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4906136087779284384700891 7359204131668926577051337)
              ·
                refine ⟨5519403098751694932788503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7359204131668926577051337 5519403098751694932788503)
                ·
                  refine ⟨8279104648127542399182755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5519403098751694932788503 8279104648127542399182755)
                  ·
                    refine ⟨12418656972191313598774133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8279104648127542399182755 12418656972191313598774133)
                    ·
                      refine ⟨1164249091142935649885075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12418656972191313598774133 1164249091142935649885075)
                      ·
                        rfl

theorem cell23_2267367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_2267367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267367 prefixEnd_2267367 := by exact prefixLift 2267367
  have htrace : WordTrace (prefixWord ++ tailWord_2267367) baseStart_2267367 baseEnd_2267367 := by
    simpa [prefixWord, tailWord_2267367, baseEnd_2267367] using wordTrace_append hprefix tailTrace_2267367
  have hstable : (prefixWord ++ tailWord_2267367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267367).length < 2 ^ (prefixWord ++ tailWord_2267367).sum := by decide
  have hdescent : baseEnd_2267367 < baseStart_2267367 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267420 : List Nat := [2, 2, 3, 1, 1, 1, 1, 3, 2, 3, 4]
def baseStart_2267420 : Nat := 118140960795 + 2267420 * 2 ^ 59
def prefixEnd_2267420 : Nat := 4983230072969 + 3 ^ 40 * 2267420 * 2
def baseEnd_2267420 : Nat := 1164276305617623942522331

theorem tailTrace_2267420 : CollatzResearch.WordTrace tailWord_2267420 prefixEnd_2267420 1164276305617623942522331 := by
  unfold tailWord_2267420
  simp only [CollatzResearch.WordTrace]
  refine ⟨41349800722766029675499857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55133067630354706233999809 41349800722766029675499857)
  ·
    refine ⟨31012350542074522256624893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41349800722766029675499857 31012350542074522256624893)
    ·
      refine ⟨11629631453277945846234335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31012350542074522256624893 11629631453277945846234335)
      ·
        refine ⟨17444447179916918769351503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11629631453277945846234335 17444447179916918769351503)
        ·
          refine ⟨26166670769875378154027255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17444447179916918769351503 26166670769875378154027255)
          ·
            refine ⟨39250006154813067231040883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26166670769875378154027255 39250006154813067231040883)
            ·
              refine ⟨58875009232219600846561325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39250006154813067231040883 58875009232219600846561325)
              ·
                refine ⟨22078128462082350317460497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 58875009232219600846561325 22078128462082350317460497)
                ·
                  refine ⟨16558596346561762738095373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22078128462082350317460497 16558596346561762738095373)
                  ·
                    refine ⟨6209473629960661026785765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16558596346561762738095373 6209473629960661026785765)
                    ·
                      refine ⟨1164276305617623942522331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6209473629960661026785765 1164276305617623942522331)
                      ·
                        rfl

theorem cell23_2267420_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 1, 3, 2, 3, 4].length) (baseStart_2267420 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267420 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267420 prefixEnd_2267420 := by exact prefixLift 2267420
  have htrace : WordTrace (prefixWord ++ tailWord_2267420) baseStart_2267420 baseEnd_2267420 := by
    simpa [prefixWord, tailWord_2267420, baseEnd_2267420] using wordTrace_append hprefix tailTrace_2267420
  have hstable : (prefixWord ++ tailWord_2267420).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267420).length < 2 ^ (prefixWord ++ tailWord_2267420).sum := by decide
  have hdescent : baseEnd_2267420 < baseStart_2267420 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267420) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267440 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 3]
def baseStart_2267440 : Nat := 118140960795 + 2267440 * 2 ^ 59
def prefixEnd_2267440 : Nat := 4983230072969 + 3 ^ 40 * 2267440 * 2
def baseEnd_2267440 : Nat := 1164286575230713864272239

theorem tailTrace_2267440 : CollatzResearch.WordTrace tailWord_2267440 prefixEnd_2267440 1164286575230713864272239 := by
  unfold tailWord_2267440
  simp only [CollatzResearch.WordTrace]
  refine ⟨41350165452729801383363887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55133553936973068511151849 41350165452729801383363887)
  ·
    refine ⟨62025248179094702075045831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41350165452729801383363887 62025248179094702075045831)
    ·
      refine ⟨93037872268642053112568747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62025248179094702075045831 93037872268642053112568747)
      ·
        refine ⟨139556808402963079668853121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93037872268642053112568747 139556808402963079668853121)
        ·
          refine ⟨104667606302222309751639841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139556808402963079668853121 104667606302222309751639841)
          ·
            refine ⟨78500704726666732313729881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104667606302222309751639841 78500704726666732313729881)
            ·
              refine ⟨58875528545000049235297411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78500704726666732313729881 58875528545000049235297411)
              ·
                refine ⟨88313292817500073852946117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58875528545000049235297411 88313292817500073852946117)
                ·
                  refine ⟨16558742403281263847427397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88313292817500073852946117 16558742403281263847427397)
                  ·
                    refine ⟨3104764200615236971392637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16558742403281263847427397 3104764200615236971392637)
                    ·
                      refine ⟨1164286575230713864272239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3104764200615236971392637 1164286575230713864272239)
                      ·
                        rfl

theorem cell23_2267440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 3].length) (baseStart_2267440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267440 prefixEnd_2267440 := by exact prefixLift 2267440
  have htrace : WordTrace (prefixWord ++ tailWord_2267440) baseStart_2267440 baseEnd_2267440 := by
    simpa [prefixWord, tailWord_2267440, baseEnd_2267440] using wordTrace_append hprefix tailTrace_2267440
  have hstable : (prefixWord ++ tailWord_2267440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267440).length < 2 ^ (prefixWord ++ tailWord_2267440).sum := by decide
  have hdescent : baseEnd_2267440 < baseStart_2267440 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267454 : List Nat := [4, 2, 1, 2, 1, 2, 1, 1, 3, 4, 2]
def baseStart_2267454 : Nat := 118140960795 + 2267454 * 2 ^ 59
def prefixEnd_2267454 : Nat := 4983230072969 + 3 ^ 40 * 2267454 * 2
def baseEnd_2267454 : Nat := 1164293763959876809497175

theorem tailTrace_2267454 : CollatzResearch.WordTrace tailWord_2267454 prefixEnd_2267454 1164293763959876809497175 := by
  unfold tailWord_2267454
  simp only [CollatzResearch.WordTrace]
  refine ⟨10337605190926110394717177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55133894351605922105158277 10337605190926110394717177)
  ·
    refine ⟨7753203893194582796037883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10337605190926110394717177 7753203893194582796037883)
    ·
      refine ⟨11629805839791874194056825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7753203893194582796037883 11629805839791874194056825)
      ·
        refine ⟨8722354379843905645542619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11629805839791874194056825 8722354379843905645542619)
        ·
          refine ⟨13083531569765858468313929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8722354379843905645542619 13083531569765858468313929)
          ·
            refine ⟨9812648677324393851235447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13083531569765858468313929 9812648677324393851235447)
            ·
              refine ⟨14718973015986590776853171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9812648677324393851235447 14718973015986590776853171)
              ·
                refine ⟨22078459523979886165279757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14718973015986590776853171 22078459523979886165279757)
                ·
                  refine ⟨8279422321492457311979909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22078459523979886165279757 8279422321492457311979909)
                  ·
                    refine ⟨1552391685279835745996233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8279422321492457311979909 1552391685279835745996233)
                    ·
                      refine ⟨1164293763959876809497175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1552391685279835745996233 1164293763959876809497175)
                      ·
                        rfl

theorem cell23_2267454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_2267454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267454 prefixEnd_2267454 := by exact prefixLift 2267454
  have htrace : WordTrace (prefixWord ++ tailWord_2267454) baseStart_2267454 baseEnd_2267454 := by
    simpa [prefixWord, tailWord_2267454, baseEnd_2267454] using wordTrace_append hprefix tailTrace_2267454
  have hstable : (prefixWord ++ tailWord_2267454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267454).length < 2 ^ (prefixWord ++ tailWord_2267454).sum := by decide
  have hdescent : baseEnd_2267454 < baseStart_2267454 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267497 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 2, 5, 2]
def baseStart_2267497 : Nat := 118140960795 + 2267497 * 2 ^ 59
def prefixEnd_2267497 : Nat := 4983230072969 + 3 ^ 40 * 2267497 * 2
def baseEnd_2267497 : Nat := 1164315843628020141259477

theorem tailTrace_2267497 : CollatzResearch.WordTrace tailWord_2267497 prefixEnd_2267497 1164315843628020141259477 := by
  unfold tailWord_2267497
  simp only [CollatzResearch.WordTrace]
  refine ⟨82702409866253101501552745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55134939910835401001035163 82702409866253101501552745)
  ·
    refine ⟨62026807399689826126164559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82702409866253101501552745 62026807399689826126164559)
    ·
      refine ⟨93040211099534739189246839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62026807399689826126164559 93040211099534739189246839)
      ·
        refine ⟨139560316649302108783870259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93040211099534739189246839 139560316649302108783870259)
        ·
          refine ⟨209340474973953163175805389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139560316649302108783870259 209340474973953163175805389)
          ·
            refine ⟨78502678115232436190927021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 209340474973953163175805389 78502678115232436190927021)
            ·
              refine ⟨29438504293212163571597633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78502678115232436190927021 29438504293212163571597633)
              ·
                refine ⟨22078878219909122678698225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29438504293212163571597633 22078878219909122678698225)
                ·
                  refine ⟨16559158664931842009023669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22078878219909122678698225 16559158664931842009023669)
                  ·
                    refine ⟨1552421124837360188345969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16559158664931842009023669 1552421124837360188345969)
                    ·
                      refine ⟨1164315843628020141259477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1552421124837360188345969 1164315843628020141259477)
                      ·
                        rfl

theorem cell23_2267497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 2, 5, 2].length) (baseStart_2267497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267497 prefixEnd_2267497 := by exact prefixLift 2267497
  have htrace : WordTrace (prefixWord ++ tailWord_2267497) baseStart_2267497 baseEnd_2267497 := by
    simpa [prefixWord, tailWord_2267497, baseEnd_2267497] using wordTrace_append hprefix tailTrace_2267497
  have hstable : (prefixWord ++ tailWord_2267497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267497).length < 2 ^ (prefixWord ++ tailWord_2267497).sum := by decide
  have hdescent : baseEnd_2267497 < baseStart_2267497 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267522 : List Nat := [3, 4, 2, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_2267522 : Nat := 118140960795 + 2267522 * 2 ^ 59
def prefixEnd_2267522 : Nat := 4983230072969 + 3 ^ 40 * 2267522 * 2
def baseEnd_2267522 : Nat := 1164328680644382543446863

theorem tailTrace_2267522 : CollatzResearch.WordTrace tailWord_2267522 prefixEnd_2267522 1164328680644382543446863 := by
  unfold tailWord_2267522
  simp only [CollatzResearch.WordTrace]
  refine ⟨20675830422790632692803205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55135547794108353847475213 20675830422790632692803205)
  ·
    refine ⟨3876718204273243629900601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20675830422790632692803205 3876718204273243629900601)
    ·
      refine ⟨2907538653204932722425451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3876718204273243629900601 2907538653204932722425451)
      ·
        refine ⟨4361307979807399083638177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2907538653204932722425451 4361307979807399083638177)
        ·
          refine ⟨3270980984855549312728633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4361307979807399083638177 3270980984855549312728633)
          ·
            refine ⟨2453235738641661984546475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3270980984855549312728633 2453235738641661984546475)
            ·
              refine ⟨3679853607962492976819713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2453235738641661984546475 3679853607962492976819713)
              ·
                refine ⟨2759890205971869732614785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3679853607962492976819713 2759890205971869732614785)
                ·
                  refine ⟨2069917654478902299461089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2759890205971869732614785 2069917654478902299461089)
                  ·
                    refine ⟨1552438240859176724595817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2069917654478902299461089 1552438240859176724595817)
                    ·
                      refine ⟨1164328680644382543446863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1552438240859176724595817 1164328680644382543446863)
                      ·
                        rfl

theorem cell23_2267522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_2267522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267522 prefixEnd_2267522 := by exact prefixLift 2267522
  have htrace : WordTrace (prefixWord ++ tailWord_2267522) baseStart_2267522 baseEnd_2267522 := by
    simpa [prefixWord, tailWord_2267522, baseEnd_2267522] using wordTrace_append hprefix tailTrace_2267522
  have hstable : (prefixWord ++ tailWord_2267522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267522).length < 2 ^ (prefixWord ++ tailWord_2267522).sum := by decide
  have hdescent : baseEnd_2267522 < baseStart_2267522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267527 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 4]
def baseStart_2267527 : Nat := 118140960795 + 2267527 * 2 ^ 59
def prefixEnd_2267527 : Nat := 4983230072969 + 3 ^ 40 * 2267527 * 2
def baseEnd_2267527 : Nat := 1164331248047655023884339

theorem tailTrace_2267527 : CollatzResearch.WordTrace tailWord_2267527 prefixEnd_2267527 1164331248047655023884339 := by
  unfold tailWord_2267527
  simp only [CollatzResearch.WordTrace]
  refine ⟨82703504056144416625144835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55135669370762944416763223 82703504056144416625144835)
  ·
    refine ⟨124055256084216624937717253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82703504056144416625144835 124055256084216624937717253)
    ·
      refine ⟨23260360515790617175821985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124055256084216624937717253 23260360515790617175821985)
      ·
        refine ⟨17445270386842962881866489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23260360515790617175821985 17445270386842962881866489)
        ·
          refine ⟨13083952790132222161399867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17445270386842962881866489 13083952790132222161399867)
          ·
            refine ⟨19625929185198333242099801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13083952790132222161399867 19625929185198333242099801)
            ·
              refine ⟨14719446888898749931574851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19625929185198333242099801 14719446888898749931574851)
              ·
                refine ⟨22079170333348124897362277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14719446888898749931574851 22079170333348124897362277)
                ·
                  refine ⟨4139844437502773418255427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22079170333348124897362277 4139844437502773418255427)
                  ·
                    refine ⟨6209766656254160127383141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4139844437502773418255427 6209766656254160127383141)
                    ·
                      refine ⟨1164331248047655023884339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6209766656254160127383141 1164331248047655023884339)
                      ·
                        rfl

theorem cell23_2267527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_2267527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267527 prefixEnd_2267527 := by exact prefixLift 2267527
  have htrace : WordTrace (prefixWord ++ tailWord_2267527) baseStart_2267527 baseEnd_2267527 := by
    simpa [prefixWord, tailWord_2267527, baseEnd_2267527] using wordTrace_append hprefix tailTrace_2267527
  have hstable : (prefixWord ++ tailWord_2267527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267527).length < 2 ^ (prefixWord ++ tailWord_2267527).sum := by decide
  have hdescent : baseEnd_2267527 < baseStart_2267527 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267554 : List Nat := [3, 3, 1, 2, 1, 1, 1, 4, 3, 4]
def baseStart_2267554 : Nat := 118140960795 + 2267554 * 2 ^ 59
def prefixEnd_2267554 : Nat := 4983230072969 + 3 ^ 40 * 2267554 * 2
def baseEnd_2267554 : Nat := 388115037341775472748905

theorem tailTrace_2267554 : CollatzResearch.WordTrace tailWord_2267554 prefixEnd_2267554 388115037341775472748905 := by
  unfold tailWord_2267554
  simp only [CollatzResearch.WordTrace]
  refine ⟨20676122206761650059094429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55136325884697733490918477 20676122206761650059094429)
  ·
    refine ⟨7753545827535618772160411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20676122206761650059094429 7753545827535618772160411)
    ·
      refine ⟨11630318741303428158240617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7753545827535618772160411 11630318741303428158240617)
      ·
        refine ⟨8722739055977571118680463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11630318741303428158240617 8722739055977571118680463)
        ·
          refine ⟨13084108583966356678020695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8722739055977571118680463 13084108583966356678020695)
          ·
            refine ⟨19626162875949535017031043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13084108583966356678020695 19626162875949535017031043)
            ·
              refine ⟨29439244313924302525546565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19626162875949535017031043 29439244313924302525546565)
              ·
                refine ⟨5519858308860806723539981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29439244313924302525546565 5519858308860806723539981)
                ·
                  refine ⟨2069946865822802521327493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5519858308860806723539981 2069946865822802521327493)
                  ·
                    refine ⟨388115037341775472748905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2069946865822802521327493 388115037341775472748905)
                    ·
                      rfl

theorem cell23_2267554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 4, 3, 4].length) (baseStart_2267554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267554 prefixEnd_2267554 := by exact prefixLift 2267554
  have htrace : WordTrace (prefixWord ++ tailWord_2267554) baseStart_2267554 baseEnd_2267554 := by
    simpa [prefixWord, tailWord_2267554, baseEnd_2267554] using wordTrace_append hprefix tailTrace_2267554
  have hstable : (prefixWord ++ tailWord_2267554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267554).length < 2 ^ (prefixWord ++ tailWord_2267554).sum := by decide
  have hdescent : baseEnd_2267554 < baseStart_2267554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267562 : List Nat := [3, 1, 6, 1, 2, 1, 1, 3, 5]
def baseStart_2267562 : Nat := 118140960795 + 2267562 * 2 ^ 59
def prefixEnd_2267562 : Nat := 4983230072969 + 3 ^ 40 * 2267562 * 2
def baseEnd_2267562 : Nat := 129372135541173598549631

theorem tailTrace_2267562 : CollatzResearch.WordTrace tailWord_2267562 prefixEnd_2267562 129372135541173598549631 := by
  unfold tailWord_2267562
  simp only [CollatzResearch.WordTrace]
  refine ⟨20676195152754404400667235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55136520407345078401779293 20676195152754404400667235)
  ·
    refine ⟨31014292729131606601000853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20676195152754404400667235 31014292729131606601000853)
    ·
      refine ⟨1453794971678044059421915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 31014292729131606601000853 1453794971678044059421915)
      ·
        refine ⟨2180692457517066089132873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1453794971678044059421915 2180692457517066089132873)
        ·
          refine ⟨1635519343137799566849655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2180692457517066089132873 1635519343137799566849655)
          ·
            refine ⟨2453279014706699350274483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1635519343137799566849655 2453279014706699350274483)
            ·
              refine ⟨3679918522060049025411725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2453279014706699350274483 3679918522060049025411725)
              ·
                refine ⟨1379969445772518384529397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3679918522060049025411725 1379969445772518384529397)
                ·
                  refine ⟨129372135541173598549631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1379969445772518384529397 129372135541173598549631)
                  ·
                    rfl

theorem cell23_2267562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 6, 1, 2, 1, 1, 3, 5].length) (baseStart_2267562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267562 prefixEnd_2267562 := by exact prefixLift 2267562
  have htrace : WordTrace (prefixWord ++ tailWord_2267562) baseStart_2267562 baseEnd_2267562 := by
    simpa [prefixWord, tailWord_2267562, baseEnd_2267562] using wordTrace_append hprefix tailTrace_2267562
  have hstable : (prefixWord ++ tailWord_2267562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267562).length < 2 ^ (prefixWord ++ tailWord_2267562).sum := by decide
  have hdescent : baseEnd_2267562 < baseStart_2267562 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267588 : List Nat := [2, 3, 3, 2, 2, 2, 1, 1, 3, 4]
def baseStart_2267588 : Nat := 118140960795 + 2267588 * 2 ^ 59
def prefixEnd_2267588 : Nat := 4983230072969 + 3 ^ 40 * 2267588 * 2
def baseEnd_2267588 : Nat := 388120856789193095073853

theorem tailTrace_2267588 : CollatzResearch.WordTrace tailWord_2267588 prefixEnd_2267588 388120856789193095073853 := by
  unfold tailWord_2267588
  simp only [CollatzResearch.WordTrace]
  refine ⟨41352864454461712021557709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55137152605948949362076945 41352864454461712021557709)
  ·
    refine ⟨15507324170423142008084141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41352864454461712021557709 15507324170423142008084141)
    ·
      refine ⟨5815246563908678253031553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15507324170423142008084141 5815246563908678253031553)
      ·
        refine ⟨4361434922931508689773665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5815246563908678253031553 4361434922931508689773665)
        ·
          refine ⟨3271076192198631517330249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4361434922931508689773665 3271076192198631517330249)
          ·
            refine ⟨2453307144148973637997687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3271076192198631517330249 2453307144148973637997687)
            ·
              refine ⟨3679960716223460456996531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2453307144148973637997687 3679960716223460456996531)
              ·
                refine ⟨5519941074335190685494797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3679960716223460456996531 5519941074335190685494797)
                ·
                  refine ⟨2069977902875696507060549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5519941074335190685494797 2069977902875696507060549)
                  ·
                    refine ⟨388120856789193095073853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2069977902875696507060549 388120856789193095073853)
                    ·
                      rfl

theorem cell23_2267588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 1, 3, 4].length) (baseStart_2267588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267588 prefixEnd_2267588 := by exact prefixLift 2267588
  have htrace : WordTrace (prefixWord ++ tailWord_2267588) baseStart_2267588 baseEnd_2267588 := by
    simpa [prefixWord, tailWord_2267588, baseEnd_2267588] using wordTrace_append hprefix tailTrace_2267588
  have hstable : (prefixWord ++ tailWord_2267588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267588).length < 2 ^ (prefixWord ++ tailWord_2267588).sum := by decide
  have hdescent : baseEnd_2267588 < baseStart_2267588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267627 : List Nat := [1, 1, 1, 1, 2, 3, 5, 2, 1, 6]
def baseStart_2267627 : Nat := 118140960795 + 2267627 * 2 ^ 59
def prefixEnd_2267627 : Nat := 4983230072969 + 3 ^ 40 * 2267627 * 2
def baseEnd_2267627 : Nat := 388127532037701544211293

theorem tailTrace_2267627 : CollatzResearch.WordTrace tailWord_2267627 prefixEnd_2267627 388127532037701544211293 := by
  unfold tailWord_2267627
  simp only [CollatzResearch.WordTrace]
  refine ⟨82707151355782133703785135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55138100903854755802523423 82707151355782133703785135)
  ·
    refine ⟨124060727033673200555677703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82707151355782133703785135 124060727033673200555677703)
    ·
      refine ⟨186091090550509800833516555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124060727033673200555677703 186091090550509800833516555)
      ·
        refine ⟨279136635825764701250274833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186091090550509800833516555 279136635825764701250274833)
        ·
          refine ⟨209352476869323525937706125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279136635825764701250274833 209352476869323525937706125)
          ·
            refine ⟨78507178825996322226639797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 209352476869323525937706125 78507178825996322226639797)
            ·
              refine ⟨7360048014937155208747481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 78507178825996322226639797 7360048014937155208747481)
              ·
                refine ⟨5520036011202866406560611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7360048014937155208747481 5520036011202866406560611)
                ·
                  refine ⟨8280054016804299609840917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5520036011202866406560611 8280054016804299609840917)
                  ·
                    refine ⟨388127532037701544211293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8280054016804299609840917 388127532037701544211293)
                    ·
                      rfl

theorem cell23_2267627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 5, 2, 1, 6].length) (baseStart_2267627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267627 prefixEnd_2267627 := by exact prefixLift 2267627
  have htrace : WordTrace (prefixWord ++ tailWord_2267627) baseStart_2267627 baseEnd_2267627 := by
    simpa [prefixWord, tailWord_2267627, baseEnd_2267627] using wordTrace_append hprefix tailTrace_2267627
  have hstable : (prefixWord ++ tailWord_2267627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267627).length < 2 ^ (prefixWord ++ tailWord_2267627).sum := by decide
  have hdescent : baseEnd_2267627 < baseStart_2267627 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267647 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 4]
def baseStart_2267647 : Nat := 118140960795 + 2267647 * 2 ^ 59
def prefixEnd_2267647 : Nat := 4983230072969 + 3 ^ 40 * 2267647 * 2
def baseEnd_2267647 : Nat := 1164392865726194554383787

theorem tailTrace_2267647 : CollatzResearch.WordTrace tailWord_2267647 prefixEnd_2267647 1164392865726194554383787 := by
  unfold tailWord_2267647
  simp only [CollatzResearch.WordTrace]
  refine ⟨82707880815709677119513195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55138587210473118079675463 82707880815709677119513195)
  ·
    refine ⟨124061821223564515679269793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82707880815709677119513195 124061821223564515679269793)
    ·
      refine ⟨93046365917673386759452345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124061821223564515679269793 93046365917673386759452345)
      ·
        refine ⟨69784774438255040069589259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93046365917673386759452345 69784774438255040069589259)
        ·
          refine ⟨104677161657382560104383889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69784774438255040069589259 104677161657382560104383889)
          ·
            refine ⟨78507871243036920078287917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104677161657382560104383889 78507871243036920078287917)
            ·
              refine ⟨29440451716138845029357969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 78507871243036920078287917 29440451716138845029357969)
              ·
                refine ⟨22080338787104133772018477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29440451716138845029357969 22080338787104133772018477)
                ·
                  refine ⟨8280127045164050164506929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22080338787104133772018477 8280127045164050164506929)
                  ·
                    refine ⟨6210095283873037623380197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8280127045164050164506929 6210095283873037623380197)
                    ·
                      refine ⟨1164392865726194554383787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6210095283873037623380197 1164392865726194554383787)
                      ·
                        rfl

theorem cell23_2267647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_2267647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267647 prefixEnd_2267647 := by exact prefixLift 2267647
  have htrace : WordTrace (prefixWord ++ tailWord_2267647) baseStart_2267647 baseEnd_2267647 := by
    simpa [prefixWord, tailWord_2267647, baseEnd_2267647] using wordTrace_append hprefix tailTrace_2267647
  have hstable : (prefixWord ++ tailWord_2267647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267647).length < 2 ^ (prefixWord ++ tailWord_2267647).sum := by decide
  have hdescent : baseEnd_2267647 < baseStart_2267647 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267651 : List Nat := [1, 1, 1, 3, 2, 1, 4, 3, 3, 2, 2]
def baseStart_2267651 : Nat := 118140960795 + 2267651 * 2 ^ 59
def prefixEnd_2267651 : Nat := 4983230072969 + 3 ^ 40 * 2267651 * 2
def baseEnd_2267651 : Nat := 1164394919648812538733769

theorem tailTrace_2267651 : CollatzResearch.WordTrace tailWord_2267651 prefixEnd_2267651 1164394919648812538733769 := by
  unfold tailWord_2267651
  simp only [CollatzResearch.WordTrace]
  refine ⟨82708026707695185802658807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55138684471796790535105871 82708026707695185802658807)
  ·
    refine ⟨124062040061542778703988211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82708026707695185802658807 124062040061542778703988211)
    ·
      refine ⟨186093060092314168055982317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124062040061542778703988211 186093060092314168055982317)
      ·
        refine ⟨69784897534617813020993369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 186093060092314168055982317 69784897534617813020993369)
        ·
          refine ⟨52338673150963359765745027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69784897534617813020993369 52338673150963359765745027)
          ·
            refine ⟨78508009726445039648617541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52338673150963359765745027 78508009726445039648617541)
            ·
              refine ⟨14720251823708444934115789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78508009726445039648617541 14720251823708444934115789)
              ·
                refine ⟨5520094433890666850293421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14720251823708444934115789 5520094433890666850293421)
                ·
                  refine ⟨2070035412709000068860033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5520094433890666850293421 2070035412709000068860033)
                  ·
                    refine ⟨1552526559531750051645025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2070035412709000068860033 1552526559531750051645025)
                    ·
                      refine ⟨1164394919648812538733769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1552526559531750051645025 1164394919648812538733769)
                      ·
                        rfl

theorem cell23_2267651_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 4, 3, 3, 2, 2].length) (baseStart_2267651 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267651 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267651 prefixEnd_2267651 := by exact prefixLift 2267651
  have htrace : WordTrace (prefixWord ++ tailWord_2267651) baseStart_2267651 baseEnd_2267651 := by
    simpa [prefixWord, tailWord_2267651, baseEnd_2267651] using wordTrace_append hprefix tailTrace_2267651
  have hstable : (prefixWord ++ tailWord_2267651).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267651).length < 2 ^ (prefixWord ++ tailWord_2267651).sum := by decide
  have hdescent : baseEnd_2267651 < baseStart_2267651 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267651) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267688 : List Nat := [2, 1, 5, 2, 1, 2, 1, 3, 1, 2, 3]
def baseStart_2267688 : Nat := 118140960795 + 2267688 * 2 ^ 59
def prefixEnd_2267688 : Nat := 4983230072969 + 3 ^ 40 * 2267688 * 2
def baseEnd_2267688 : Nat := 1164413918433028893971099

theorem tailTrace_2267688 : CollatzResearch.WordTrace tailWord_2267688 prefixEnd_2267688 1164413918433028893971099 := by
  unfold tailWord_2267688
  simp only [CollatzResearch.WordTrace]
  refine ⟨41354688104280570560877859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55139584139040760747837145 41354688104280570560877859)
  ·
    refine ⟨62032032156420855841316789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41354688104280570560877859 62032032156420855841316789)
    ·
      refine ⟨5815503014664455235123449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62032032156420855841316789 5815503014664455235123449)
      ·
        refine ⟨4361627260998341426342587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5815503014664455235123449 4361627260998341426342587)
        ·
          refine ⟨6542440891497512139513881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4361627260998341426342587 6542440891497512139513881)
          ·
            refine ⟨4906830668623134104635411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6542440891497512139513881 4906830668623134104635411)
            ·
              refine ⟨7360246002934701156953117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4906830668623134104635411 7360246002934701156953117)
              ·
                refine ⟨2760092251100512933857419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7360246002934701156953117 2760092251100512933857419)
                ·
                  refine ⟨4140138376650769400786129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2760092251100512933857419 4140138376650769400786129)
                  ·
                    refine ⟨3105103782488077050589597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4140138376650769400786129 3105103782488077050589597)
                    ·
                      refine ⟨1164413918433028893971099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3105103782488077050589597 1164413918433028893971099)
                      ·
                        rfl

theorem cell23_2267688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 1, 2, 3].length) (baseStart_2267688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267688 prefixEnd_2267688 := by exact prefixLift 2267688
  have htrace : WordTrace (prefixWord ++ tailWord_2267688) baseStart_2267688 baseEnd_2267688 := by
    simpa [prefixWord, tailWord_2267688, baseEnd_2267688] using wordTrace_append hprefix tailTrace_2267688
  have hstable : (prefixWord ++ tailWord_2267688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267688).length < 2 ^ (prefixWord ++ tailWord_2267688).sum := by decide
  have hdescent : baseEnd_2267688 < baseStart_2267688 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267701 : List Nat := [1, 3, 3, 1, 1, 2, 3, 1, 4, 1, 3]
def baseStart_2267701 : Nat := 118140960795 + 2267701 * 2 ^ 59
def prefixEnd_2267701 : Nat := 4983230072969 + 3 ^ 40 * 2267701 * 2
def baseEnd_2267701 : Nat := 1164420593681537343108539

theorem tailTrace_2267701 : CollatzResearch.WordTrace tailWord_2267701 prefixEnd_2267701 1164420593681537343108539 := by
  unfold tailWord_2267701
  simp only [CollatzResearch.WordTrace]
  refine ⟨82709850357514044341978957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55139900238342696227985971 82709850357514044341978957)
  ·
    refine ⟨31016193884067766628242109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82709850357514044341978957 31016193884067766628242109)
    ·
      refine ⟨11631072706525412485590791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31016193884067766628242109 11631072706525412485590791)
      ·
        refine ⟨17446609059788118728386187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11631072706525412485590791 17446609059788118728386187)
        ·
          refine ⟨26169913589682178092579281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17446609059788118728386187 26169913589682178092579281)
          ·
            refine ⟨19627435192261633569434461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26169913589682178092579281 19627435192261633569434461)
            ·
              refine ⟨7360288197098112588537923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19627435192261633569434461 7360288197098112588537923)
              ·
                refine ⟨11040432295647168882806885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7360288197098112588537923 11040432295647168882806885)
                ·
                  refine ⟨2070081055433844165526291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11040432295647168882806885 2070081055433844165526291)
                  ·
                    refine ⟨3105121583150766248289437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2070081055433844165526291 3105121583150766248289437)
                    ·
                      refine ⟨1164420593681537343108539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3105121583150766248289437 1164420593681537343108539)
                      ·
                        rfl

theorem cell23_2267701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 4, 1, 3].length) (baseStart_2267701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267701 prefixEnd_2267701 := by exact prefixLift 2267701
  have htrace : WordTrace (prefixWord ++ tailWord_2267701) baseStart_2267701 baseEnd_2267701 := by
    simpa [prefixWord, tailWord_2267701, baseEnd_2267701] using wordTrace_append hprefix tailTrace_2267701
  have hstable : (prefixWord ++ tailWord_2267701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267701).length < 2 ^ (prefixWord ++ tailWord_2267701).sum := by decide
  have hdescent : baseEnd_2267701 < baseStart_2267701 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267702 : List Nat := [5, 1, 2, 1, 2, 1, 2, 4, 1, 2, 2]
def baseStart_2267702 : Nat := 118140960795 + 2267702 * 2 ^ 59
def prefixEnd_2267702 : Nat := 4983230072969 + 3 ^ 40 * 2267702 * 2
def baseEnd_2267702 : Nat := 1164421107162191839196035

theorem tailTrace_2267702 : CollatzResearch.WordTrace tailWord_2267702 prefixEnd_2267702 1164421107162191839196035 := by
  unfold tailWord_2267702
  simp only [CollatzResearch.WordTrace]
  refine ⟨5169367926906901344547835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55139924553673614341843573 5169367926906901344547835)
  ·
    refine ⟨7754051890360352016821753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5169367926906901344547835 7754051890360352016821753)
    ·
      refine ⟨5815538917770264012616315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7754051890360352016821753 5815538917770264012616315)
      ·
        refine ⟨8723308376655396018924473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5815538917770264012616315 8723308376655396018924473)
        ·
          refine ⟨6542481282491547014193355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8723308376655396018924473 6542481282491547014193355)
          ·
            refine ⟨9813721923737320521290033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6542481282491547014193355 9813721923737320521290033)
            ·
              refine ⟨7360291442802990390967525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9813721923737320521290033 7360291442802990390967525)
              ·
                refine ⟨1380054645525560698306411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7360291442802990390967525 1380054645525560698306411)
                ·
                  refine ⟨2070081968288341047459617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1380054645525560698306411 2070081968288341047459617)
                  ·
                    refine ⟨1552561476216255785594713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2070081968288341047459617 1552561476216255785594713)
                    ·
                      refine ⟨1164421107162191839196035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1552561476216255785594713 1164421107162191839196035)
                      ·
                        rfl

theorem cell23_2267702_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 2, 4, 1, 2, 2].length) (baseStart_2267702 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267702 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267702 prefixEnd_2267702 := by exact prefixLift 2267702
  have htrace : WordTrace (prefixWord ++ tailWord_2267702) baseStart_2267702 baseEnd_2267702 := by
    simpa [prefixWord, tailWord_2267702, baseEnd_2267702] using wordTrace_append hprefix tailTrace_2267702
  have hstable : (prefixWord ++ tailWord_2267702).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267702).length < 2 ^ (prefixWord ++ tailWord_2267702).sum := by decide
  have hdescent : baseEnd_2267702 < baseStart_2267702 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267702) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267707 : List Nat := [1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 4]
def baseStart_2267707 : Nat := 118140960795 + 2267707 * 2 ^ 59
def prefixEnd_2267707 : Nat := 4983230072969 + 3 ^ 40 * 2267707 * 2
def baseEnd_2267707 : Nat := 1164423674565464319633511

theorem tailTrace_2267707 : CollatzResearch.WordTrace tailWord_2267707 prefixEnd_2267707 1164423674565464319633511 := by
  unfold tailWord_2267707
  simp only [CollatzResearch.WordTrace]
  refine ⟨82710069195492307366697375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55140046130328204911131583 82710069195492307366697375)
  ·
    refine ⟨124065103793238461050046063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82710069195492307366697375 124065103793238461050046063)
    ·
      refine ⟨186097655689857691575069095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124065103793238461050046063 186097655689857691575069095)
      ·
        refine ⟨279146483534786537362603643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186097655689857691575069095 279146483534786537362603643)
        ·
          refine ⟨418719725302179806043905465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279146483534786537362603643 418719725302179806043905465)
          ·
            refine ⟨314039793976634854532929099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 418719725302179806043905465 314039793976634854532929099)
            ·
              refine ⟨471059690964952281799393649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314039793976634854532929099 471059690964952281799393649)
              ·
                refine ⟨353294768223714211349545237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 471059690964952281799393649 353294768223714211349545237)
                ·
                  refine ⟨16560692260486603657009933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 353294768223714211349545237 16560692260486603657009933)
                  ·
                    refine ⟨6210259597682476371378725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16560692260486603657009933 6210259597682476371378725)
                    ·
                      refine ⟨1164423674565464319633511, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6210259597682476371378725 1164423674565464319633511)
                      ·
                        rfl

theorem cell23_2267707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 4].length) (baseStart_2267707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267707 prefixEnd_2267707 := by exact prefixLift 2267707
  have htrace : WordTrace (prefixWord ++ tailWord_2267707) baseStart_2267707 baseEnd_2267707 := by
    simpa [prefixWord, tailWord_2267707, baseEnd_2267707] using wordTrace_append hprefix tailTrace_2267707
  have hstable : (prefixWord ++ tailWord_2267707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267707).length < 2 ^ (prefixWord ++ tailWord_2267707).sum := by decide
  have hdescent : baseEnd_2267707 < baseStart_2267707 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267815 : List Nat := [1, 1, 6, 3, 1, 1, 1, 4, 5]
def baseStart_2267815 : Nat := 118140960795 + 2267815 * 2 ^ 59
def prefixEnd_2267815 : Nat := 4983230072969 + 3 ^ 40 * 2267815 * 2
def baseEnd_2267815 : Nat := 129386570052905544120335

theorem tailTrace_2267815 : CollatzResearch.WordTrace tailWord_2267815 prefixEnd_2267815 129386570052905544120335 := by
  unfold tailWord_2267815
  simp only [CollatzResearch.WordTrace]
  refine ⟨82714008279101041811628899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55142672186067361207752599 82714008279101041811628899)
  ·
    refine ⟨124071012418651562717443349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82714008279101041811628899 124071012418651562717443349)
    ·
      refine ⟨5815828707124292002380157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 124071012418651562717443349 5815828707124292002380157)
      ·
        refine ⟨2180935765171609500892559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5815828707124292002380157 2180935765171609500892559)
        ·
          refine ⟨3271403647757414251338839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2180935765171609500892559 3271403647757414251338839)
          ·
            refine ⟨4907105471636121377008259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3271403647757414251338839 4907105471636121377008259)
            ·
              refine ⟨7360658207454182065512389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4907105471636121377008259 7360658207454182065512389)
              ·
                refine ⟨1380123413897659137283573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7360658207454182065512389 1380123413897659137283573)
                ·
                  refine ⟨129386570052905544120335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1380123413897659137283573 129386570052905544120335)
                  ·
                    rfl

theorem cell23_2267815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 1, 4, 5].length) (baseStart_2267815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267815 prefixEnd_2267815 := by exact prefixLift 2267815
  have htrace : WordTrace (prefixWord ++ tailWord_2267815) baseStart_2267815 baseEnd_2267815 := by
    simpa [prefixWord, tailWord_2267815, baseEnd_2267815] using wordTrace_append hprefix tailTrace_2267815
  have hstable : (prefixWord ++ tailWord_2267815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267815).length < 2 ^ (prefixWord ++ tailWord_2267815).sum := by decide
  have hdescent : baseEnd_2267815 < baseStart_2267815 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267821 : List Nat := [1, 5, 2, 1, 1, 2, 2, 1, 1, 2, 5]
def baseStart_2267821 : Nat := 118140960795 + 2267821 * 2 ^ 59
def prefixEnd_2267821 : Nat := 4983230072969 + 3 ^ 40 * 2267821 * 2
def baseEnd_2267821 : Nat := 1164482211360076873607987

theorem tailTrace_2267821 : CollatzResearch.WordTrace tailWord_2267821 prefixEnd_2267821 1164482211360076873607987 := by
  unfold tailWord_2267821
  simp only [CollatzResearch.WordTrace]
  refine ⟨82714227117079304836347317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55142818078052869890898211 82714227117079304836347317)
  ·
    refine ⟨7754458792226184828407561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82714227117079304836347317 7754458792226184828407561)
    ·
      refine ⟨5815844094169638621305671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7754458792226184828407561 5815844094169638621305671)
      ·
        refine ⟨8723766141254457931958507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5815844094169638621305671 8723766141254457931958507)
        ·
          refine ⟨13085649211881686897937761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8723766141254457931958507 13085649211881686897937761)
          ·
            refine ⟨9814236908911265173453321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13085649211881686897937761 9814236908911265173453321)
            ·
              refine ⟨7360677681683448880089991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9814236908911265173453321 7360677681683448880089991)
              ·
                refine ⟨11041016522525173320134987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7360677681683448880089991 11041016522525173320134987)
                ·
                  refine ⟨16561524783787759980202481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11041016522525173320134987 16561524783787759980202481)
                  ·
                    refine ⟨12421143587840819985151861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16561524783787759980202481 12421143587840819985151861)
                    ·
                      refine ⟨1164482211360076873607987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12421143587840819985151861 1164482211360076873607987)
                      ·
                        rfl

theorem cell23_2267821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 1, 2, 5].length) (baseStart_2267821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267821 prefixEnd_2267821 := by exact prefixLift 2267821
  have htrace : WordTrace (prefixWord ++ tailWord_2267821) baseStart_2267821 baseEnd_2267821 := by
    simpa [prefixWord, tailWord_2267821, baseEnd_2267821] using wordTrace_append hprefix tailTrace_2267821
  have hstable : (prefixWord ++ tailWord_2267821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267821).length < 2 ^ (prefixWord ++ tailWord_2267821).sum := by decide
  have hdescent : baseEnd_2267821 < baseStart_2267821 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267848 : List Nat := [2, 1, 3, 1, 2, 5, 1, 1, 2, 1, 4]
def baseStart_2267848 : Nat := 118140960795 + 2267848 * 2 ^ 59
def prefixEnd_2267848 : Nat := 4983230072969 + 3 ^ 40 * 2267848 * 2
def baseEnd_2267848 : Nat := 1164496075337748267970363

theorem tailTrace_2267848 : CollatzResearch.WordTrace tailWord_2267848 prefixEnd_2267848 1164496075337748267970363 := by
  unfold tailWord_2267848
  simp only [CollatzResearch.WordTrace]
  refine ⟨41357605943990744223790099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55143474591987658965053465 41357605943990744223790099)
  ·
    refine ⟨62036408915986116335685149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41357605943990744223790099 62036408915986116335685149)
    ·
      refine ⟨23263653343494793625881931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62036408915986116335685149 23263653343494793625881931)
      ·
        refine ⟨34895480015242190438822897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23263653343494793625881931 34895480015242190438822897)
        ·
          refine ⟨26171610011431642829117173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34895480015242190438822897 26171610011431642829117173)
          ·
            refine ⟨2453588438571716515229735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26171610011431642829117173 2453588438571716515229735)
            ·
              refine ⟨3680382657857574772844603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2453588438571716515229735 3680382657857574772844603)
              ·
                refine ⟨5520573986786362159266905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3680382657857574772844603 5520573986786362159266905)
                ·
                  refine ⟨4140430490089771619450179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5520573986786362159266905 4140430490089771619450179)
                  ·
                    refine ⟨6210645735134657429175269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4140430490089771619450179 6210645735134657429175269)
                    ·
                      refine ⟨1164496075337748267970363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6210645735134657429175269 1164496075337748267970363)
                      ·
                        rfl

theorem cell23_2267848_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 2, 1, 4].length) (baseStart_2267848 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267848 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267848 prefixEnd_2267848 := by exact prefixLift 2267848
  have htrace : WordTrace (prefixWord ++ tailWord_2267848) baseStart_2267848 baseEnd_2267848 := by
    simpa [prefixWord, tailWord_2267848, baseEnd_2267848] using wordTrace_append hprefix tailTrace_2267848
  have hstable : (prefixWord ++ tailWord_2267848).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267848).length < 2 ^ (prefixWord ++ tailWord_2267848).sum := by decide
  have hdescent : baseEnd_2267848 < baseStart_2267848 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267848) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267871 : List Nat := [1, 1, 2, 3, 2, 3, 3, 2, 6]
def baseStart_2267871 : Nat := 118140960795 + 2267871 * 2 ^ 59
def prefixEnd_2267871 : Nat := 4983230072969 + 3 ^ 40 * 2267871 * 2
def baseEnd_2267871 : Nat := 129389765043644630886973

theorem tailTrace_2267871 : CollatzResearch.WordTrace tailWord_2267871 prefixEnd_2267871 129389765043644630886973 := by
  unfold tailWord_2267871
  simp only [CollatzResearch.WordTrace]
  refine ⟨82716050766898163375667467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55144033844598775583778311 82716050766898163375667467)
  ·
    refine ⟨124074076150347245063501201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82716050766898163375667467 124074076150347245063501201)
    ·
      refine ⟨93055557112760433797625901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124074076150347245063501201 93055557112760433797625901)
      ·
        refine ⟨34895833917285162674109713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93055557112760433797625901 34895833917285162674109713)
        ·
          refine ⟨26171875437963872005582285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34895833917285162674109713 26171875437963872005582285)
          ·
            refine ⟨9814453289236452002093357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26171875437963872005582285 9814453289236452002093357)
            ·
              refine ⟨3680419983463669500785009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9814453289236452002093357 3680419983463669500785009)
              ·
                refine ⟨2760314987597752125588757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3680419983463669500785009 2760314987597752125588757)
                ·
                  refine ⟨129389765043644630886973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2760314987597752125588757 129389765043644630886973)
                  ·
                    rfl

theorem cell23_2267871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 2, 6].length) (baseStart_2267871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267871 prefixEnd_2267871 := by exact prefixLift 2267871
  have htrace : WordTrace (prefixWord ++ tailWord_2267871) baseStart_2267871 baseEnd_2267871 := by
    simpa [prefixWord, tailWord_2267871, baseEnd_2267871] using wordTrace_append hprefix tailTrace_2267871
  have hstable : (prefixWord ++ tailWord_2267871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267871).length < 2 ^ (prefixWord ++ tailWord_2267871).sum := by decide
  have hdescent : baseEnd_2267871 < baseStart_2267871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267875 : List Nat := [1, 1, 1, 7, 1, 1, 2, 4, 1, 4]
def baseStart_2267875 : Nat := 118140960795 + 2267875 * 2 ^ 59
def prefixEnd_2267875 : Nat := 4983230072969 + 3 ^ 40 * 2267875 * 2
def baseEnd_2267875 : Nat := 388169979771806554110913

theorem tailTrace_2267875 : CollatzResearch.WordTrace tailWord_2267875 prefixEnd_2267875 388169979771806554110913 := by
  unfold tailWord_2267875
  simp only [CollatzResearch.WordTrace]
  refine ⟨82716196658883672058813079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55144131105922448039208719 82716196658883672058813079)
  ·
    refine ⟨124074294988325508088219619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82716196658883672058813079 124074294988325508088219619)
    ·
      refine ⟨186111442482488262132329429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124074294988325508088219619 186111442482488262132329429)
      ·
        refine ⟨4361986933183318643726471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 186111442482488262132329429 4361986933183318643726471)
        ·
          refine ⟨6542980399774977965589707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4361986933183318643726471 6542980399774977965589707)
          ·
            refine ⟨9814470599662466948384561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6542980399774977965589707 9814470599662466948384561)
            ·
              refine ⟨7360852949746850211288421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9814470599662466948384561 7360852949746850211288421)
              ·
                refine ⟨1380159928077534414616579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7360852949746850211288421 1380159928077534414616579)
                ·
                  refine ⟨2070239892116301621924869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1380159928077534414616579 2070239892116301621924869)
                  ·
                    refine ⟨388169979771806554110913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2070239892116301621924869 388169979771806554110913)
                    ·
                      rfl

theorem cell23_2267875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 4, 1, 4].length) (baseStart_2267875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267875 prefixEnd_2267875 := by exact prefixLift 2267875
  have htrace : WordTrace (prefixWord ++ tailWord_2267875) baseStart_2267875 baseEnd_2267875 := by
    simpa [prefixWord, tailWord_2267875, baseEnd_2267875] using wordTrace_append hprefix tailTrace_2267875
  have hstable : (prefixWord ++ tailWord_2267875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267875).length < 2 ^ (prefixWord ++ tailWord_2267875).sum := by decide
  have hdescent : baseEnd_2267875 < baseStart_2267875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267898 : List Nat := [3, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3]
def baseStart_2267898 : Nat := 118140960795 + 2267898 * 2 ^ 59
def prefixEnd_2267898 : Nat := 4983230072969 + 3 ^ 40 * 2267898 * 2
def baseEnd_2267898 : Nat := 1164521749370473072345133

theorem tailTrace_2267898 : CollatzResearch.WordTrace tailWord_2267898 prefixEnd_2267898 1164521749370473072345133 := by
  unfold tailWord_2267898
  simp only [CollatzResearch.WordTrace]
  refine ⟨20679258884450086746725087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55144690358533564657933565 20679258884450086746725087)
  ·
    refine ⟨31018888326675130120087631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20679258884450086746725087 31018888326675130120087631)
    ·
      refine ⟨46528332490012695180131447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31018888326675130120087631 46528332490012695180131447)
      ·
        refine ⟨69792498735019042770197171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46528332490012695180131447 69792498735019042770197171)
        ·
          refine ⟨104688748102528564155295757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69792498735019042770197171 104688748102528564155295757)
          ·
            refine ⟨39258280538448211558235909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104688748102528564155295757 39258280538448211558235909)
            ·
              refine ⟨7360927600959039667169233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39258280538448211558235909 7360927600959039667169233)
              ·
                refine ⟨5520695700719279750376925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7360927600959039667169233 5520695700719279750376925)
                ·
                  refine ⟨2070260887769729906391347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5520695700719279750376925 2070260887769729906391347)
                  ·
                    refine ⟨3105391331654594859587021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2070260887769729906391347 3105391331654594859587021)
                    ·
                      refine ⟨1164521749370473072345133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3105391331654594859587021 1164521749370473072345133)
                      ·
                        rfl

theorem cell23_2267898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3].length) (baseStart_2267898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267898 prefixEnd_2267898 := by exact prefixLift 2267898
  have htrace : WordTrace (prefixWord ++ tailWord_2267898) baseStart_2267898 baseEnd_2267898 := by
    simpa [prefixWord, tailWord_2267898, baseEnd_2267898] using wordTrace_append hprefix tailTrace_2267898
  have hstable : (prefixWord ++ tailWord_2267898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267898).length < 2 ^ (prefixWord ++ tailWord_2267898).sum := by decide
  have hdescent : baseEnd_2267898 < baseStart_2267898 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267908 : List Nat := [2, 3, 2, 2, 1, 1, 1, 3, 1, 5, 2]
def baseStart_2267908 : Nat := 118140960795 + 2267908 * 2 ^ 59
def prefixEnd_2267908 : Nat := 4983230072969 + 3 ^ 40 * 2267908 * 2
def baseEnd_2267908 : Nat := 1164526884177018033220087

theorem tailTrace_2267908 : CollatzResearch.WordTrace tailWord_2267908 prefixEnd_2267908 1164526884177018033220087 := by
  unfold tailWord_2267908
  simp only [CollatzResearch.WordTrace]
  refine ⟨41358700133882059347382189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55144933511842745796509585 41358700133882059347382189)
  ·
    refine ⟨15509512550205772255268321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41358700133882059347382189 15509512550205772255268321)
    ·
      refine ⟨11632134412654329191451241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15509512550205772255268321 11632134412654329191451241)
      ·
        refine ⟨8724100809490746893588431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11632134412654329191451241 8724100809490746893588431)
        ·
          refine ⟨13086151214236120340382647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8724100809490746893588431 13086151214236120340382647)
          ·
            refine ⟨19629226821354180510573971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13086151214236120340382647 19629226821354180510573971)
            ·
              refine ⟨29443840232031270765860957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19629226821354180510573971 29443840232031270765860957)
              ·
                refine ⟨11041440087011726537197859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29443840232031270765860957 11041440087011726537197859)
                ·
                  refine ⟨16562160130517589805796789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11041440087011726537197859 16562160130517589805796789)
                  ·
                    refine ⟨1552702512236024044293449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16562160130517589805796789 1552702512236024044293449)
                    ·
                      refine ⟨1164526884177018033220087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1552702512236024044293449 1164526884177018033220087)
                      ·
                        rfl

theorem cell23_2267908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 1, 5, 2].length) (baseStart_2267908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267908 prefixEnd_2267908 := by exact prefixLift 2267908
  have htrace : WordTrace (prefixWord ++ tailWord_2267908) baseStart_2267908 baseEnd_2267908 := by
    simpa [prefixWord, tailWord_2267908, baseEnd_2267908] using wordTrace_append hprefix tailTrace_2267908
  have hstable : (prefixWord ++ tailWord_2267908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267908).length < 2 ^ (prefixWord ++ tailWord_2267908).sum := by decide
  have hdescent : baseEnd_2267908 < baseStart_2267908 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267941 : List Nat := [1, 3, 1, 2, 3, 1, 1, 4, 1, 1, 5]
def baseStart_2267941 : Nat := 118140960795 + 2267941 * 2 ^ 59
def prefixEnd_2267941 : Nat := 4983230072969 + 3 ^ 40 * 2267941 * 2
def baseEnd_2267941 : Nat := 1164543829038616404107435

theorem tailTrace_2267941 : CollatzResearch.WordTrace tailWord_2267941 prefixEnd_2267941 1164543829038616404107435 := by
  unfold tailWord_2267941
  simp only [CollatzResearch.WordTrace]
  refine ⟨82718603876644565330715677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55145735917763043553810451 82718603876644565330715677)
  ·
    refine ⟨31019476453741711999018379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82718603876644565330715677 31019476453741711999018379)
    ·
      refine ⟨46529214680612567998527569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31019476453741711999018379 46529214680612567998527569)
      ·
        refine ⟨34896911010459425998895677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46529214680612567998527569 34896911010459425998895677)
        ·
          refine ⟨13086341628922284749585879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34896911010459425998895677 13086341628922284749585879)
          ·
            refine ⟨19629512443383427124378819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13086341628922284749585879 19629512443383427124378819)
            ·
              refine ⟨29444268665075140686568229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19629512443383427124378819 29444268665075140686568229)
              ·
                refine ⟨5520800374701588878731543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29444268665075140686568229 5520800374701588878731543)
                ·
                  refine ⟨8281200562052383318097315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5520800374701588878731543 8281200562052383318097315)
                  ·
                    refine ⟨12421800843078574977145973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8281200562052383318097315 12421800843078574977145973)
                    ·
                      refine ⟨1164543829038616404107435, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12421800843078574977145973 1164543829038616404107435)
                      ·
                        rfl

theorem cell23_2267941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_2267941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267941 prefixEnd_2267941 := by exact prefixLift 2267941
  have htrace : WordTrace (prefixWord ++ tailWord_2267941) baseStart_2267941 baseEnd_2267941 := by
    simpa [prefixWord, tailWord_2267941, baseEnd_2267941] using wordTrace_append hprefix tailTrace_2267941
  have hstable : (prefixWord ++ tailWord_2267941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267941).length < 2 ^ (prefixWord ++ tailWord_2267941).sum := by decide
  have hdescent : baseEnd_2267941 < baseStart_2267941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267948 : List Nat := [2, 2, 1, 1, 1, 4, 3, 3, 2, 4]
def baseStart_2267948 : Nat := 118140960795 + 2267948 * 2 ^ 59
def prefixEnd_2267948 : Nat := 4983230072969 + 3 ^ 40 * 2267948 * 2
def baseEnd_2267948 : Nat := 388182474467732625573301

theorem tailTrace_2267948 : CollatzResearch.WordTrace tailWord_2267948 prefixEnd_2267948 388182474467732625573301 := by
  unfold tailWord_2267948
  simp only [CollatzResearch.WordTrace]
  refine ⟨41359429593809602763110249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55145906125079470350813665 41359429593809602763110249)
  ·
    refine ⟨31019572195357202072332687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41359429593809602763110249 31019572195357202072332687)
    ·
      refine ⟨46529358293035803108499031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31019572195357202072332687 46529358293035803108499031)
      ·
        refine ⟨69794037439553704662748547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46529358293035803108499031 69794037439553704662748547)
        ·
          refine ⟨104691056159330556994122821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69794037439553704662748547 104691056159330556994122821)
          ·
            refine ⟨19629573029874479436398029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104691056159330556994122821 19629573029874479436398029)
            ·
              refine ⟨7361089886202929788649261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19629573029874479436398029 7361089886202929788649261)
              ·
                refine ⟨2760408707326098670743473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7361089886202929788649261 2760408707326098670743473)
                ·
                  refine ⟨2070306530494574003057605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2760408707326098670743473 2070306530494574003057605)
                  ·
                    refine ⟨388182474467732625573301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2070306530494574003057605 388182474467732625573301)
                    ·
                      rfl

theorem cell23_2267948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 4].length) (baseStart_2267948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267948 prefixEnd_2267948 := by exact prefixLift 2267948
  have htrace : WordTrace (prefixWord ++ tailWord_2267948) baseStart_2267948 baseEnd_2267948 := by
    simpa [prefixWord, tailWord_2267948, baseEnd_2267948] using wordTrace_append hprefix tailTrace_2267948
  have hstable : (prefixWord ++ tailWord_2267948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267948).length < 2 ^ (prefixWord ++ tailWord_2267948).sum := by decide
  have hdescent : baseEnd_2267948 < baseStart_2267948 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267955 : List Nat := [1, 1, 1, 2, 6, 3, 1, 2, 1, 1, 4]
def baseStart_2267955 : Nat := 118140960795 + 2267955 * 2 ^ 59
def prefixEnd_2267955 : Nat := 4983230072969 + 3 ^ 40 * 2267955 * 2
def baseEnd_2267955 : Nat := 1164551017767779349332371

theorem tailTrace_2267955 : CollatzResearch.WordTrace tailWord_2267955 prefixEnd_2267955 1164551017767779349332371 := by
  unfold tailWord_2267955
  simp only [CollatzResearch.WordTrace]
  refine ⟨82719114498593845721725319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55146076332395897147816879 82719114498593845721725319)
  ·
    refine ⟨124078671747890768582587979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82719114498593845721725319 124078671747890768582587979)
    ·
      refine ⟨186118007621836152873881969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124078671747890768582587979 186118007621836152873881969)
      ·
        refine ⟨139588505716377114655411477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186118007621836152873881969 139588505716377114655411477)
        ·
          refine ⟨6543211205455177249472413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 139588505716377114655411477 6543211205455177249472413)
          ·
            refine ⟨2453704202045691468552155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6543211205455177249472413 2453704202045691468552155)
            ·
              refine ⟨3680556303068537202828233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2453704202045691468552155 3680556303068537202828233)
              ·
                refine ⟨2760417227301402902121175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3680556303068537202828233 2760417227301402902121175)
                ·
                  refine ⟨4140625840952104353181763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2760417227301402902121175 4140625840952104353181763)
                  ·
                    refine ⟨6210938761428156529772645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4140625840952104353181763 6210938761428156529772645)
                    ·
                      refine ⟨1164551017767779349332371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6210938761428156529772645 1164551017767779349332371)
                      ·
                        rfl

theorem cell23_2267955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 1, 1, 4].length) (baseStart_2267955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267955 prefixEnd_2267955 := by exact prefixLift 2267955
  have htrace : WordTrace (prefixWord ++ tailWord_2267955) baseStart_2267955 baseEnd_2267955 := by
    simpa [prefixWord, tailWord_2267955, baseEnd_2267955] using wordTrace_append hprefix tailTrace_2267955
  have hstable : (prefixWord ++ tailWord_2267955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267955).length < 2 ^ (prefixWord ++ tailWord_2267955).sum := by decide
  have hdescent : baseEnd_2267955 < baseStart_2267955 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2267991 : List Nat := [1, 1, 3, 2, 4, 1, 1, 1, 2, 7]
def baseStart_2267991 : Nat := 118140960795 + 2267991 * 2 ^ 59
def prefixEnd_2267991 : Nat := 4983230072969 + 3 ^ 40 * 2267991 * 2
def baseEnd_2267991 : Nat := 388189834357113736160735

theorem tailTrace_2267991 : CollatzResearch.WordTrace tailWord_2267991 prefixEnd_2267991 388189834357113736160735 := by
  unfold tailWord_2267991
  simp only [CollatzResearch.WordTrace]
  refine ⟨82720427526463423870035827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55146951684308949246690551 82720427526463423870035827)
  ·
    refine ⟨124080641289695135805053741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82720427526463423870035827 124080641289695135805053741)
    ·
      refine ⟨46530240483635675926895153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124080641289695135805053741 46530240483635675926895153)
      ·
        refine ⟨34897680362726756945171365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46530240483635675926895153 34897680362726756945171365)
        ·
          refine ⟨6543315068011266927219631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34897680362726756945171365 6543315068011266927219631)
          ·
            refine ⟨9814972602016900390829447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6543315068011266927219631 9814972602016900390829447)
            ·
              refine ⟨14722458903025350586244171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9814972602016900390829447 14722458903025350586244171)
              ·
                refine ⟨22083688354538025879366257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14722458903025350586244171 22083688354538025879366257)
                ·
                  refine ⟨16562766265903519409524693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22083688354538025879366257 16562766265903519409524693)
                  ·
                    refine ⟨388189834357113736160735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16562766265903519409524693 388189834357113736160735)
                    ·
                      rfl

theorem cell23_2267991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 1, 1, 2, 7].length) (baseStart_2267991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2267991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2267991 prefixEnd_2267991 := by exact prefixLift 2267991
  have htrace : WordTrace (prefixWord ++ tailWord_2267991) baseStart_2267991 baseEnd_2267991 := by
    simpa [prefixWord, tailWord_2267991, baseEnd_2267991] using wordTrace_append hprefix tailTrace_2267991
  have hstable : (prefixWord ++ tailWord_2267991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2267991).length < 2 ^ (prefixWord ++ tailWord_2267991).sum := by decide
  have hdescent : baseEnd_2267991 < baseStart_2267991 := by decide
  rcases family_descends (prefixWord ++ tailWord_2267991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268005 : List Nat := [1, 3, 1, 3, 1, 1, 4, 3, 2, 1, 3]
def baseStart_2268005 : Nat := 118140960795 + 2268005 * 2 ^ 59
def prefixEnd_2268005 : Nat := 4983230072969 + 3 ^ 40 * 2268005 * 2
def baseEnd_2268005 : Nat := 1164576691800504153707141

theorem tailTrace_2268005 : CollatzResearch.WordTrace tailWord_2268005 prefixEnd_2268005 1164576691800504153707141 := by
  unfold tailWord_2268005
  simp only [CollatzResearch.WordTrace]
  refine ⟨82720938148412704261045469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55147292098941802840696979 82720938148412704261045469)
  ·
    refine ⟨31020351805654764097892051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82720938148412704261045469 31020351805654764097892051)
    ·
      refine ⟨46530527708482146146838077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31020351805654764097892051 46530527708482146146838077)
      ·
        refine ⟨17448947890680804805064279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46530527708482146146838077 17448947890680804805064279)
        ·
          refine ⟨26173421836021207207596419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17448947890680804805064279 26173421836021207207596419)
          ·
            refine ⟨39260132754031810811394629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26173421836021207207596419 39260132754031810811394629)
            ·
              refine ⟨7361274891380964527136493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39260132754031810811394629 7361274891380964527136493)
              ·
                refine ⟨2760478084267861697676185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7361274891380964527136493 2760478084267861697676185)
                ·
                  refine ⟨2070358563200896273257139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2760478084267861697676185 2070358563200896273257139)
                  ·
                    refine ⟨3105537844801344409885709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2070358563200896273257139 3105537844801344409885709)
                    ·
                      refine ⟨1164576691800504153707141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3105537844801344409885709 1164576691800504153707141)
                      ·
                        rfl

theorem cell23_2268005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_2268005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268005 prefixEnd_2268005 := by exact prefixLift 2268005
  have htrace : WordTrace (prefixWord ++ tailWord_2268005) baseStart_2268005 baseEnd_2268005 := by
    simpa [prefixWord, tailWord_2268005, baseEnd_2268005] using wordTrace_append hprefix tailTrace_2268005
  have hstable : (prefixWord ++ tailWord_2268005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268005).length < 2 ^ (prefixWord ++ tailWord_2268005).sum := by decide
  have hdescent : baseEnd_2268005 < baseStart_2268005 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268031 : List Nat := [1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 5]
def baseStart_2268031 : Nat := 118140960795 + 2268031 * 2 ^ 59
def prefixEnd_2268031 : Nat := 4983230072969 + 3 ^ 40 * 2268031 * 2
def baseEnd_2268031 : Nat := 1164590042297521051982021

theorem tailTrace_2268031 : CollatzResearch.WordTrace tailWord_2268031 prefixEnd_2268031 1164590042297521051982021 := by
  unfold tailWord_2268031
  simp only [CollatzResearch.WordTrace]
  refine ⟨82721886446318510701491947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55147924297545673800994631 82721886446318510701491947)
  ·
    refine ⟨124082829669477766052237921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82721886446318510701491947 124082829669477766052237921)
    ·
      refine ⟨93062122252108324539178441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124082829669477766052237921 93062122252108324539178441)
      ·
        refine ⟨69796591689081243404383831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93062122252108324539178441 69796591689081243404383831)
        ·
          refine ⟨104694887533621865106575747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69796591689081243404383831 104694887533621865106575747)
          ·
            refine ⟨157042331300432797659863621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104694887533621865106575747 157042331300432797659863621)
            ·
              refine ⟨29445437118831149561224429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 157042331300432797659863621 29445437118831149561224429)
              ·
                refine ⟨11042038919561681085459161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29445437118831149561224429 11042038919561681085459161)
                ·
                  refine ⟨8281529189671260814094371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11042038919561681085459161 8281529189671260814094371)
                  ·
                    refine ⟨12422293784506891221141557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8281529189671260814094371 12422293784506891221141557)
                    ·
                      refine ⟨1164590042297521051982021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12422293784506891221141557 1164590042297521051982021)
                      ·
                        rfl

theorem cell23_2268031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_2268031 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268031 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268031 prefixEnd_2268031 := by exact prefixLift 2268031
  have htrace : WordTrace (prefixWord ++ tailWord_2268031) baseStart_2268031 baseEnd_2268031 := by
    simpa [prefixWord, tailWord_2268031, baseEnd_2268031] using wordTrace_append hprefix tailTrace_2268031
  have hstable : (prefixWord ++ tailWord_2268031).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268031).length < 2 ^ (prefixWord ++ tailWord_2268031).sum := by decide
  have hdescent : baseEnd_2268031 < baseStart_2268031 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268108 : List Nat := [2, 2, 1, 4, 1, 1, 3, 1, 1, 2, 5]
def baseStart_2268108 : Nat := 118140960795 + 2268108 * 2 ^ 59
def prefixEnd_2268108 : Nat := 4983230072969 + 3 ^ 40 * 2268108 * 2
def baseEnd_2268108 : Nat := 1164629580307917250719167

theorem tailTrace_2268108 : CollatzResearch.WordTrace tailWord_2268108 prefixEnd_2268108 1164629580307917250719167 := by
  unfold tailWord_2268108
  simp only [CollatzResearch.WordTrace]
  refine ⟨41362347433519776426022489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55149796578026368568029985 41362347433519776426022489)
  ·
    refine ⟨31021760575139832319516867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41362347433519776426022489 31021760575139832319516867)
    ·
      refine ⟨46532640862709748479275301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31021760575139832319516867 46532640862709748479275301)
      ·
        refine ⟨8724870161758077839864119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46532640862709748479275301 8724870161758077839864119)
        ·
          refine ⟨13087305242637116759796179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8724870161758077839864119 13087305242637116759796179)
          ·
            refine ⟨19630957863955675139694269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13087305242637116759796179 19630957863955675139694269)
            ·
              refine ⟨7361609198983378177385351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19630957863955675139694269 7361609198983378177385351)
              ·
                refine ⟨11042413798475067266078027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7361609198983378177385351 11042413798475067266078027)
                ·
                  refine ⟨16563620697712600899117041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11042413798475067266078027 16563620697712600899117041)
                  ·
                    refine ⟨12422715523284450674337781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16563620697712600899117041 12422715523284450674337781)
                    ·
                      refine ⟨1164629580307917250719167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12422715523284450674337781 1164629580307917250719167)
                      ·
                        rfl

theorem cell23_2268108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 1, 2, 5].length) (baseStart_2268108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268108 prefixEnd_2268108 := by exact prefixLift 2268108
  have htrace : WordTrace (prefixWord ++ tailWord_2268108) baseStart_2268108 baseEnd_2268108 := by
    simpa [prefixWord, tailWord_2268108, baseEnd_2268108] using wordTrace_append hprefix tailTrace_2268108
  have hstable : (prefixWord ++ tailWord_2268108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268108).length < 2 ^ (prefixWord ++ tailWord_2268108).sum := by decide
  have hdescent : baseEnd_2268108 < baseStart_2268108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268135 : List Nat := [1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_2268135 : Nat := 118140960795 + 2268135 * 2 ^ 59
def prefixEnd_2268135 : Nat := 4983230072969 + 3 ^ 40 * 2268135 * 2
def baseEnd_2268135 : Nat := 1164643444285588645081543

theorem tailTrace_2268135 : CollatzResearch.WordTrace tailWord_2268135 prefixEnd_2268135 1164643444285588645081543 := by
  unfold tailWord_2268135
  simp only [CollatzResearch.WordTrace]
  refine ⟨82725679637941736463277859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55150453091961157642185239 82725679637941736463277859)
  ·
    refine ⟨124088519456912604694916789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82725679637941736463277859 124088519456912604694916789)
    ·
      refine ⟨11633298699085556690148449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124088519456912604694916789 11633298699085556690148449)
      ·
        refine ⟨8724974024314167517611337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11633298699085556690148449 8724974024314167517611337)
        ·
          refine ⟨6543730518235625638208503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8724974024314167517611337 6543730518235625638208503)
          ·
            refine ⟨9815595777353438457312755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6543730518235625638208503 9815595777353438457312755)
            ·
              refine ⟨14723393666030157685969133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9815595777353438457312755 14723393666030157685969133)
              ·
                refine ⟨5521272624761309132238425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14723393666030157685969133 5521272624761309132238425)
                ·
                  refine ⟨4140954468570981849178819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5521272624761309132238425 4140954468570981849178819)
                  ·
                    refine ⟨6211431702856472773768229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4140954468570981849178819 6211431702856472773768229)
                    ·
                      refine ⟨1164643444285588645081543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6211431702856472773768229 1164643444285588645081543)
                      ·
                        rfl

theorem cell23_2268135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_2268135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268135 prefixEnd_2268135 := by exact prefixLift 2268135
  have htrace : WordTrace (prefixWord ++ tailWord_2268135) baseStart_2268135 baseEnd_2268135 := by
    simpa [prefixWord, tailWord_2268135, baseEnd_2268135] using wordTrace_append hprefix tailTrace_2268135
  have hstable : (prefixWord ++ tailWord_2268135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268135).length < 2 ^ (prefixWord ++ tailWord_2268135).sum := by decide
  have hdescent : baseEnd_2268135 < baseStart_2268135 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268185 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 5, 1, 3]
def baseStart_2268185 : Nat := 118140960795 + 2268185 * 2 ^ 59
def prefixEnd_2268185 : Nat := 4983230072969 + 3 ^ 40 * 2268185 * 2
def baseEnd_2268185 : Nat := 1164669118318313449456313

theorem tailTrace_2268185 : CollatzResearch.WordTrace tailWord_2268185 prefixEnd_2268185 1164669118318313449456313 := by
  unfold tailWord_2268185
  simp only [CollatzResearch.WordTrace]
  refine ⟨82727503287760595002598009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55151668858507063335065339 82727503287760595002598009)
  ·
    refine ⟨62045627465820446251948507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82727503287760595002598009 62045627465820446251948507)
    ·
      refine ⟨93068441198730669377922761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62045627465820446251948507 93068441198730669377922761)
      ·
        refine ⟨69801330899048002033442071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93068441198730669377922761 69801330899048002033442071)
        ·
          refine ⟨104701996348572003050163107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69801330899048002033442071 104701996348572003050163107)
          ·
            refine ⟨157052994522858004575244661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104701996348572003050163107 157052994522858004575244661)
            ·
              refine ⟨14723718236517937928929187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 157052994522858004575244661 14723718236517937928929187)
              ·
                refine ⟨22085577354776906893393781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14723718236517937928929187 22085577354776906893393781)
                ·
                  refine ⟨2070522877010335021255667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22085577354776906893393781 2070522877010335021255667)
                  ·
                    refine ⟨3105784315515502531883501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2070522877010335021255667 3105784315515502531883501)
                    ·
                      refine ⟨1164669118318313449456313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3105784315515502531883501 1164669118318313449456313)
                      ·
                        rfl

theorem cell23_2268185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 5, 1, 3].length) (baseStart_2268185 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268185 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268185 prefixEnd_2268185 := by exact prefixLift 2268185
  have htrace : WordTrace (prefixWord ++ tailWord_2268185) baseStart_2268185 baseEnd_2268185 := by
    simpa [prefixWord, tailWord_2268185, baseEnd_2268185] using wordTrace_append hprefix tailTrace_2268185
  have hstable : (prefixWord ++ tailWord_2268185).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268185).length < 2 ^ (prefixWord ++ tailWord_2268185).sum := by decide
  have hdescent : baseEnd_2268185 < baseStart_2268185 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268189 : List Nat := [1, 4, 2, 2, 3, 2, 1, 1, 2, 2, 3]
def baseStart_2268189 : Nat := 118140960795 + 2268189 * 2 ^ 59
def prefixEnd_2268189 : Nat := 4983230072969 + 3 ^ 40 * 2268189 * 2
def baseEnd_2268189 : Nat := 1164671172240931433806295

theorem tailTrace_2268189 : CollatzResearch.WordTrace tailWord_2268189 prefixEnd_2268189 1164671172240931433806295 := by
  unfold tailWord_2268189
  simp only [CollatzResearch.WordTrace]
  refine ⟨82727649179746103685743621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55151766119830735790495747 82727649179746103685743621)
  ·
    refine ⟨15511434221202394441076929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82727649179746103685743621 15511434221202394441076929)
    ·
      refine ⟨11633575665901795830807697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15511434221202394441076929 11633575665901795830807697)
      ·
        refine ⟨8725181749426346873105773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11633575665901795830807697 8725181749426346873105773)
        ·
          refine ⟨3271943156034880077414665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8725181749426346873105773 3271943156034880077414665)
          ·
            refine ⟨2453957367026160058060999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3271943156034880077414665 2453957367026160058060999)
            ·
              refine ⟨3680936050539240087091499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2453957367026160058060999 3680936050539240087091499)
              ·
                refine ⟨5521404075808860130637249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3680936050539240087091499 5521404075808860130637249)
                ·
                  refine ⟨4141053056856645097977937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5521404075808860130637249 4141053056856645097977937)
                  ·
                    refine ⟨3105789792642483823483453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4141053056856645097977937 3105789792642483823483453)
                    ·
                      refine ⟨1164671172240931433806295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3105789792642483823483453 1164671172240931433806295)
                      ·
                        rfl

theorem cell23_2268189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 2, 2, 3].length) (baseStart_2268189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268189 prefixEnd_2268189 := by exact prefixLift 2268189
  have htrace : WordTrace (prefixWord ++ tailWord_2268189) baseStart_2268189 baseEnd_2268189 := by
    simpa [prefixWord, tailWord_2268189, baseEnd_2268189] using wordTrace_append hprefix tailTrace_2268189
  have hstable : (prefixWord ++ tailWord_2268189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268189).length < 2 ^ (prefixWord ++ tailWord_2268189).sum := by decide
  have hdescent : baseEnd_2268189 < baseStart_2268189 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268218 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 3, 6]
def baseStart_2268218 : Nat := 118140960795 + 2268218 * 2 ^ 59
def prefixEnd_2268218 : Nat := 4983230072969 + 3 ^ 40 * 2268218 * 2
def baseEnd_2268218 : Nat := 388228687726637273447887

theorem tailTrace_2268218 : CollatzResearch.WordTrace tailWord_2268218 prefixEnd_2268218 388228687726637273447887 := by
  unfold tailWord_2268218
  simp only [CollatzResearch.WordTrace]
  refine ⟨20682176724160260409637327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55152471264427361092366205 20682176724160260409637327)
  ·
    refine ⟨31023265086240390614455991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20682176724160260409637327 31023265086240390614455991)
    ·
      refine ⟨46534897629360585921683987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31023265086240390614455991 46534897629360585921683987)
      ·
        refine ⟨69802346444040878882525981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46534897629360585921683987 69802346444040878882525981)
        ·
          refine ⟨26175879916515329580947243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69802346444040878882525981 26175879916515329580947243)
          ·
            refine ⟨39263819874772994371420865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26175879916515329580947243 39263819874772994371420865)
            ·
              refine ⟨29447864906079745778565649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39263819874772994371420865 29447864906079745778565649)
              ·
                refine ⟨22085898679559809333924237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29447864906079745778565649 22085898679559809333924237)
                ·
                  refine ⟨8282212004834928500221589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22085898679559809333924237 8282212004834928500221589)
                  ·
                    refine ⟨388228687726637273447887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8282212004834928500221589 388228687726637273447887)
                    ·
                      rfl

theorem cell23_2268218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 3, 6].length) (baseStart_2268218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268218 prefixEnd_2268218 := by exact prefixLift 2268218
  have htrace : WordTrace (prefixWord ++ tailWord_2268218) baseStart_2268218 baseEnd_2268218 := by
    simpa [prefixWord, tailWord_2268218, baseEnd_2268218] using wordTrace_append hprefix tailTrace_2268218
  have hstable : (prefixWord ++ tailWord_2268218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268218).length < 2 ^ (prefixWord ++ tailWord_2268218).sum := by decide
  have hdescent : baseEnd_2268218 < baseStart_2268218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268242 : List Nat := [3, 2, 2, 1, 3, 1, 1, 4, 1, 1, 4]
def baseStart_2268242 : Nat := 118140960795 + 2268242 * 2 ^ 59
def prefixEnd_2268242 : Nat := 4983230072969 + 3 ^ 40 * 2268242 * 2
def baseEnd_2268242 : Nat := 1164698386715619726443551

theorem tailTrace_2268242 : CollatzResearch.WordTrace tailWord_2268242 prefixEnd_2268242 1164698386715619726443551 := by
  unfold tailWord_2268242
  simp only [CollatzResearch.WordTrace]
  refine ⟨20682395562138523434355745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55153054832369395824948653 20682395562138523434355745)
  ·
    refine ⟨15511796671603892575766809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20682395562138523434355745 15511796671603892575766809)
    ·
      refine ⟨11633847503702919431825107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15511796671603892575766809 11633847503702919431825107)
      ·
        refine ⟨17450771255554379147737661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11633847503702919431825107 17450771255554379147737661)
        ·
          refine ⟨6544039220832892180401623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17450771255554379147737661 6544039220832892180401623)
          ·
            refine ⟨9816058831249338270602435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6544039220832892180401623 9816058831249338270602435)
            ·
              refine ⟨14724088246874007405903653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9816058831249338270602435 14724088246874007405903653)
              ·
                refine ⟨2760766546288876388606935, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14724088246874007405903653 2760766546288876388606935)
                ·
                  refine ⟨4141149819433314582910403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2760766546288876388606935 4141149819433314582910403)
                  ·
                    refine ⟨6211724729149971874365605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4141149819433314582910403 6211724729149971874365605)
                    ·
                      refine ⟨1164698386715619726443551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6211724729149971874365605 1164698386715619726443551)
                      ·
                        rfl

theorem cell23_2268242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 1, 1, 4].length) (baseStart_2268242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268242 prefixEnd_2268242 := by exact prefixLift 2268242
  have htrace : WordTrace (prefixWord ++ tailWord_2268242) baseStart_2268242 baseEnd_2268242 := by
    simpa [prefixWord, tailWord_2268242, baseEnd_2268242] using wordTrace_append hprefix tailTrace_2268242
  have hstable : (prefixWord ++ tailWord_2268242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268242).length < 2 ^ (prefixWord ++ tailWord_2268242).sum := by decide
  have hdescent : baseEnd_2268242 < baseStart_2268242 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268248 : List Nat := [2, 1, 2, 2, 1, 3, 3, 9]
def baseStart_2268248 : Nat := 118140960795 + 2268248 * 2 ^ 59
def prefixEnd_2268248 : Nat := 4983230072969 + 3 ^ 40 * 2268248 * 2
def baseEnd_2268248 : Nat := 43137091392575803813649

theorem tailTrace_2268248 : CollatzResearch.WordTrace tailWord_2268248 prefixEnd_2268248 43137091392575803813649 := by
  unfold tailWord_2268248
  simp only [CollatzResearch.WordTrace]
  refine ⟨41364900543266178381070699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55153200724354904508094265 41364900543266178381070699)
  ·
    refine ⟨62047350814899267571606049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41364900543266178381070699 62047350814899267571606049)
    ·
      refine ⟨46535513111174450678704537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62047350814899267571606049 46535513111174450678704537)
      ·
        refine ⟨34901634833380838009028403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46535513111174450678704537 34901634833380838009028403)
        ·
          refine ⟨52352452250071257013542605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34901634833380838009028403 52352452250071257013542605)
          ·
            refine ⟨19632169593776721380078477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52352452250071257013542605 19632169593776721380078477)
            ·
              refine ⟨7362063597666270517529429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19632169593776721380078477 7362063597666270517529429)
              ·
                refine ⟨43137091392575803813649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 7362063597666270517529429 43137091392575803813649)
                ·
                  rfl

theorem cell23_2268248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 9].length) (baseStart_2268248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268248 prefixEnd_2268248 := by exact prefixLift 2268248
  have htrace : WordTrace (prefixWord ++ tailWord_2268248) baseStart_2268248 baseEnd_2268248 := by
    simpa [prefixWord, tailWord_2268248, baseEnd_2268248] using wordTrace_append hprefix tailTrace_2268248
  have hstable : (prefixWord ++ tailWord_2268248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268248).length < 2 ^ (prefixWord ++ tailWord_2268248).sum := by decide
  have hdescent : baseEnd_2268248 < baseStart_2268248 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268296 : List Nat := [2, 1, 3, 4, 2, 2, 1, 2, 1, 2, 3]
def baseStart_2268296 : Nat := 118140960795 + 2268296 * 2 ^ 59
def prefixEnd_2268296 : Nat := 4983230072969 + 3 ^ 40 * 2268296 * 2
def baseEnd_2268296 : Nat := 1164726114670962515168303

theorem tailTrace_2268296 : CollatzResearch.WordTrace tailWord_2268296 prefixEnd_2268296 1164726114670962515168303 := by
  unfold tailWord_2268296
  simp only [CollatzResearch.WordTrace]
  refine ⟨41365775895179230479944371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55154367860238973973259161 41365775895179230479944371)
  ·
    refine ⟨62048663842768845719916557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41365775895179230479944371 62048663842768845719916557)
    ·
      refine ⟨23268248941038317144968709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62048663842768845719916557 23268248941038317144968709)
      ·
        refine ⟨4362796676444684464681633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23268248941038317144968709 4362796676444684464681633)
        ·
          refine ⟨3272097507333513348511225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4362796676444684464681633 3272097507333513348511225)
          ·
            refine ⟨2454073130500135011383419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3272097507333513348511225 2454073130500135011383419)
            ·
              refine ⟨3681109695750202517075129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2454073130500135011383419 3681109695750202517075129)
              ·
                refine ⟨2760832271812651887806347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3681109695750202517075129 2760832271812651887806347)
                ·
                  refine ⟨4141248407718977831709521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2760832271812651887806347 4141248407718977831709521)
                  ·
                    refine ⟨3105936305789233373782141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4141248407718977831709521 3105936305789233373782141)
                    ·
                      refine ⟨1164726114670962515168303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3105936305789233373782141 1164726114670962515168303)
                      ·
                        rfl

theorem cell23_2268296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_2268296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268296 prefixEnd_2268296 := by exact prefixLift 2268296
  have htrace : WordTrace (prefixWord ++ tailWord_2268296) baseStart_2268296 baseEnd_2268296 := by
    simpa [prefixWord, tailWord_2268296, baseEnd_2268296] using wordTrace_append hprefix tailTrace_2268296
  have hstable : (prefixWord ++ tailWord_2268296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268296).length < 2 ^ (prefixWord ++ tailWord_2268296).sum := by decide
  have hdescent : baseEnd_2268296 < baseStart_2268296 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268335 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 2, 4, 3]
def baseStart_2268335 : Nat := 118140960795 + 2268335 * 2 ^ 59
def prefixEnd_2268335 : Nat := 4983230072969 + 3 ^ 40 * 2268335 * 2
def baseEnd_2268335 : Nat := 1164746140416487862580623

theorem tailTrace_2268335 : CollatzResearch.WordTrace tailWord_2268335 prefixEnd_2268335 1164746140416487862580623 := by
  unfold tailWord_2268335
  simp only [CollatzResearch.WordTrace]
  refine ⟨82732974237217170620558459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55155316158144780413705639 82732974237217170620558459)
  ·
    refine ⟨124099461355825755930837689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82732974237217170620558459 124099461355825755930837689)
    ·
      refine ⟨93074596016869316948128267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124099461355825755930837689 93074596016869316948128267)
      ·
        refine ⟨139611894025303975422192401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93074596016869316948128267 139611894025303975422192401)
        ·
          refine ⟨104708920518977981566644301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139611894025303975422192401 104708920518977981566644301)
          ·
            refine ⟨39265845194616743087491613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104708920518977981566644301 39265845194616743087491613)
            ·
              refine ⟨14724691947981278657809355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39265845194616743087491613 14724691947981278657809355)
              ·
                refine ⟨22087037921971917986714033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14724691947981278657809355 22087037921971917986714033)
                ·
                  refine ⟨16565278441478938490035525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22087037921971917986714033 16565278441478938490035525)
                  ·
                    refine ⟨3105989707777300966881661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16565278441478938490035525 3105989707777300966881661)
                    ·
                      refine ⟨1164746140416487862580623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3105989707777300966881661 1164746140416487862580623)
                      ·
                        rfl

theorem cell23_2268335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4, 3].length) (baseStart_2268335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268335 prefixEnd_2268335 := by exact prefixLift 2268335
  have htrace : WordTrace (prefixWord ++ tailWord_2268335) baseStart_2268335 baseEnd_2268335 := by
    simpa [prefixWord, tailWord_2268335, baseEnd_2268335] using wordTrace_append hprefix tailTrace_2268335
  have hstable : (prefixWord ++ tailWord_2268335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268335).length < 2 ^ (prefixWord ++ tailWord_2268335).sum := by decide
  have hdescent : baseEnd_2268335 < baseStart_2268335 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268345 : List Nat := [1, 2, 1, 4, 1, 3, 1, 1, 1, 4, 4]
def baseStart_2268345 : Nat := 118140960795 + 2268345 * 2 ^ 59
def prefixEnd_2268345 : Nat := 4983230072969 + 3 ^ 40 * 2268345 * 2
def baseEnd_2268345 : Nat := 1164751275223032823455577

theorem tailTrace_2268345 : CollatzResearch.WordTrace tailWord_2268345 prefixEnd_2268345 1164751275223032823455577 := by
  unfold tailWord_2268345
  simp only [CollatzResearch.WordTrace]
  refine ⟨82733338967180942328422489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55155559311453961552281659 82733338967180942328422489)
  ·
    refine ⟨62050004225385706746316867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82733338967180942328422489 62050004225385706746316867)
    ·
      refine ⟨93075006338078560119475301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62050004225385706746316867 93075006338078560119475301)
      ·
        refine ⟨17451563688389730022401619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93075006338078560119475301 17451563688389730022401619)
        ·
          refine ⟨26177345532584595033602429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17451563688389730022401619 26177345532584595033602429)
          ·
            refine ⟨9816504574719223137600911, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26177345532584595033602429 9816504574719223137600911)
            ·
              refine ⟨14724756862078834706401367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9816504574719223137600911 14724756862078834706401367)
              ·
                refine ⟨22087135293118252059602051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14724756862078834706401367 22087135293118252059602051)
                ·
                  refine ⟨33130702939677378089403077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22087135293118252059602051 33130702939677378089403077)
                  ·
                    refine ⟨6212006801189508391763077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33130702939677378089403077 6212006801189508391763077)
                    ·
                      refine ⟨1164751275223032823455577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6212006801189508391763077 1164751275223032823455577)
                      ·
                        rfl

theorem cell23_2268345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_2268345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268345 prefixEnd_2268345 := by exact prefixLift 2268345
  have htrace : WordTrace (prefixWord ++ tailWord_2268345) baseStart_2268345 baseEnd_2268345 := by
    simpa [prefixWord, tailWord_2268345, baseEnd_2268345] using wordTrace_append hprefix tailTrace_2268345
  have hstable : (prefixWord ++ tailWord_2268345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268345).length < 2 ^ (prefixWord ++ tailWord_2268345).sum := by decide
  have hdescent : baseEnd_2268345 < baseStart_2268345 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268446 : List Nat := [4, 3, 2, 1, 2, 1, 1, 1, 1, 2, 5]
def baseStart_2268446 : Nat := 118140960795 + 2268446 * 2 ^ 59
def prefixEnd_2268446 : Nat := 4983230072969 + 3 ^ 40 * 2268446 * 2
def baseEnd_2268446 : Nat := 1164803136769136928292613

theorem tailTrace_2268446 : CollatzResearch.WordTrace tailWord_2268446 prefixEnd_2268446 1164803136769136928292613 := by
  unfold tailWord_2268446
  simp only [CollatzResearch.WordTrace]
  refine ⟨10342127842476879572231149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55158015159876691051899461 10342127842476879572231149)
  ·
    refine ⟨3878297940928829839586681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10342127842476879572231149 3878297940928829839586681)
    ·
      refine ⟨2908723455696622379690011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3878297940928829839586681 2908723455696622379690011)
      ·
        refine ⟨4363085183544933569535017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2908723455696622379690011 4363085183544933569535017)
        ·
          refine ⟨3272313887658700177151263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4363085183544933569535017 3272313887658700177151263)
          ·
            refine ⟨4908470831488050265726895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3272313887658700177151263 4908470831488050265726895)
            ·
              refine ⟨7362706247232075398590343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4908470831488050265726895 7362706247232075398590343)
              ·
                refine ⟨11044059370848113097885515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7362706247232075398590343 11044059370848113097885515)
                ·
                  refine ⟨16566089056272169646828273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11044059370848113097885515 16566089056272169646828273)
                  ·
                    refine ⟨12424566792204127235121205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16566089056272169646828273 12424566792204127235121205)
                    ·
                      refine ⟨1164803136769136928292613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12424566792204127235121205 1164803136769136928292613)
                      ·
                        rfl

theorem cell23_2268446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 1, 2, 5].length) (baseStart_2268446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268446 prefixEnd_2268446 := by exact prefixLift 2268446
  have htrace : WordTrace (prefixWord ++ tailWord_2268446) baseStart_2268446 baseEnd_2268446 := by
    simpa [prefixWord, tailWord_2268446, baseEnd_2268446] using wordTrace_append hprefix tailTrace_2268446
  have hstable : (prefixWord ++ tailWord_2268446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268446).length < 2 ^ (prefixWord ++ tailWord_2268446).sum := by decide
  have hdescent : baseEnd_2268446 < baseStart_2268446 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268485 : List Nat := [1, 3, 1, 1, 1, 2, 1, 2, 1, 3, 7]
def baseStart_2268485 : Nat := 118140960795 + 2268485 * 2 ^ 59
def prefixEnd_2268485 : Nat := 4983230072969 + 3 ^ 40 * 2268485 * 2
def baseEnd_2268485 : Nat := 1164823162514662275704933

theorem tailTrace_2268485 : CollatzResearch.WordTrace tailWord_2268485 prefixEnd_2268485 1164823162514662275704933 := by
  unfold tailWord_2268485
  simp only [CollatzResearch.WordTrace]
  refine ⟨82738445186673746238518909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55158963457782497492345939 82738445186673746238518909)
  ·
    refine ⟨31026916945002654839444591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82738445186673746238518909 31026916945002654839444591)
    ·
      refine ⟨46540375417503982259166887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31026916945002654839444591 46540375417503982259166887)
      ·
        refine ⟨69810563126255973388750331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46540375417503982259166887 69810563126255973388750331)
        ·
          refine ⟨104715844689383960083125497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69810563126255973388750331 104715844689383960083125497)
          ·
            refine ⟨78536883517037970062344123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104715844689383960083125497 78536883517037970062344123)
            ·
              refine ⟨117805325275556955093516185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78536883517037970062344123 117805325275556955093516185)
              ·
                refine ⟨88353993956667716320137139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 117805325275556955093516185 88353993956667716320137139)
                ·
                  refine ⟨132530990935001574480205709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 88353993956667716320137139 132530990935001574480205709)
                  ·
                    refine ⟨49699121600625590430077141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 132530990935001574480205709 49699121600625590430077141)
                    ·
                      refine ⟨1164823162514662275704933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49699121600625590430077141 1164823162514662275704933)
                      ·
                        rfl

theorem cell23_2268485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_2268485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268485 prefixEnd_2268485 := by exact prefixLift 2268485
  have htrace : WordTrace (prefixWord ++ tailWord_2268485) baseStart_2268485 baseEnd_2268485 := by
    simpa [prefixWord, tailWord_2268485, baseEnd_2268485] using wordTrace_append hprefix tailTrace_2268485
  have hstable : (prefixWord ++ tailWord_2268485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268485).length < 2 ^ (prefixWord ++ tailWord_2268485).sum := by decide
  have hdescent : baseEnd_2268485 < baseStart_2268485 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268499 : List Nat := [1, 1, 1, 2, 1, 1, 5, 4, 2, 3, 2]
def baseStart_2268499 : Nat := 118140960795 + 2268499 * 2 ^ 59
def prefixEnd_2268499 : Nat := 4983230072969 + 3 ^ 40 * 2268499 * 2
def baseEnd_2268499 : Nat := 1164830351243825220929869

theorem tailTrace_2268499 : CollatzResearch.WordTrace tailWord_2268499 prefixEnd_2268499 1164830351243825220929869 := by
  unfold tailWord_2268499
  simp only [CollatzResearch.WordTrace]
  refine ⟨82738955808623026629528551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55159303872415351086352367 82738955808623026629528551)
  ·
    refine ⟨124108433712934539944292827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82738955808623026629528551 124108433712934539944292827)
    ·
      refine ⟨186162650569401809916439241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124108433712934539944292827 186162650569401809916439241)
      ·
        refine ⟨139621987927051357437329431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186162650569401809916439241 139621987927051357437329431)
        ·
          refine ⟨209432981890577036155994147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139621987927051357437329431 209432981890577036155994147)
          ·
            refine ⟨314149472835865554233991221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209432981890577036155994147 314149472835865554233991221)
            ·
              refine ⟨29451513078362395709436677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 314149472835865554233991221 29451513078362395709436677)
              ·
                refine ⟨5522158702192949195519377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29451513078362395709436677 5522158702192949195519377)
                ·
                  refine ⟨4141619026644711896639533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5522158702192949195519377 4141619026644711896639533)
                  ·
                    refine ⟨1553107134991766961239825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4141619026644711896639533 1553107134991766961239825)
                    ·
                      refine ⟨1164830351243825220929869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1553107134991766961239825 1164830351243825220929869)
                      ·
                        rfl

theorem cell23_2268499_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 3, 2].length) (baseStart_2268499 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268499 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268499 prefixEnd_2268499 := by exact prefixLift 2268499
  have htrace : WordTrace (prefixWord ++ tailWord_2268499) baseStart_2268499 baseEnd_2268499 := by
    simpa [prefixWord, tailWord_2268499, baseEnd_2268499] using wordTrace_append hprefix tailTrace_2268499
  have hstable : (prefixWord ++ tailWord_2268499).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268499).length < 2 ^ (prefixWord ++ tailWord_2268499).sum := by decide
  have hdescent : baseEnd_2268499 < baseStart_2268499 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268499) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268552 : List Nat := [2, 1, 3, 3, 1, 3, 10]
def baseStart_2268552 : Nat := 118140960795 + 2268552 * 2 ^ 59
def prefixEnd_2268552 : Nat := 4983230072969 + 3 ^ 40 * 2268552 * 2
def baseEnd_2268552 : Nat := 14380957601463129797125

theorem tailTrace_2268552 : CollatzResearch.WordTrace tailWord_2268552 prefixEnd_2268552 14380957601463129797125 := by
  unfold tailWord_2268552
  simp only [CollatzResearch.WordTrace]
  refine ⟨41370444438715508340603955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55160592584954011120805273 41370444438715508340603955)
  ·
    refine ⟨62055666658073262510905933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41370444438715508340603955 62055666658073262510905933)
    ·
      refine ⟨23270874996777473441589725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62055666658073262510905933 23270874996777473441589725)
      ·
        refine ⟨8726578123791552540596147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23270874996777473441589725 8726578123791552540596147)
        ·
          refine ⟨13089867185687328810894221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8726578123791552540596147 13089867185687328810894221)
          ·
            refine ⟨4908700194632748304085333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13089867185687328810894221 4908700194632748304085333)
            ·
              refine ⟨14380957601463129797125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 4908700194632748304085333 14380957601463129797125)
              ·
                rfl

theorem cell23_2268552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 10].length) (baseStart_2268552 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268552 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268552 prefixEnd_2268552 := by exact prefixLift 2268552
  have htrace : WordTrace (prefixWord ++ tailWord_2268552) baseStart_2268552 baseEnd_2268552 := by
    simpa [prefixWord, tailWord_2268552, baseEnd_2268552] using wordTrace_append hprefix tailTrace_2268552
  have hstable : (prefixWord ++ tailWord_2268552).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268552).length < 2 ^ (prefixWord ++ tailWord_2268552).sum := by decide
  have hdescent : baseEnd_2268552 < baseStart_2268552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268573 : List Nat := [1, 4, 2, 1, 3, 2, 3, 1, 2, 4]
def baseStart_2268573 : Nat := 118140960795 + 2268573 * 2 ^ 59
def prefixEnd_2268573 : Nat := 4983230072969 + 3 ^ 40 * 2268573 * 2
def baseEnd_2268573 : Nat := 388289449604085977134843

theorem tailTrace_2268573 : CollatzResearch.WordTrace tailWord_2268573 prefixEnd_2268573 388289449604085977134843 := by
  unfold tailWord_2268573
  simp only [CollatzResearch.WordTrace]
  refine ⟨82741654810354937267722373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55161103206903291511814915 82741654810354937267722373)
  ·
    refine ⟨15514060276941550737697945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82741654810354937267722373 15514060276941550737697945)
    ·
      refine ⟨11635545207706163053273459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15514060276941550737697945 11635545207706163053273459)
      ·
        refine ⟨17453317811559244579910189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11635545207706163053273459 17453317811559244579910189)
        ·
          refine ⟨6544994179334716717466321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17453317811559244579910189 6544994179334716717466321)
          ·
            refine ⟨4908745634501037538099741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6544994179334716717466321 4908745634501037538099741)
            ·
              refine ⟨1840779612937889076787403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4908745634501037538099741 1840779612937889076787403)
              ·
                refine ⟨2761169419406833615181105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1840779612937889076787403 2761169419406833615181105)
                ·
                  refine ⟨2070877064555125211385829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2761169419406833615181105 2070877064555125211385829)
                  ·
                    refine ⟨388289449604085977134843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2070877064555125211385829 388289449604085977134843)
                    ·
                      rfl

theorem cell23_2268573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 2, 3, 1, 2, 4].length) (baseStart_2268573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268573 prefixEnd_2268573 := by exact prefixLift 2268573
  have htrace : WordTrace (prefixWord ++ tailWord_2268573) baseStart_2268573 baseEnd_2268573 := by
    simpa [prefixWord, tailWord_2268573, baseEnd_2268573] using wordTrace_append hprefix tailTrace_2268573
  have hstable : (prefixWord ++ tailWord_2268573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268573).length < 2 ^ (prefixWord ++ tailWord_2268573).sum := by decide
  have hdescent : baseEnd_2268573 < baseStart_2268573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268597 : List Nat := [1, 3, 3, 2, 2, 3, 1, 3, 1, 2, 2]
def baseStart_2268597 : Nat := 118140960795 + 2268597 * 2 ^ 59
def prefixEnd_2268597 : Nat := 4983230072969 + 3 ^ 40 * 2268597 * 2
def baseEnd_2268597 : Nat := 1164880672347965837504419

theorem tailTrace_2268597 : CollatzResearch.WordTrace tailWord_2268597 prefixEnd_2268597 1164880672347965837504419 := by
  unfold tailWord_2268597
  simp only [CollatzResearch.WordTrace]
  refine ⟨82742530162267989366596045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55161686774845326244397363 82742530162267989366596045)
  ·
    refine ⟨31028448810850496012473517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82742530162267989366596045 31028448810850496012473517)
    ·
      refine ⟨11635668304068936004677569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31028448810850496012473517 11635668304068936004677569)
      ·
        refine ⟨8726751228051702003508177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11635668304068936004677569 8726751228051702003508177)
        ·
          refine ⟨6545063421038776502631133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8726751228051702003508177 6545063421038776502631133)
          ·
            refine ⟨2454398782889541188486675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6545063421038776502631133 2454398782889541188486675)
            ·
              refine ⟨3681598174334311782730013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2454398782889541188486675 3681598174334311782730013)
              ·
                refine ⟨1380599315375366918523755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3681598174334311782730013 1380599315375366918523755)
                ·
                  refine ⟨2070898973063050377785633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1380599315375366918523755 2070898973063050377785633)
                  ·
                    refine ⟨1553174229797287783339225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2070898973063050377785633 1553174229797287783339225)
                    ·
                      refine ⟨1164880672347965837504419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1553174229797287783339225 1164880672347965837504419)
                      ·
                        rfl

theorem cell23_2268597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 1, 3, 1, 2, 2].length) (baseStart_2268597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268597 prefixEnd_2268597 := by exact prefixLift 2268597
  have htrace : WordTrace (prefixWord ++ tailWord_2268597) baseStart_2268597 baseEnd_2268597 := by
    simpa [prefixWord, tailWord_2268597, baseEnd_2268597] using wordTrace_append hprefix tailTrace_2268597
  have hstable : (prefixWord ++ tailWord_2268597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268597).length < 2 ^ (prefixWord ++ tailWord_2268597).sum := by decide
  have hdescent : baseEnd_2268597 < baseStart_2268597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268602 : List Nat := [3, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4]
def baseStart_2268602 : Nat := 118140960795 + 2268602 * 2 ^ 59
def prefixEnd_2268602 : Nat := 4983230072969 + 3 ^ 40 * 2268602 * 2
def baseEnd_2268602 : Nat := 1164883239751238317941895

theorem tailTrace_2268602 : CollatzResearch.WordTrace tailWord_2268602 prefixEnd_2268602 1164883239751238317941895 := by
  unfold tailWord_2268602
  simp only [CollatzResearch.WordTrace]
  refine ⟨20685678131812468805132015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55161808351499916813685373 20685678131812468805132015)
  ·
    refine ⟨31028517197718703207698023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20685678131812468805132015 31028517197718703207698023)
    ·
      refine ⟨46542775796578054811547035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31028517197718703207698023 46542775796578054811547035)
      ·
        refine ⟨69814163694867082217320553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46542775796578054811547035 69814163694867082217320553)
        ·
          refine ⟨52360622771150311662990415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69814163694867082217320553 52360622771150311662990415)
          ·
            refine ⟨78540934156725467494485623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52360622771150311662990415 78540934156725467494485623)
            ·
              refine ⟨117811401235088201241728435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78540934156725467494485623 117811401235088201241728435)
              ·
                refine ⟨176717101852632301862592653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 117811401235088201241728435 176717101852632301862592653)
                ·
                  refine ⟨66268913194737113198472245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 176717101852632301862592653 66268913194737113198472245)
                  ·
                    refine ⟨6212710612006604362356773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66268913194737113198472245 6212710612006604362356773)
                    ·
                      refine ⟨1164883239751238317941895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6212710612006604362356773 1164883239751238317941895)
                      ·
                        rfl

theorem cell23_2268602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 1, 3, 5, 4].length) (baseStart_2268602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268602 prefixEnd_2268602 := by exact prefixLift 2268602
  have htrace : WordTrace (prefixWord ++ tailWord_2268602) baseStart_2268602 baseEnd_2268602 := by
    simpa [prefixWord, tailWord_2268602, baseEnd_2268602] using wordTrace_append hprefix tailTrace_2268602
  have hstable : (prefixWord ++ tailWord_2268602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268602).length < 2 ^ (prefixWord ++ tailWord_2268602).sum := by decide
  have hdescent : baseEnd_2268602 < baseStart_2268602 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268606 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2]
def baseStart_2268606 : Nat := 118140960795 + 2268606 * 2 ^ 59
def prefixEnd_2268606 : Nat := 4983230072969 + 3 ^ 40 * 2268606 * 2
def baseEnd_2268606 : Nat := 1164885293673856302291877

theorem tailTrace_2268606 : CollatzResearch.WordTrace tailWord_2268606 prefixEnd_2268606 1164885293673856302291877 := by
  unfold tailWord_2268606
  simp only [CollatzResearch.WordTrace]
  refine ⟨10342857302404422987959209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55161905612823589269115781 10342857302404422987959209)
  ·
    refine ⟨7757142976803317240969407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10342857302404422987959209 7757142976803317240969407)
    ·
      refine ⟨11635714465204975861454111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7757142976803317240969407 11635714465204975861454111)
      ·
        refine ⟨17453571697807463792181167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11635714465204975861454111 17453571697807463792181167)
        ·
          refine ⟨26180357546711195688271751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17453571697807463792181167 26180357546711195688271751)
          ·
            refine ⟨39270536320066793532407627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26180357546711195688271751 39270536320066793532407627)
            ·
              refine ⟨58905804480100190298611441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39270536320066793532407627 58905804480100190298611441)
              ·
                refine ⟨44179353360075142723958581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58905804480100190298611441 44179353360075142723958581)
                ·
                  refine ⟨4141814377507044630371117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44179353360075142723958581 4141814377507044630371117)
                  ·
                    refine ⟨1553180391565141736389169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4141814377507044630371117 1553180391565141736389169)
                    ·
                      refine ⟨1164885293673856302291877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1553180391565141736389169 1164885293673856302291877)
                      ·
                        rfl

theorem cell23_2268606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_2268606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268606 prefixEnd_2268606 := by exact prefixLift 2268606
  have htrace : WordTrace (prefixWord ++ tailWord_2268606) baseStart_2268606 baseEnd_2268606 := by
    simpa [prefixWord, tailWord_2268606, baseEnd_2268606] using wordTrace_append hprefix tailTrace_2268606
  have hstable : (prefixWord ++ tailWord_2268606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268606).length < 2 ^ (prefixWord ++ tailWord_2268606).sum := by decide
  have hdescent : baseEnd_2268606 < baseStart_2268606 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268630 : List Nat := [5, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3]
def baseStart_2268630 : Nat := 118140960795 + 2268630 * 2 ^ 59
def prefixEnd_2268630 : Nat := 4983230072969 + 3 ^ 40 * 2268630 * 2
def baseEnd_2268630 : Nat := 1164897617209564208391767

theorem tailTrace_2268630 : CollatzResearch.WordTrace tailWord_2268630 prefixEnd_2268630 1164897617209564208391767 := by
  unfold tailWord_2268630
  simp only [CollatzResearch.WordTrace]
  refine ⟨5171483360696777250159209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55162489180765624001698229 5171483360696777250159209)
  ·
    refine ⟨3878612520522582937619407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5171483360696777250159209 3878612520522582937619407)
    ·
      refine ⟨5817918780783874406429111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3878612520522582937619407 5817918780783874406429111)
      ·
        refine ⟨8726878171175811609643667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5817918780783874406429111 8726878171175811609643667)
        ·
          refine ⟨13090317256763717414465501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8726878171175811609643667 13090317256763717414465501)
          ·
            refine ⟨4908868971286394030424563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13090317256763717414465501 4908868971286394030424563)
            ·
              refine ⟨7363303456929591045636845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4908868971286394030424563 7363303456929591045636845)
              ·
                refine ⟨2761238796348596642113817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7363303456929591045636845 2761238796348596642113817)
                ·
                  refine ⟨2070929097261447481585363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2761238796348596642113817 2070929097261447481585363)
                  ·
                    refine ⟨3106393645892171222378045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2070929097261447481585363 3106393645892171222378045)
                    ·
                      refine ⟨1164897617209564208391767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3106393645892171222378045 1164897617209564208391767)
                      ·
                        rfl

theorem cell23_2268630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3].length) (baseStart_2268630 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268630 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268630 prefixEnd_2268630 := by exact prefixLift 2268630
  have htrace : WordTrace (prefixWord ++ tailWord_2268630) baseStart_2268630 baseEnd_2268630 := by
    simpa [prefixWord, tailWord_2268630, baseEnd_2268630] using wordTrace_append hprefix tailTrace_2268630
  have hstable : (prefixWord ++ tailWord_2268630).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268630).length < 2 ^ (prefixWord ++ tailWord_2268630).sum := by decide
  have hdescent : baseEnd_2268630 < baseStart_2268630 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268652 : List Nat := [2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 7]
def baseStart_2268652 : Nat := 118140960795 + 2268652 * 2 ^ 59
def prefixEnd_2268652 : Nat := 4983230072969 + 3 ^ 40 * 2268652 * 2
def baseEnd_2268652 : Nat := 1164908913783963122316665

theorem tailTrace_2268652 : CollatzResearch.WordTrace tailWord_2268652 prefixEnd_2268652 1164908913783963122316665 := by
  unfold tailWord_2268652
  simp only [CollatzResearch.WordTrace]
  refine ⟨41372268088534366879924105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55163024118045822506565473 41372268088534366879924105)
  ·
    refine ⟨31029201066400775159943079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41372268088534366879924105 31029201066400775159943079)
    ·
      refine ⟨46543801599601162739914619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31029201066400775159943079 46543801599601162739914619)
      ·
        refine ⟨69815702399401744109871929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46543801599601162739914619 69815702399401744109871929)
        ·
          refine ⟨52361776799551308082403947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69815702399401744109871929 52361776799551308082403947)
          ·
            refine ⟨78542665199326962123605921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52361776799551308082403947 78542665199326962123605921)
            ·
              refine ⟨58906998899495221592704441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78542665199326962123605921 58906998899495221592704441)
              ·
                refine ⟨44180249174621416194528331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 58906998899495221592704441 44180249174621416194528331)
                ·
                  refine ⟨66270373761932124291792497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44180249174621416194528331 66270373761932124291792497)
                  ·
                    refine ⟨49702780321449093218844373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66270373761932124291792497 49702780321449093218844373)
                    ·
                      refine ⟨1164908913783963122316665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49702780321449093218844373 1164908913783963122316665)
                      ·
                        rfl

theorem cell23_2268652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 7].length) (baseStart_2268652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268652 prefixEnd_2268652 := by exact prefixLift 2268652
  have htrace : WordTrace (prefixWord ++ tailWord_2268652) baseStart_2268652 baseEnd_2268652 := by
    simpa [prefixWord, tailWord_2268652, baseEnd_2268652] using wordTrace_append hprefix tailTrace_2268652
  have hstable : (prefixWord ++ tailWord_2268652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268652).length < 2 ^ (prefixWord ++ tailWord_2268652).sum := by decide
  have hdescent : baseEnd_2268652 < baseStart_2268652 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268706 : List Nat := [3, 3, 1, 1, 1, 1, 5, 1, 2, 5]
def baseStart_2268706 : Nat := 118140960795 + 2268706 * 2 ^ 59
def prefixEnd_2268706 : Nat := 4983230072969 + 3 ^ 40 * 2268706 * 2
def baseEnd_2268706 : Nat := 388312213913101970347139

theorem tailTrace_2268706 : CollatzResearch.WordTrace tailWord_2268706 prefixEnd_2268706 388312213913101970347139 := by
  unfold tailWord_2268706
  simp only [CollatzResearch.WordTrace]
  refine ⟨20686626429718275245578493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55164337145915400654875981 20686626429718275245578493)
  ·
    refine ⟨7757484911144353217091935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20686626429718275245578493 7757484911144353217091935)
    ·
      refine ⟨11636227366716529825637903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7757484911144353217091935 11636227366716529825637903)
      ·
        refine ⟨17454341050074794738456855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11636227366716529825637903 17454341050074794738456855)
        ·
          refine ⟨26181511575112192107685283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17454341050074794738456855 26181511575112192107685283)
          ·
            refine ⟨39272267362668288161527925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26181511575112192107685283 39272267362668288161527925)
            ·
              refine ⟨3681775065250152015143243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39272267362668288161527925 3681775065250152015143243)
              ·
                refine ⟨5522662597875228022714865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3681775065250152015143243 5522662597875228022714865)
                ·
                  refine ⟨4141996948406421017036149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5522662597875228022714865 4141996948406421017036149)
                  ·
                    refine ⟨388312213913101970347139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4141996948406421017036149 388312213913101970347139)
                    ·
                      rfl

theorem cell23_2268706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 5, 1, 2, 5].length) (baseStart_2268706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268706 prefixEnd_2268706 := by exact prefixLift 2268706
  have htrace : WordTrace (prefixWord ++ tailWord_2268706) baseStart_2268706 baseEnd_2268706 := by
    simpa [prefixWord, tailWord_2268706, baseEnd_2268706] using wordTrace_append hprefix tailTrace_2268706
  have hstable : (prefixWord ++ tailWord_2268706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268706).length < 2 ^ (prefixWord ++ tailWord_2268706).sum := by decide
  have hdescent : baseEnd_2268706 < baseStart_2268706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268816 : List Nat := [2, 1, 1, 1, 1, 1, 3, 3, 2, 6, 2]
def baseStart_2268816 : Nat := 118140960795 + 2268816 * 2 ^ 59
def prefixEnd_2268816 : Nat := 4983230072969 + 3 ^ 40 * 2268816 * 2
def baseEnd_2268816 : Nat := 1164993124611300480665911

theorem tailTrace_2268816 : CollatzResearch.WordTrace tailWord_2268816 prefixEnd_2268816 1164993124611300480665911 := by
  unfold tailWord_2268816
  simp only [CollatzResearch.WordTrace]
  refine ⟨41375258874237294884409151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55167011832316393179212201 41375258874237294884409151)
  ·
    refine ⟨62062888311355942326613727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41375258874237294884409151 62062888311355942326613727)
    ·
      refine ⟨93094332467033913489920591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62062888311355942326613727 93094332467033913489920591)
      ·
        refine ⟨139641498700550870234880887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93094332467033913489920591 139641498700550870234880887)
        ·
          refine ⟨209462248050826305352321331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139641498700550870234880887 209462248050826305352321331)
          ·
            refine ⟨314193372076239458028481997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209462248050826305352321331 314193372076239458028481997)
            ·
              refine ⟨117822514528589796760680749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 314193372076239458028481997 117822514528589796760680749)
              ·
                refine ⟨44183442948221173785255281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117822514528589796760680749 44183442948221173785255281)
                ·
                  refine ⟨33137582211165880338941461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44183442948221173785255281 33137582211165880338941461)
                  ·
                    refine ⟨1553324166148400640887881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 33137582211165880338941461 1553324166148400640887881)
                    ·
                      refine ⟨1164993124611300480665911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1553324166148400640887881 1164993124611300480665911)
                      ·
                        rfl

theorem cell23_2268816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 3, 3, 2, 6, 2].length) (baseStart_2268816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268816 prefixEnd_2268816 := by exact prefixLift 2268816
  have htrace : WordTrace (prefixWord ++ tailWord_2268816) baseStart_2268816 baseEnd_2268816 := by
    simpa [prefixWord, tailWord_2268816, baseEnd_2268816] using wordTrace_append hprefix tailTrace_2268816
  have hstable : (prefixWord ++ tailWord_2268816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268816).length < 2 ^ (prefixWord ++ tailWord_2268816).sum := by decide
  have hdescent : baseEnd_2268816 < baseStart_2268816 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268839 : List Nat := [1, 1, 6, 15]
def baseStart_2268839 : Nat := 118140960795 + 2268839 * 2 ^ 59
def prefixEnd_2268839 : Nat := 4983230072969 + 3 ^ 40 * 2268839 * 2
def baseEnd_2268839 : Nat := 532695443377390896515

theorem tailTrace_2268839 : CollatzResearch.WordTrace tailWord_2268839 prefixEnd_2268839 532695443377390896515 := by
  unfold tailWord_2268839
  simp only [CollatzResearch.WordTrace]
  refine ⟨82751356627391264696905571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55167571084927509797937047 82751356627391264696905571)
  ·
    refine ⟨124127034941086897045358357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82751356627391264696905571 124127034941086897045358357)
    ·
      refine ⟨5818454762863448299001173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 124127034941086897045358357 5818454762863448299001173)
      ·
        refine ⟨532695443377390896515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 15 5818454762863448299001173 532695443377390896515)
        ·
          rfl

theorem cell23_2268839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 15].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 15].length) (baseStart_2268839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268839 prefixEnd_2268839 := by exact prefixLift 2268839
  have htrace : WordTrace (prefixWord ++ tailWord_2268839) baseStart_2268839 baseEnd_2268839 := by
    simpa [prefixWord, tailWord_2268839, baseEnd_2268839] using wordTrace_append hprefix tailTrace_2268839
  have hstable : (prefixWord ++ tailWord_2268839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268839).length < 2 ^ (prefixWord ++ tailWord_2268839).sum := by decide
  have hdescent : baseEnd_2268839 < baseStart_2268839 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268859 : List Nat := [1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 6]
def baseStart_2268859 : Nat := 118140960795 + 2268859 * 2 ^ 59
def prefixEnd_2268859 : Nat := 4983230072969 + 3 ^ 40 * 2268859 * 2
def baseEnd_2268859 : Nat := 1165015204279443812428213

theorem tailTrace_2268859 : CollatzResearch.WordTrace tailWord_2268859 prefixEnd_2268859 1165015204279443812428213 := by
  unfold tailWord_2268859
  simp only [CollatzResearch.WordTrace]
  refine ⟨82752086087318808112633631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55168057391545872075089087 82752086087318808112633631)
  ·
    refine ⟨124128129130978212168950447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82752086087318808112633631 124128129130978212168950447)
    ·
      refine ⟨186192193696467318253425671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124128129130978212168950447 186192193696467318253425671)
      ·
        refine ⟨279288290544700977380138507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186192193696467318253425671 279288290544700977380138507)
        ·
          refine ⟨418932435817051466070207761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279288290544700977380138507 418932435817051466070207761)
          ·
            refine ⟨314199326862788599552655821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 418932435817051466070207761 314199326862788599552655821)
            ·
              refine ⟨117824747573545724832245933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 314199326862788599552655821 117824747573545724832245933)
              ·
                refine ⟨44184280340079646812092225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 117824747573545724832245933 44184280340079646812092225)
                ·
                  refine ⟨33138210255059735109069169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44184280340079646812092225 33138210255059735109069169)
                  ·
                    refine ⟨24853657691294801331801877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33138210255059735109069169 24853657691294801331801877)
                    ·
                      refine ⟨1165015204279443812428213, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24853657691294801331801877 1165015204279443812428213)
                      ·
                        rfl

theorem cell23_2268859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 3, 3, 2, 2, 6].length) (baseStart_2268859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268859 prefixEnd_2268859 := by exact prefixLift 2268859
  have htrace : WordTrace (prefixWord ++ tailWord_2268859) baseStart_2268859 baseEnd_2268859 := by
    simpa [prefixWord, tailWord_2268859, baseEnd_2268859] using wordTrace_append hprefix tailTrace_2268859
  have hstable : (prefixWord ++ tailWord_2268859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268859).length < 2 ^ (prefixWord ++ tailWord_2268859).sum := by decide
  have hdescent : baseEnd_2268859 < baseStart_2268859 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268884 : List Nat := [2, 4, 1, 3, 1, 1, 1, 5, 1, 2, 2]
def baseStart_2268884 : Nat := 118140960795 + 2268884 * 2 ^ 59
def prefixEnd_2268884 : Nat := 4983230072969 + 3 ^ 40 * 2268884 * 2
def baseEnd_2268884 : Nat := 1165028041295806214615599

theorem tailTrace_2268884 : CollatzResearch.WordTrace tailWord_2268884 prefixEnd_2268884 1165028041295806214615599 := by
  unfold tailWord_2268884
  simp only [CollatzResearch.WordTrace]
  refine ⟨41376498956114118691146853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55168665274818824921529137 41376498956114118691146853)
  ·
    refine ⟨7758093554271397254590035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41376498956114118691146853 7758093554271397254590035)
    ·
      refine ⟨11637140331407095881885053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7758093554271397254590035 11637140331407095881885053)
      ·
        refine ⟨4363927624277660955706895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11637140331407095881885053 4363927624277660955706895)
        ·
          refine ⟨6545891436416491433560343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4363927624277660955706895 6545891436416491433560343)
          ·
            refine ⟨9818837154624737150340515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6545891436416491433560343 9818837154624737150340515)
            ·
              refine ⟨14728255731937105725510773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9818837154624737150340515 14728255731937105725510773)
              ·
                refine ⟨1380773974869103661766635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14728255731937105725510773 1380773974869103661766635)
                ·
                  refine ⟨2071160962303655492649953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1380773974869103661766635 2071160962303655492649953)
                  ·
                    refine ⟨1553370721727741619487465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2071160962303655492649953 1553370721727741619487465)
                    ·
                      refine ⟨1165028041295806214615599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1553370721727741619487465 1165028041295806214615599)
                      ·
                        rfl

theorem cell23_2268884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 1, 1, 5, 1, 2, 2].length) (baseStart_2268884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268884 prefixEnd_2268884 := by exact prefixLift 2268884
  have htrace : WordTrace (prefixWord ++ tailWord_2268884) baseStart_2268884 baseEnd_2268884 := by
    simpa [prefixWord, tailWord_2268884, baseEnd_2268884] using wordTrace_append hprefix tailTrace_2268884
  have hstable : (prefixWord ++ tailWord_2268884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268884).length < 2 ^ (prefixWord ++ tailWord_2268884).sum := by decide
  have hdescent : baseEnd_2268884 < baseStart_2268884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268906 : List Nat := [3, 1, 3, 1, 1, 1, 2, 1, 1, 5, 4]
def baseStart_2268906 : Nat := 118140960795 + 2268906 * 2 ^ 59
def prefixEnd_2268906 : Nat := 4983230072969 + 3 ^ 40 * 2268906 * 2
def baseEnd_2268906 : Nat := 1165039337870205128540497

theorem tailTrace_2268906 : CollatzResearch.WordTrace tailWord_2268906 prefixEnd_2268906 1165039337870205128540497 := by
  unfold tailWord_2268906
  simp only [CollatzResearch.WordTrace]
  refine ⟨20688450079537133784898643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55169200212099023426396381 20688450079537133784898643)
  ·
    refine ⟨31032675119305700677347965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20688450079537133784898643 31032675119305700677347965)
    ·
      refine ⟨11637253169739637754005487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31032675119305700677347965 11637253169739637754005487)
      ·
        refine ⟨17455879754609456631008231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11637253169739637754005487 17455879754609456631008231)
        ·
          refine ⟨26183819631914184946512347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17455879754609456631008231 26183819631914184946512347)
          ·
            refine ⟨39275729447871277419768521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26183819631914184946512347 39275729447871277419768521)
            ·
              refine ⟨29456797085903458064826391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39275729447871277419768521 29456797085903458064826391)
              ·
                refine ⟨44185195628855187097239587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29456797085903458064826391 44185195628855187097239587)
                ·
                  refine ⟨66277793443282780645859381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44185195628855187097239587 66277793443282780645859381)
                  ·
                    refine ⟨6213543135307760685549317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 66277793443282780645859381 6213543135307760685549317)
                    ·
                      refine ⟨1165039337870205128540497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6213543135307760685549317 1165039337870205128540497)
                      ·
                        rfl

theorem cell23_2268906_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 2, 1, 1, 5, 4].length) (baseStart_2268906 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268906 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268906 prefixEnd_2268906 := by exact prefixLift 2268906
  have htrace : WordTrace (prefixWord ++ tailWord_2268906) baseStart_2268906 baseEnd_2268906 := by
    simpa [prefixWord, tailWord_2268906, baseEnd_2268906] using wordTrace_append hprefix tailTrace_2268906
  have hstable : (prefixWord ++ tailWord_2268906).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268906).length < 2 ^ (prefixWord ++ tailWord_2268906).sum := by decide
  have hdescent : baseEnd_2268906 < baseStart_2268906 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268906) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268923 : List Nat := [1, 1, 1, 1, 1, 3, 1, 7, 1, 4, 2]
def baseStart_2268923 : Nat := 118140960795 + 2268923 * 2 ^ 59
def prefixEnd_2268923 : Nat := 4983230072969 + 3 ^ 40 * 2268923 * 2
def baseEnd_2268923 : Nat := 1165048067041331562027919

theorem tailTrace_2268923 : CollatzResearch.WordTrace tailWord_2268923 prefixEnd_2268923 1165048067041331562027919 := by
  unfold tailWord_2268923
  simp only [CollatzResearch.WordTrace]
  refine ⟨82754420359086947042963423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55169613572724631361975615 82754420359086947042963423)
  ·
    refine ⟨124131630538630420564445135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82754420359086947042963423 124131630538630420564445135)
    ·
      refine ⟨186197445807945630846667703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124131630538630420564445135 186197445807945630846667703)
      ·
        refine ⟨279296168711918446270001555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186197445807945630846667703 279296168711918446270001555)
        ·
          refine ⟨418944253067877669405002333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279296168711918446270001555 418944253067877669405002333)
          ·
            refine ⟨157104094900454126026875875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 418944253067877669405002333 157104094900454126026875875)
            ·
              refine ⟨235656142350681189040313813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 157104094900454126026875875 235656142350681189040313813)
              ·
                refine ⟨5523190836344090368132355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 235656142350681189040313813 5523190836344090368132355)
                ·
                  refine ⟨8284786254516135552198533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5523190836344090368132355 8284786254516135552198533)
                  ·
                    refine ⟨1553397422721775416037225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8284786254516135552198533 1553397422721775416037225)
                    ·
                      refine ⟨1165048067041331562027919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1553397422721775416037225 1165048067041331562027919)
                      ·
                        rfl

theorem cell23_2268923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 7, 1, 4, 2].length) (baseStart_2268923 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268923 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268923 prefixEnd_2268923 := by exact prefixLift 2268923
  have htrace : WordTrace (prefixWord ++ tailWord_2268923) baseStart_2268923 baseEnd_2268923 := by
    simpa [prefixWord, tailWord_2268923, baseEnd_2268923] using wordTrace_append hprefix tailTrace_2268923
  have hstable : (prefixWord ++ tailWord_2268923).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268923).length < 2 ^ (prefixWord ++ tailWord_2268923).sum := by decide
  have hdescent : baseEnd_2268923 < baseStart_2268923 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268940 : List Nat := [2, 2, 1, 2, 2, 1, 3, 2, 4, 2, 2]
def baseStart_2268940 : Nat := 118140960795 + 2268940 * 2 ^ 59
def prefixEnd_2268940 : Nat := 4983230072969 + 3 ^ 40 * 2268940 * 2
def baseEnd_2268940 : Nat := 1165056796212457995515341

theorem tailTrace_2268940 : CollatzResearch.WordTrace tailWord_2268940 prefixEnd_2268940 1165056796212457995515341 := by
  unfold tailWord_2268940
  simp only [CollatzResearch.WordTrace]
  refine ⟨41377520200012679473166137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55170026933350239297554849 41377520200012679473166137)
  ·
    refine ⟨31033140150009509604874603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41377520200012679473166137 31033140150009509604874603)
    ·
      refine ⟨46549710225014264407311905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31033140150009509604874603 46549710225014264407311905)
      ·
        refine ⟨34912282668760698305483929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46549710225014264407311905 34912282668760698305483929)
        ·
          refine ⟨26184212001570523729112947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34912282668760698305483929 26184212001570523729112947)
          ·
            refine ⟨39276318002355785593669421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26184212001570523729112947 39276318002355785593669421)
            ·
              refine ⟨14728619250883419597626033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39276318002355785593669421 14728619250883419597626033)
              ·
                refine ⟨11046464438162564698219525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14728619250883419597626033 11046464438162564698219525)
                ·
                  refine ⟨2071212082155480880916161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11046464438162564698219525 2071212082155480880916161)
                  ·
                    refine ⟨1553409061616610660687121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2071212082155480880916161 1553409061616610660687121)
                    ·
                      refine ⟨1165056796212457995515341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1553409061616610660687121 1165056796212457995515341)
                      ·
                        rfl

theorem cell23_2268940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 2, 4, 2, 2].length) (baseStart_2268940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268940 prefixEnd_2268940 := by exact prefixLift 2268940
  have htrace : WordTrace (prefixWord ++ tailWord_2268940) baseStart_2268940 baseEnd_2268940 := by
    simpa [prefixWord, tailWord_2268940, baseEnd_2268940] using wordTrace_append hprefix tailTrace_2268940
  have hstable : (prefixWord ++ tailWord_2268940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268940).length < 2 ^ (prefixWord ++ tailWord_2268940).sum := by decide
  have hdescent : baseEnd_2268940 < baseStart_2268940 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268956 : List Nat := [2, 2, 3, 1, 1, 2, 1, 1, 1, 2, 7]
def baseStart_2268956 : Nat := 118140960795 + 2268956 * 2 ^ 59
def prefixEnd_2268956 : Nat := 4983230072969 + 3 ^ 40 * 2268956 * 2
def baseEnd_2268956 : Nat := 1165065011902929932915267

theorem tailTrace_2268956 : CollatzResearch.WordTrace tailWord_2268956 prefixEnd_2268956 1165065011902929932915267 := by
  unfold tailWord_2268956
  simp only [CollatzResearch.WordTrace]
  refine ⟨41377811983983696839457361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55170415978644929119276481 41377811983983696839457361)
  ·
    refine ⟨31033358987987772629593021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41377811983983696839457361 31033358987987772629593021)
    ·
      refine ⟨11637509620495414736097383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31033358987987772629593021 11637509620495414736097383)
      ·
        refine ⟨17456264430743122104146075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11637509620495414736097383 17456264430743122104146075)
        ·
          refine ⟨26184396646114683156219113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17456264430743122104146075 26184396646114683156219113)
          ·
            refine ⟨19638297484586012367164335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26184396646114683156219113 19638297484586012367164335)
            ·
              refine ⟨29457446226879018550746503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19638297484586012367164335 29457446226879018550746503)
              ·
                refine ⟨44186169340318527826119755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29457446226879018550746503 44186169340318527826119755)
                ·
                  refine ⟨66279254010477791739179633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44186169340318527826119755 66279254010477791739179633)
                  ·
                    refine ⟨49709440507858343804384725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66279254010477791739179633 49709440507858343804384725)
                    ·
                      refine ⟨1165065011902929932915267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49709440507858343804384725 1165065011902929932915267)
                      ·
                        rfl

theorem cell23_2268956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 1, 1, 2, 7].length) (baseStart_2268956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268956 prefixEnd_2268956 := by exact prefixLift 2268956
  have htrace : WordTrace (prefixWord ++ tailWord_2268956) baseStart_2268956 baseEnd_2268956 := by
    simpa [prefixWord, tailWord_2268956, baseEnd_2268956] using wordTrace_append hprefix tailTrace_2268956
  have hstable : (prefixWord ++ tailWord_2268956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268956).length < 2 ^ (prefixWord ++ tailWord_2268956).sum := by decide
  have hdescent : baseEnd_2268956 < baseStart_2268956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268963 : List Nat := [1, 1, 1, 4, 2, 1, 2, 6, 5]
def baseStart_2268963 : Nat := 118140960795 + 2268963 * 2 ^ 59
def prefixEnd_2268963 : Nat := 4983230072969 + 3 ^ 40 * 2268963 * 2
def baseEnd_2268963 : Nat := 129452067363056822836415

theorem tailTrace_2268963 : CollatzResearch.WordTrace tailWord_2268963 prefixEnd_2268963 129452067363056822836415 := by
  unfold tailWord_2268963
  simp only [CollatzResearch.WordTrace]
  refine ⟨82755879278942033874419543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55170586185961355916279695 82755879278942033874419543)
  ·
    refine ⟨124133818918413050811629315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82755879278942033874419543 124133818918413050811629315)
    ·
      refine ⟨186200728377619576217443973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124133818918413050811629315 186200728377619576217443973)
      ·
        refine ⟨34912636570803670540770745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 186200728377619576217443973 34912636570803670540770745)
        ·
          refine ⟨26184477428102752905578059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34912636570803670540770745 26184477428102752905578059)
          ·
            refine ⟨39276716142154129358367089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26184477428102752905578059 39276716142154129358367089)
            ·
              refine ⟨29457537106615597018775317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39276716142154129358367089 29457537106615597018775317)
              ·
                refine ⟨1380822051872606110255093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29457537106615597018775317 1380822051872606110255093)
                ·
                  refine ⟨129452067363056822836415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1380822051872606110255093 129452067363056822836415)
                  ·
                    rfl

theorem cell23_2268963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 2, 6, 5].length) (baseStart_2268963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268963 prefixEnd_2268963 := by exact prefixLift 2268963
  have htrace : WordTrace (prefixWord ++ tailWord_2268963) baseStart_2268963 baseEnd_2268963 := by
    simpa [prefixWord, tailWord_2268963, baseEnd_2268963] using wordTrace_append hprefix tailTrace_2268963
  have hstable : (prefixWord ++ tailWord_2268963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268963).length < 2 ^ (prefixWord ++ tailWord_2268963).sum := by decide
  have hdescent : baseEnd_2268963 < baseStart_2268963 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2268983 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 4, 5, 2]
def baseStart_2268983 : Nat := 118140960795 + 2268983 * 2 ^ 59
def prefixEnd_2268983 : Nat := 4983230072969 + 3 ^ 40 * 2268983 * 2
def baseEnd_2268983 : Nat := 1165078875880601327277643

theorem tailTrace_2268983 : CollatzResearch.WordTrace tailWord_2268983 prefixEnd_2268983 1165078875880601327277643 := by
  unfold tailWord_2268983
  simp only [CollatzResearch.WordTrace]
  refine ⟨82756608738869577290147603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55171072492579718193431735 82756608738869577290147603)
  ·
    refine ⟨124134913108304365935221405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82756608738869577290147603 124134913108304365935221405)
    ·
      refine ⟨46550592415614137225708027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124134913108304365935221405 46550592415614137225708027)
      ·
        refine ⟨69825888623421205838562041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46550592415614137225708027 69825888623421205838562041)
        ·
          refine ⟨52369416467565904378921531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69825888623421205838562041 52369416467565904378921531)
          ·
            refine ⟨78554124701348856568382297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52369416467565904378921531 78554124701348856568382297)
            ·
              refine ⟨58915593526011642426286723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78554124701348856568382297 58915593526011642426286723)
              ·
                refine ⟨88373390289017463639430085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58915593526011642426286723 88373390289017463639430085)
                ·
                  refine ⟨16570010679190774432393141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 88373390289017463639430085 16570010679190774432393141)
                  ·
                    refine ⟨1553438501174135103036857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16570010679190774432393141 1553438501174135103036857)
                    ·
                      refine ⟨1165078875880601327277643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1553438501174135103036857 1165078875880601327277643)
                      ·
                        rfl

theorem cell23_2268983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 4, 5, 2].length) (baseStart_2268983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2268983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2268983 prefixEnd_2268983 := by exact prefixLift 2268983
  have htrace : WordTrace (prefixWord ++ tailWord_2268983) baseStart_2268983 baseEnd_2268983 := by
    simpa [prefixWord, tailWord_2268983, baseEnd_2268983] using wordTrace_append hprefix tailTrace_2268983
  have hstable : (prefixWord ++ tailWord_2268983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2268983).length < 2 ^ (prefixWord ++ tailWord_2268983).sum := by decide
  have hdescent : baseEnd_2268983 < baseStart_2268983 := by decide
  rcases family_descends (prefixWord ++ tailWord_2268983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269033 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 4, 2, 3]
def baseStart_2269033 : Nat := 118140960795 + 2269033 * 2 ^ 59
def prefixEnd_2269033 : Nat := 4983230072969 + 3 ^ 40 * 2269033 * 2
def baseEnd_2269033 : Nat := 1165104549913326131652413

theorem tailTrace_2269033 : CollatzResearch.WordTrace tailWord_2269033 prefixEnd_2269033 1165104549913326131652413 := by
  unfold tailWord_2269033
  simp only [CollatzResearch.WordTrace]
  refine ⟨82758432388688435829467753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55172288259125623886311835 82758432388688435829467753)
  ·
    refine ⟨62068824291516326872100815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82758432388688435829467753 62068824291516326872100815)
    ·
      refine ⟨93103236437274490308151223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62068824291516326872100815 93103236437274490308151223)
      ·
        refine ⟨139654854655911735462226835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93103236437274490308151223 139654854655911735462226835)
        ·
          refine ⟨209482281983867603193340253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139654854655911735462226835 209482281983867603193340253)
          ·
            refine ⟨78555855743950351197502595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 209482281983867603193340253 78555855743950351197502595)
            ·
              refine ⟨117833783615925526796253893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78555855743950351197502595 117833783615925526796253893)
              ·
                refine ⟨22093834427986036274297605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117833783615925526796253893 22093834427986036274297605)
                ·
                  refine ⟨4142593955247381801430801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22093834427986036274297605 4142593955247381801430801)
                  ·
                    refine ⟨3106945466435536351073101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4142593955247381801430801 3106945466435536351073101)
                    ·
                      refine ⟨1165104549913326131652413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3106945466435536351073101 1165104549913326131652413)
                      ·
                        rfl

theorem cell23_2269033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 2, 3].length) (baseStart_2269033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269033 prefixEnd_2269033 := by exact prefixLift 2269033
  have htrace : WordTrace (prefixWord ++ tailWord_2269033) baseStart_2269033 baseEnd_2269033 := by
    simpa [prefixWord, tailWord_2269033, baseEnd_2269033] using wordTrace_append hprefix tailTrace_2269033
  have hstable : (prefixWord ++ tailWord_2269033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269033).length < 2 ^ (prefixWord ++ tailWord_2269033).sum := by decide
  have hdescent : baseEnd_2269033 < baseStart_2269033 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269050 : List Nat := [3, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3]
def baseStart_2269050 : Nat := 118140960795 + 2269050 * 2 ^ 59
def prefixEnd_2269050 : Nat := 4983230072969 + 3 ^ 40 * 2269050 * 2
def baseEnd_2269050 : Nat := 1165113279084452565139835

theorem tailTrace_2269050 : CollatzResearch.WordTrace tailWord_2269050 prefixEnd_2269050 1165113279084452565139835 := by
  unfold tailWord_2269050
  simp only [CollatzResearch.WordTrace]
  refine ⟨20689763107406711933209151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55172701619751231821891069 20689763107406711933209151)
  ·
    refine ⟨31034644661110067899813727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20689763107406711933209151 31034644661110067899813727)
    ·
      refine ⟨46551966991665101849720591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31034644661110067899813727 46551966991665101849720591)
      ·
        refine ⟨69827950487497652774580887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46551966991665101849720591 69827950487497652774580887)
        ·
          refine ⟨104741925731246479161871331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69827950487497652774580887 104741925731246479161871331)
          ·
            refine ⟨157112888596869718742806997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104741925731246479161871331 157112888596869718742806997)
            ·
              refine ⟨3682333326489134033034539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 157112888596869718742806997 3682333326489134033034539)
              ·
                refine ⟨5523499989733701049551809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3682333326489134033034539 5523499989733701049551809)
                ·
                  refine ⟨4142624992300275787163857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5523499989733701049551809 4142624992300275787163857)
                  ·
                    refine ⟨3106968744225206840372893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4142624992300275787163857 3106968744225206840372893)
                    ·
                      refine ⟨1165113279084452565139835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3106968744225206840372893 1165113279084452565139835)
                      ·
                        rfl

theorem cell23_2269050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 2, 2, 3].length) (baseStart_2269050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269050 prefixEnd_2269050 := by exact prefixLift 2269050
  have htrace : WordTrace (prefixWord ++ tailWord_2269050) baseStart_2269050 baseEnd_2269050 := by
    simpa [prefixWord, tailWord_2269050, baseEnd_2269050] using wordTrace_append hprefix tailTrace_2269050
  have hstable : (prefixWord ++ tailWord_2269050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269050).length < 2 ^ (prefixWord ++ tailWord_2269050).sum := by decide
  have hdescent : baseEnd_2269050 < baseStart_2269050 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269074 : List Nat := [3, 2, 3, 2, 1, 1, 2, 4, 1, 4]
def baseStart_2269074 : Nat := 118140960795 + 2269074 * 2 ^ 59
def prefixEnd_2269074 : Nat := 4983230072969 + 3 ^ 40 * 2269074 * 2
def baseEnd_2269074 : Nat := 388375200873386823746575

theorem tailTrace_2269074 : CollatzResearch.WordTrace tailWord_2269074 prefixEnd_2269074 388375200873386823746575 := by
  unfold tailWord_2269074
  simp only [CollatzResearch.WordTrace]
  refine ⟨20689981945384974957927569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55173285187693266554473517 20689981945384974957927569)
  ·
    refine ⟨15517486459038731218445677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20689981945384974957927569 15517486459038731218445677)
    ·
      refine ⟨5819057422139524206917129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15517486459038731218445677 5819057422139524206917129)
      ·
        refine ⟨4364293066604643155187847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5819057422139524206917129 4364293066604643155187847)
        ·
          refine ⟨6546439599906964732781771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4364293066604643155187847 6546439599906964732781771)
          ·
            refine ⟨9819659399860447099172657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6546439599906964732781771 9819659399860447099172657)
            ·
              refine ⟨7364744549895335324379493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9819659399860447099172657 7364744549895335324379493)
              ·
                refine ⟨1380889603105375373321155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7364744549895335324379493 1380889603105375373321155)
                ·
                  refine ⟨2071334404658063059981733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1380889603105375373321155 2071334404658063059981733)
                  ·
                    refine ⟨388375200873386823746575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2071334404658063059981733 388375200873386823746575)
                    ·
                      rfl

theorem cell23_2269074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_2269074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269074 prefixEnd_2269074 := by exact prefixLift 2269074
  have htrace : WordTrace (prefixWord ++ tailWord_2269074) baseStart_2269074 baseEnd_2269074 := by
    simpa [prefixWord, tailWord_2269074, baseEnd_2269074] using wordTrace_append hprefix tailTrace_2269074
  have hstable : (prefixWord ++ tailWord_2269074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269074).length < 2 ^ (prefixWord ++ tailWord_2269074).sum := by decide
  have hdescent : baseEnd_2269074 < baseStart_2269074 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269087 : List Nat := [1, 1, 2, 5, 3, 1, 3, 1, 6]
def baseStart_2269087 : Nat := 118140960795 + 2269087 * 2 ^ 59
def prefixEnd_2269087 : Nat := 4983230072969 + 3 ^ 40 * 2269087 * 2
def baseEnd_2269087 : Nat := 129459141985407657819685

theorem tailTrace_2269087 : CollatzResearch.WordTrace tailWord_2269087 prefixEnd_2269087 129459141985407657819685 := by
  unfold tailWord_2269087
  simp only [CollatzResearch.WordTrace]
  refine ⟨82760401930492803051933515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55173601286995202034622343 82760401930492803051933515)
  ·
    refine ⟨124140602895739204577900273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82760401930492803051933515 124140602895739204577900273)
    ·
      refine ⟨93105452171804403433425205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124140602895739204577900273 93105452171804403433425205)
      ·
        refine ⟨8728636141106662821883613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93105452171804403433425205 8728636141106662821883613)
        ·
          refine ⟨3273238552914998558206355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8728636141106662821883613 3273238552914998558206355)
          ·
            refine ⟨4909857829372497837309533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3273238552914998558206355 4909857829372497837309533)
            ·
              refine ⟨1841196686014686688991075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4909857829372497837309533 1841196686014686688991075)
              ·
                refine ⟨2761795029022030033486613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1841196686014686688991075 2761795029022030033486613)
                ·
                  refine ⟨129459141985407657819685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2761795029022030033486613 129459141985407657819685)
                  ·
                    rfl

theorem cell23_2269087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 3, 1, 6].length) (baseStart_2269087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269087 prefixEnd_2269087 := by exact prefixLift 2269087
  have htrace : WordTrace (prefixWord ++ tailWord_2269087) baseStart_2269087 baseEnd_2269087 := by
    simpa [prefixWord, tailWord_2269087, baseEnd_2269087] using wordTrace_append hprefix tailTrace_2269087
  have hstable : (prefixWord ++ tailWord_2269087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269087).length < 2 ^ (prefixWord ++ tailWord_2269087).sum := by decide
  have hdescent : baseEnd_2269087 < baseStart_2269087 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269108 : List Nat := [2, 5, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_2269108 : Nat := 118140960795 + 2269108 * 2 ^ 59
def prefixEnd_2269108 : Nat := 4983230072969 + 3 ^ 40 * 2269108 * 2
def baseEnd_2269108 : Nat := 388381020320804446071523

theorem tailTrace_2269108 : CollatzResearch.WordTrace tailWord_2269108 prefixEnd_2269108 388381020320804446071523 := by
  unfold tailWord_2269108
  simp only [CollatzResearch.WordTrace]
  refine ⟨41380583931708361819223989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55174111908944482425631985 41380583931708361819223989)
  ·
    refine ⟨3879429743597658920552249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 41380583931708361819223989 3879429743597658920552249)
    ·
      refine ⟨2909572307698244190414187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3879429743597658920552249 2909572307698244190414187)
      ·
        refine ⟨4364358461547366285621281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2909572307698244190414187 4364358461547366285621281)
        ·
          refine ⟨3273268846160524714215961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4364358461547366285621281 3273268846160524714215961)
          ·
            refine ⟨2454951634620393535661971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3273268846160524714215961 2454951634620393535661971)
            ·
              refine ⟨3682427451930590303492957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2454951634620393535661971 3682427451930590303492957)
              ·
                refine ⟨1380910294473971363809859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3682427451930590303492957 1380910294473971363809859)
                ·
                  refine ⟨2071365441710957045714789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1380910294473971363809859 2071365441710957045714789)
                  ·
                    refine ⟨388381020320804446071523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2071365441710957045714789 388381020320804446071523)
                    ·
                      rfl

theorem cell23_2269108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_2269108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269108 prefixEnd_2269108 := by exact prefixLift 2269108
  have htrace : WordTrace (prefixWord ++ tailWord_2269108) baseStart_2269108 baseEnd_2269108 := by
    simpa [prefixWord, tailWord_2269108, baseEnd_2269108] using wordTrace_append hprefix tailTrace_2269108
  have hstable : (prefixWord ++ tailWord_2269108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269108).length < 2 ^ (prefixWord ++ tailWord_2269108).sum := by decide
  have hdescent : baseEnd_2269108 < baseStart_2269108 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269113 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 3, 6]
def baseStart_2269113 : Nat := 118140960795 + 2269113 * 2 ^ 59
def prefixEnd_2269113 : Nat := 4983230072969 + 3 ^ 40 * 2269113 * 2
def baseEnd_2269113 : Nat := 388381876121895272884015

theorem tailTrace_2269113 : CollatzResearch.WordTrace tailWord_2269113 prefixEnd_2269113 388381876121895272884015 := by
  unfold tailWord_2269113
  simp only [CollatzResearch.WordTrace]
  refine ⟨82761350228398609492379993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55174233485599072994919995 82761350228398609492379993)
  ·
    refine ⟨62071012671298957119284995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82761350228398609492379993 62071012671298957119284995)
    ·
      refine ⟨93106519006948435678927493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62071012671298957119284995 93106519006948435678927493)
      ·
        refine ⟨17457472313802831689798905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93106519006948435678927493 17457472313802831689798905)
        ·
          refine ⟨13093104235352123767349179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17457472313802831689798905 13093104235352123767349179)
          ·
            refine ⟨19639656353028185651023769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13093104235352123767349179 19639656353028185651023769)
            ·
              refine ⟨14729742264771139238267827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19639656353028185651023769 14729742264771139238267827)
              ·
                refine ⟨22094613397156708857401741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14729742264771139238267827 22094613397156708857401741)
                ·
                  refine ⟨8285480023933765821525653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22094613397156708857401741 8285480023933765821525653)
                  ·
                    refine ⟨388381876121895272884015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8285480023933765821525653 388381876121895272884015)
                    ·
                      rfl

theorem cell23_2269113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 3, 6].length) (baseStart_2269113 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269113 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269113 prefixEnd_2269113 := by exact prefixLift 2269113
  have htrace : WordTrace (prefixWord ++ tailWord_2269113) baseStart_2269113 baseEnd_2269113 := by
    simpa [prefixWord, tailWord_2269113, baseEnd_2269113] using wordTrace_append hprefix tailTrace_2269113
  have hstable : (prefixWord ++ tailWord_2269113).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269113).length < 2 ^ (prefixWord ++ tailWord_2269113).sum := by decide
  have hdescent : baseEnd_2269113 < baseStart_2269113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269120 : List Nat := [2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 4]
def baseStart_2269120 : Nat := 118140960795 + 2269120 * 2 ^ 59
def prefixEnd_2269120 : Nat := 4983230072969 + 3 ^ 40 * 2269120 * 2
def baseEnd_2269120 : Nat := 1165149222730267291264513

theorem tailTrace_2269120 : CollatzResearch.WordTrace tailWord_2269120 prefixEnd_2269120 1165149222730267291264513 := by
  unfold tailWord_2269120
  simp only [CollatzResearch.WordTrace]
  refine ⟨41380802769686624843942407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55174403692915499791923209 41380802769686624843942407)
  ·
    refine ⟨62071204154529937265913611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41380802769686624843942407 62071204154529937265913611)
    ·
      refine ⟨93106806231794905898870417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62071204154529937265913611 93106806231794905898870417)
      ·
        refine ⟨69830104673846179424152813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93106806231794905898870417 69830104673846179424152813)
        ·
          refine ⟨26186289252692317284057305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69830104673846179424152813 26186289252692317284057305)
          ·
            refine ⟨19639716939519237963042979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26186289252692317284057305 19639716939519237963042979)
            ·
              refine ⟨29459575409278856944564469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19639716939519237963042979 29459575409278856944564469)
              ·
                refine ⟨2761835194619892838552919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29459575409278856944564469 2761835194619892838552919)
                ·
                  refine ⟨4142752791929839257829379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2761835194619892838552919 4142752791929839257829379)
                  ·
                    refine ⟨6214129187894758886744069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4142752791929839257829379 6214129187894758886744069)
                    ·
                      refine ⟨1165149222730267291264513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6214129187894758886744069 1165149222730267291264513)
                      ·
                        rfl

theorem cell23_2269120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 1, 1, 4].length) (baseStart_2269120 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269120 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269120 prefixEnd_2269120 := by exact prefixLift 2269120
  have htrace : WordTrace (prefixWord ++ tailWord_2269120) baseStart_2269120 baseEnd_2269120 := by
    simpa [prefixWord, tailWord_2269120, baseEnd_2269120] using wordTrace_append hprefix tailTrace_2269120
  have hstable : (prefixWord ++ tailWord_2269120).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269120).length < 2 ^ (prefixWord ++ tailWord_2269120).sum := by decide
  have hdescent : baseEnd_2269120 < baseStart_2269120 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269130 : List Nat := [3, 1, 2, 1, 2, 1, 4, 1, 4, 4]
def baseStart_2269130 : Nat := 118140960795 + 2269130 * 2 ^ 59
def prefixEnd_2269130 : Nat := 4983230072969 + 3 ^ 40 * 2269130 * 2
def baseEnd_2269130 : Nat := 388384785845604084046489

theorem tailTrace_2269130 : CollatzResearch.WordTrace tailWord_2269130 prefixEnd_2269130 388384785845604084046489 := by
  unfold tailWord_2269130
  simp only [CollatzResearch.WordTrace]
  refine ⟨20690492567334255348937211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55174646846224680930499229 20690492567334255348937211)
  ·
    refine ⟨31035738851001383023405817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20690492567334255348937211 31035738851001383023405817)
    ·
      refine ⟨23276804138251037267554363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31035738851001383023405817 23276804138251037267554363)
      ·
        refine ⟨34915206207376555901331545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23276804138251037267554363 34915206207376555901331545)
        ·
          refine ⟨26186404655532416925998659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34915206207376555901331545 26186404655532416925998659)
          ·
            refine ⟨39279606983298625388997989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26186404655532416925998659 39279606983298625388997989)
            ·
              refine ⟨7364926309368492260437123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39279606983298625388997989 7364926309368492260437123)
              ·
                refine ⟨11047389464052738390655685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7364926309368492260437123 11047389464052738390655685)
                ·
                  refine ⟨2071385524509888448247941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11047389464052738390655685 2071385524509888448247941)
                  ·
                    refine ⟨388384785845604084046489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2071385524509888448247941 388384785845604084046489)
                    ·
                      rfl

theorem cell23_2269130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 4, 1, 4, 4].length) (baseStart_2269130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269130 prefixEnd_2269130 := by exact prefixLift 2269130
  have htrace : WordTrace (prefixWord ++ tailWord_2269130) baseStart_2269130 baseEnd_2269130 := by
    simpa [prefixWord, tailWord_2269130, baseEnd_2269130] using wordTrace_append hprefix tailTrace_2269130
  have hstable : (prefixWord ++ tailWord_2269130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269130).length < 2 ^ (prefixWord ++ tailWord_2269130).sum := by decide
  have hdescent : baseEnd_2269130 < baseStart_2269130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269137 : List Nat := [1, 2, 2, 1, 2, 1, 2, 5, 3, 2, 2]
def baseStart_2269137 : Nat := 118140960795 + 2269137 * 2 ^ 59
def prefixEnd_2269137 : Nat := 4983230072969 + 3 ^ 40 * 2269137 * 2
def baseEnd_2269137 : Nat := 1165157951901393724751935

theorem tailTrace_2269137 : CollatzResearch.WordTrace tailWord_2269137 prefixEnd_2269137 1165157951901393724751935 := by
  unfold tailWord_2269137
  simp only [CollatzResearch.WordTrace]
  refine ⟨82762225580311661591253665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55174817053541107727502443 82762225580311661591253665)
  ·
    refine ⟨62071669185233746193440249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82762225580311661591253665 62071669185233746193440249)
    ·
      refine ⟨46553751888925309645080187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62071669185233746193440249 46553751888925309645080187)
      ·
        refine ⟨69830627833387964467620281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46553751888925309645080187 69830627833387964467620281)
        ·
          refine ⟨52372970875040973350715211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 69830627833387964467620281 52372970875040973350715211)
          ·
            refine ⟨78559456312561460026072817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52372970875040973350715211 78559456312561460026072817)
            ·
              refine ⟨58919592234421095019554613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 78559456312561460026072817 58919592234421095019554613)
              ·
                refine ⟨5523711771976977658083245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 58919592234421095019554613 5523711771976977658083245)
                ·
                  refine ⟨2071391914491366621781217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5523711771976977658083245 2071391914491366621781217)
                  ·
                    refine ⟨1553543935868524966335913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2071391914491366621781217 1553543935868524966335913)
                    ·
                      refine ⟨1165157951901393724751935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1553543935868524966335913 1165157951901393724751935)
                      ·
                        rfl

theorem cell23_2269137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 5, 3, 2, 2].length) (baseStart_2269137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269137 prefixEnd_2269137 := by exact prefixLift 2269137
  have htrace : WordTrace (prefixWord ++ tailWord_2269137) baseStart_2269137 baseEnd_2269137 := by
    simpa [prefixWord, tailWord_2269137, baseEnd_2269137] using wordTrace_append hprefix tailTrace_2269137
  have hstable : (prefixWord ++ tailWord_2269137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269137).length < 2 ^ (prefixWord ++ tailWord_2269137).sum := by decide
  have hdescent : baseEnd_2269137 < baseStart_2269137 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269140 : List Nat := [2, 4, 1, 2, 1, 1, 1, 4, 1, 1, 5]
def baseStart_2269140 : Nat := 118140960795 + 2269140 * 2 ^ 59
def prefixEnd_2269140 : Nat := 4983230072969 + 3 ^ 40 * 2269140 * 2
def baseEnd_2269140 : Nat := 1165159492343357213014421

theorem tailTrace_2269140 : CollatzResearch.WordTrace tailWord_2269140 prefixEnd_2269140 1165159492343357213014421 := by
  unfold tailWord_2269140
  simp only [CollatzResearch.WordTrace]
  refine ⟨41381167499650396551806437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55174889999533862069075249 41381167499650396551806437)
  ·
    refine ⟨7758968906184449353463707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41381167499650396551806437 7758968906184449353463707)
    ·
      refine ⟨11638453359276674030195561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7758968906184449353463707 11638453359276674030195561)
      ·
        refine ⟨8728840019457505522646671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11638453359276674030195561 8728840019457505522646671)
        ·
          refine ⟨13093260029186258283970007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8728840019457505522646671 13093260029186258283970007)
          ·
            refine ⟨19639890043779387425955011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13093260029186258283970007 19639890043779387425955011)
            ·
              refine ⟨29459835065669081138932517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19639890043779387425955011 29459835065669081138932517)
              ·
                refine ⟨5523719074812952713549847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29459835065669081138932517 5523719074812952713549847)
                ·
                  refine ⟨8285578612219429070324771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5523719074812952713549847 8285578612219429070324771)
                  ·
                    refine ⟨12428367918329143605487157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8285578612219429070324771 12428367918329143605487157)
                    ·
                      refine ⟨1165159492343357213014421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12428367918329143605487157 1165159492343357213014421)
                      ·
                        rfl

theorem cell23_2269140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_2269140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269140 prefixEnd_2269140 := by exact prefixLift 2269140
  have htrace : WordTrace (prefixWord ++ tailWord_2269140) baseStart_2269140 baseEnd_2269140 := by
    simpa [prefixWord, tailWord_2269140, baseEnd_2269140] using wordTrace_append hprefix tailTrace_2269140
  have hstable : (prefixWord ++ tailWord_2269140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269140).length < 2 ^ (prefixWord ++ tailWord_2269140).sum := by decide
  have hdescent : baseEnd_2269140 < baseStart_2269140 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269143 : List Nat := [1, 1, 3, 2, 1, 1, 6, 8]
def baseStart_2269143 : Nat := 118140960795 + 2269143 * 2 ^ 59
def prefixEnd_2269143 : Nat := 4983230072969 + 3 ^ 40 * 2269143 * 2
def baseEnd_2269143 : Nat := 43154112325382248195441

theorem tailTrace_2269143 : CollatzResearch.WordTrace tailWord_2269143 prefixEnd_2269143 43154112325382248195441 := by
  unfold tailWord_2269143
  simp only [CollatzResearch.WordTrace]
  refine ⟨82762444418289924615972083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55174962945526616410648055 82762444418289924615972083)
  ·
    refine ⟨124143666627434886923958125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82762444418289924615972083 124143666627434886923958125)
    ·
      refine ⟨46553874985288082596484297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124143666627434886923958125 46553874985288082596484297)
      ·
        refine ⟨34915406238966061947363223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46553874985288082596484297 34915406238966061947363223)
        ·
          refine ⟨52373109358449092921044835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34915406238966061947363223 52373109358449092921044835)
          ·
            refine ⟨78559664037673639381567253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52373109358449092921044835 78559664037673639381567253)
            ·
              refine ⟨3682484251765951846010965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 78559664037673639381567253 3682484251765951846010965)
              ·
                refine ⟨43154112325382248195441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3682484251765951846010965 43154112325382248195441)
                ·
                  rfl

theorem cell23_2269143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 8].length) (baseStart_2269143 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269143 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269143 prefixEnd_2269143 := by exact prefixLift 2269143
  have htrace : WordTrace (prefixWord ++ tailWord_2269143) baseStart_2269143 baseEnd_2269143 := by
    simpa [prefixWord, tailWord_2269143, baseEnd_2269143] using wordTrace_append hprefix tailTrace_2269143
  have hstable : (prefixWord ++ tailWord_2269143).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269143).length < 2 ^ (prefixWord ++ tailWord_2269143).sum := by decide
  have hdescent : baseEnd_2269143 < baseStart_2269143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269154 : List Nat := [3, 3, 3, 1, 2, 1, 1, 1, 3, 1, 4]
def baseStart_2269154 : Nat := 118140960795 + 2269154 * 2 ^ 59
def prefixEnd_2269154 : Nat := 4983230072969 + 3 ^ 40 * 2269154 * 2
def baseEnd_2269154 : Nat := 1165166681072520158239357

theorem tailTrace_2269154 : CollatzResearch.WordTrace tailWord_2269154 prefixEnd_2269154 1165166681072520158239357 := by
  unfold tailWord_2269154
  simp only [CollatzResearch.WordTrace]
  refine ⟨20690711405312518373655629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55175230414166715663081677 20690711405312518373655629)
  ·
    refine ⟨7759016776992194390120861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20690711405312518373655629 7759016776992194390120861)
    ·
      refine ⟨2909631291372072896295323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7759016776992194390120861 2909631291372072896295323)
      ·
        refine ⟨4364446937058109344442985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2909631291372072896295323 4364446937058109344442985)
        ·
          refine ⟨3273335202793582008332239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4364446937058109344442985 3273335202793582008332239)
          ·
            refine ⟨4910002804190373012498359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3273335202793582008332239 4910002804190373012498359)
            ·
              refine ⟨7365004206285559518747539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4910002804190373012498359 7365004206285559518747539)
              ·
                refine ⟨11047506309428339278121309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7365004206285559518747539 11047506309428339278121309)
                ·
                  refine ⟨4142814866035627229295491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11047506309428339278121309 4142814866035627229295491)
                  ·
                    refine ⟨6214222299053440843943237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4142814866035627229295491 6214222299053440843943237)
                    ·
                      refine ⟨1165166681072520158239357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6214222299053440843943237 1165166681072520158239357)
                      ·
                        rfl

theorem cell23_2269154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 3, 1, 4].length) (baseStart_2269154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269154 prefixEnd_2269154 := by exact prefixLift 2269154
  have htrace : WordTrace (prefixWord ++ tailWord_2269154) baseStart_2269154 baseEnd_2269154 := by
    simpa [prefixWord, tailWord_2269154, baseEnd_2269154] using wordTrace_append hprefix tailTrace_2269154
  have hstable : (prefixWord ++ tailWord_2269154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269154).length < 2 ^ (prefixWord ++ tailWord_2269154).sum := by decide
  have hdescent : baseEnd_2269154 < baseStart_2269154 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269174 : List Nat := [5, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5]
def baseStart_2269174 : Nat := 118140960795 + 2269174 * 2 ^ 59
def prefixEnd_2269174 : Nat := 4983230072969 + 3 ^ 40 * 2269174 * 2
def baseEnd_2269174 : Nat := 1165176950685610079989265

theorem tailTrace_2269174 : CollatzResearch.WordTrace tailWord_2269174 prefixEnd_2269174 1165176950685610079989265 := by
  unfold tailWord_2269174
  simp only [CollatzResearch.WordTrace]
  refine ⟨5172723442573601056896911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55175716720785077940233717 5172723442573601056896911)
  ·
    refine ⟨7759085163860401585345367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5172723442573601056896911 7759085163860401585345367)
    ·
      refine ⟨11638627745790602378018051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7759085163860401585345367 11638627745790602378018051)
      ·
        refine ⟨17457941618685903567027077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11638627745790602378018051 17457941618685903567027077)
        ·
          refine ⟨3273364053503606918817577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17457941618685903567027077 3273364053503606918817577)
          ·
            refine ⟨2455023040127705189113183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3273364053503606918817577 2455023040127705189113183)
            ·
              refine ⟨3682534560191557783669775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2455023040127705189113183 3682534560191557783669775)
              ·
                refine ⟨5523801840287336675504663, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3682534560191557783669775 5523801840287336675504663)
                ·
                  refine ⟨8285702760431005013256995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5523801840287336675504663 8285702760431005013256995)
                  ·
                    refine ⟨12428554140646507519885493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8285702760431005013256995 12428554140646507519885493)
                    ·
                      refine ⟨1165176950685610079989265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12428554140646507519885493 1165176950685610079989265)
                      ·
                        rfl

theorem cell23_2269174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5].length) (baseStart_2269174 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269174 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269174 prefixEnd_2269174 := by exact prefixLift 2269174
  have htrace : WordTrace (prefixWord ++ tailWord_2269174) baseStart_2269174 baseEnd_2269174 := by
    simpa [prefixWord, tailWord_2269174, baseEnd_2269174] using wordTrace_append hprefix tailTrace_2269174
  have hstable : (prefixWord ++ tailWord_2269174).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269174).length < 2 ^ (prefixWord ++ tailWord_2269174).sum := by decide
  have hdescent : baseEnd_2269174 < baseStart_2269174 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269183 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 5]
def baseStart_2269183 : Nat := 118140960795 + 2269183 * 2 ^ 59
def prefixEnd_2269183 : Nat := 4983230072969 + 3 ^ 40 * 2269183 * 2
def baseEnd_2269183 : Nat := 1165181572011500544776723

theorem tailTrace_2269183 : CollatzResearch.WordTrace tailWord_2269183 prefixEnd_2269183 1165181572011500544776723 := by
  unfold tailWord_2269183
  simp only [CollatzResearch.WordTrace]
  refine ⟨82763903338145011447428203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55175935558763340964952135 82763903338145011447428203)
  ·
    refine ⟨124145855007217517171142305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82763903338145011447428203 124145855007217517171142305)
    ·
      refine ⟨93109391255413137878356729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124145855007217517171142305 93109391255413137878356729)
      ·
        refine ⟨69832043441559853408767547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93109391255413137878356729 69832043441559853408767547)
        ·
          refine ⟨104748065162339780113151321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69832043441559853408767547 104748065162339780113151321)
          ·
            refine ⟨78561048871754835084863491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104748065162339780113151321 78561048871754835084863491)
            ·
              refine ⟨117841573307632252627295237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 78561048871754835084863491 117841573307632252627295237)
              ·
                refine ⟨22095294995181047367617857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 117841573307632252627295237 22095294995181047367617857)
                ·
                  refine ⟨16571471246385785525713393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22095294995181047367617857 16571471246385785525713393)
                  ·
                    refine ⟨12428603434789339144285045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16571471246385785525713393 12428603434789339144285045)
                    ·
                      refine ⟨1165181572011500544776723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12428603434789339144285045 1165181572011500544776723)
                      ·
                        rfl

theorem cell23_2269183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 5].length) (baseStart_2269183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269183 prefixEnd_2269183 := by exact prefixLift 2269183
  have htrace : WordTrace (prefixWord ++ tailWord_2269183) baseStart_2269183 baseEnd_2269183 := by
    simpa [prefixWord, tailWord_2269183, baseEnd_2269183] using wordTrace_append hprefix tailTrace_2269183
  have hstable : (prefixWord ++ tailWord_2269183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269183).length < 2 ^ (prefixWord ++ tailWord_2269183).sum := by decide
  have hdescent : baseEnd_2269183 < baseStart_2269183 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269203 : List Nat := [1, 1, 1, 2, 1, 4, 3, 1, 1, 8]
def baseStart_2269203 : Nat := 118140960795 + 2269203 * 2 ^ 59
def prefixEnd_2269203 : Nat := 4983230072969 + 3 ^ 40 * 2269203 * 2
def baseEnd_2269203 : Nat := 388397280541530155508877

theorem tailTrace_2269203 : CollatzResearch.WordTrace tailWord_2269203 prefixEnd_2269203 388397280541530155508877 := by
  unfold tailWord_2269203
  simp only [CollatzResearch.WordTrace]
  refine ⟨82764632798072554863156263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55176421865381703242104175 82764632798072554863156263)
  ·
    refine ⟨124146949197108832294734395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82764632798072554863156263 124146949197108832294734395)
    ·
      refine ⟨186220423795663248442101593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124146949197108832294734395 186220423795663248442101593)
      ·
        refine ⟨139665317846747436331576195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186220423795663248442101593 139665317846747436331576195)
        ·
          refine ⟨209497976770121154497364293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139665317846747436331576195 209497976770121154497364293)
          ·
            refine ⟨39280870644397716468255805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 209497976770121154497364293 39280870644397716468255805)
            ·
              refine ⟨14730326491649143675595927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39280870644397716468255805 14730326491649143675595927)
              ·
                refine ⟨22095489737473715513393891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14730326491649143675595927 22095489737473715513393891)
                ·
                  refine ⟨33143234606210573270090837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22095489737473715513393891 33143234606210573270090837)
                  ·
                    refine ⟨388397280541530155508877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 33143234606210573270090837 388397280541530155508877)
                    ·
                      rfl

theorem cell23_2269203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 3, 1, 1, 8].length) (baseStart_2269203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269203 prefixEnd_2269203 := by exact prefixLift 2269203
  have htrace : WordTrace (prefixWord ++ tailWord_2269203) baseStart_2269203 baseEnd_2269203 := by
    simpa [prefixWord, tailWord_2269203, baseEnd_2269203] using wordTrace_append hprefix tailTrace_2269203
  have hstable : (prefixWord ++ tailWord_2269203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269203).length < 2 ^ (prefixWord ++ tailWord_2269203).sum := by decide
  have hdescent : baseEnd_2269203 < baseStart_2269203 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269243 : List Nat := [1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 7]
def baseStart_2269243 : Nat := 118140960795 + 2269243 * 2 ^ 59
def prefixEnd_2269243 : Nat := 4983230072969 + 3 ^ 40 * 2269243 * 2
def baseEnd_2269243 : Nat := 1165212380850770310026447

theorem tailTrace_2269243 : CollatzResearch.WordTrace tailWord_2269243 prefixEnd_2269243 1165212380850770310026447 := by
  unfold tailWord_2269243
  simp only [CollatzResearch.WordTrace]
  refine ⟨82766091717927641694612383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55177394478618427796408255 82766091717927641694612383)
  ·
    refine ⟨124149137576891462541918575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82766091717927641694612383 124149137576891462541918575)
    ·
      refine ⟨186223706365337193812877863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124149137576891462541918575 186223706365337193812877863)
      ·
        refine ⟨279335559548005790719316795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186223706365337193812877863 279335559548005790719316795)
        ·
          refine ⟨419003339322008686078975193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 279335559548005790719316795 419003339322008686078975193)
          ·
            refine ⟨314252504491506514559231395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 419003339322008686078975193 314252504491506514559231395)
            ·
              refine ⟨471378756737259771838847093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 314252504491506514559231395 471378756737259771838847093)
              ·
                refine ⟨44191758444118103609891915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 471378756737259771838847093 44191758444118103609891915)
                ·
                  refine ⟨66287637666177155414837873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44191758444118103609891915 66287637666177155414837873)
                  ·
                    refine ⟨49715728249632866561128405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 66287637666177155414837873 49715728249632866561128405)
                    ·
                      refine ⟨1165212380850770310026447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 49715728249632866561128405 1165212380850770310026447)
                      ·
                        rfl

theorem cell23_2269243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 2, 7].length) (baseStart_2269243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269243 prefixEnd_2269243 := by exact prefixLift 2269243
  have htrace : WordTrace (prefixWord ++ tailWord_2269243) baseStart_2269243 baseEnd_2269243 := by
    simpa [prefixWord, tailWord_2269243, baseEnd_2269243] using wordTrace_append hprefix tailTrace_2269243
  have hstable : (prefixWord ++ tailWord_2269243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269243).length < 2 ^ (prefixWord ++ tailWord_2269243).sum := by decide
  have hdescent : baseEnd_2269243 < baseStart_2269243 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269244 : List Nat := [2, 2, 2, 2, 2, 1, 3, 1, 4, 2, 2]
def baseStart_2269244 : Nat := 118140960795 + 2269244 * 2 ^ 59
def prefixEnd_2269244 : Nat := 4983230072969 + 3 ^ 40 * 2269244 * 2
def baseEnd_2269244 : Nat := 1165212894331424806113943

theorem tailTrace_2269244 : CollatzResearch.WordTrace tailWord_2269244 prefixEnd_2269244 1165212894331424806113943 := by
  unfold tailWord_2269244
  simp only [CollatzResearch.WordTrace]
  refine ⟨41383064095462009432699393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55177418793949345910265857 41383064095462009432699393)
  ·
    refine ⟨31037298071596507074524545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41383064095462009432699393 31037298071596507074524545)
    ·
      refine ⟨23277973553697380305893409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31037298071596507074524545 23277973553697380305893409)
      ·
        refine ⟨17458480165273035229420057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23277973553697380305893409 17458480165273035229420057)
        ·
          refine ⟨13093860123954776422065043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17458480165273035229420057 13093860123954776422065043)
          ·
            refine ⟨19640790185932164633097565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13093860123954776422065043 19640790185932164633097565)
            ·
              refine ⟨7365296319724561737411587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19640790185932164633097565 7365296319724561737411587)
              ·
                refine ⟨11047944479586842606117381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7365296319724561737411587 11047944479586842606117381)
                ·
                  refine ⟨2071489589922532988647009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11047944479586842606117381 2071489589922532988647009)
                  ·
                    refine ⟨1553617192441899741485257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2071489589922532988647009 1553617192441899741485257)
                    ·
                      refine ⟨1165212894331424806113943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1553617192441899741485257 1165212894331424806113943)
                      ·
                        rfl

theorem cell23_2269244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 1, 4, 2, 2].length) (baseStart_2269244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269244 prefixEnd_2269244 := by exact prefixLift 2269244
  have htrace : WordTrace (prefixWord ++ tailWord_2269244) baseStart_2269244 baseEnd_2269244 := by
    simpa [prefixWord, tailWord_2269244, baseEnd_2269244] using wordTrace_append hprefix tailTrace_2269244
  have hstable : (prefixWord ++ tailWord_2269244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269244).length < 2 ^ (prefixWord ++ tailWord_2269244).sum := by decide
  have hdescent : baseEnd_2269244 < baseStart_2269244 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269280 : List Nat := [2, 1, 1, 3, 2, 3, 2, 1, 1, 7]
def baseStart_2269280 : Nat := 118140960795 + 2269280 * 2 ^ 59
def prefixEnd_2269280 : Nat := 4983230072969 + 3 ^ 40 * 2269280 * 2
def baseEnd_2269280 : Nat := 388410459878328888421259

theorem tailTrace_2269280 : CollatzResearch.WordTrace tailWord_2269280 prefixEnd_2269280 388410459878328888421259 := by
  unfold tailWord_2269280
  simp only [CollatzResearch.WordTrace]
  refine ⟨41383720609396798506854647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55178294145862398009139529 41383720609396798506854647)
  ·
    refine ⟨62075580914095197760281971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41383720609396798506854647 62075580914095197760281971)
    ·
      refine ⟨93113371371142796640422957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62075580914095197760281971 93113371371142796640422957)
      ·
        refine ⟨34917514264178548740158609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93113371371142796640422957 34917514264178548740158609)
        ·
          refine ⟨26188135698133911555118957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34917514264178548740158609 26188135698133911555118957)
          ·
            refine ⟨9820550886800216833169609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26188135698133911555118957 9820550886800216833169609)
            ·
              refine ⟨7365413165100162624877207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9820550886800216833169609 7365413165100162624877207)
              ·
                refine ⟨11048119747650243937315811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7365413165100162624877207 11048119747650243937315811)
                ·
                  refine ⟨16572179621475365905973717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11048119747650243937315811 16572179621475365905973717)
                  ·
                    refine ⟨388410459878328888421259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16572179621475365905973717 388410459878328888421259)
                    ·
                      rfl

theorem cell23_2269280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 1, 1, 7].length) (baseStart_2269280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269280 prefixEnd_2269280 := by exact prefixLift 2269280
  have htrace : WordTrace (prefixWord ++ tailWord_2269280) baseStart_2269280 baseEnd_2269280 := by
    simpa [prefixWord, tailWord_2269280, baseEnd_2269280] using wordTrace_append hprefix tailTrace_2269280
  have hstable : (prefixWord ++ tailWord_2269280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269280).length < 2 ^ (prefixWord ++ tailWord_2269280).sum := by decide
  have hdescent : baseEnd_2269280 < baseStart_2269280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269378 : List Nat := [3, 5, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_2269378 : Nat := 118140960795 + 2269378 * 2 ^ 59
def prefixEnd_2269378 : Nat := 4983230072969 + 3 ^ 40 * 2269378 * 2
def baseEnd_2269378 : Nat := 388427233579709093946109

theorem tailTrace_2269378 : CollatzResearch.WordTrace tailWord_2269378 prefixEnd_2269378 388427233579709093946109 := by
  unfold tailWord_2269378
  simp only [CollatzResearch.WordTrace]
  refine ⟨20692753893109639937694197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55180677048292373167184525 20692753893109639937694197)
  ·
    refine ⟨1939945677479028744158831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20692753893109639937694197 1939945677479028744158831)
    ·
      refine ⟨2909918516218543116238247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1939945677479028744158831 2909918516218543116238247)
      ·
        refine ⟨4364877774327814674357371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2909918516218543116238247 4364877774327814674357371)
        ·
          refine ⟨6547316661491722011536057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4364877774327814674357371 6547316661491722011536057)
          ·
            refine ⟨4910487496118791508652043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6547316661491722011536057 4910487496118791508652043)
            ·
              refine ⟨7365731244178187262978065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4910487496118791508652043 7365731244178187262978065)
              ·
                refine ⟨5524298433133640447233549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7365731244178187262978065 5524298433133640447233549)
                ·
                  refine ⟨2071611912425115167712581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5524298433133640447233549 2071611912425115167712581)
                  ·
                    refine ⟨388427233579709093946109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2071611912425115167712581 388427233579709093946109)
                    ·
                      rfl

theorem cell23_2269378_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_2269378 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269378 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269378 prefixEnd_2269378 := by exact prefixLift 2269378
  have htrace : WordTrace (prefixWord ++ tailWord_2269378) baseStart_2269378 baseEnd_2269378 := by
    simpa [prefixWord, tailWord_2269378, baseEnd_2269378] using wordTrace_append hprefix tailTrace_2269378
  have hstable : (prefixWord ++ tailWord_2269378).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269378).length < 2 ^ (prefixWord ++ tailWord_2269378).sum := by decide
  have hdescent : baseEnd_2269378 < baseStart_2269378 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269378) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269387 : List Nat := [1, 1, 1, 1, 3, 2, 4, 4, 1, 5]
def baseStart_2269387 : Nat := 118140960795 + 2269387 * 2 ^ 59
def prefixEnd_2269387 : Nat := 4983230072969 + 3 ^ 40 * 2269387 * 2
def baseEnd_2269387 : Nat := 388428774021672582208595

theorem tailTrace_2269387 : CollatzResearch.WordTrace tailWord_2269387 prefixEnd_2269387 388428774021672582208595 := by
  unfold tailWord_2269387
  simp only [CollatzResearch.WordTrace]
  refine ⟨82771343829405954287854415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55180895886270636191902943 82771343829405954287854415)
  ·
    refine ⟨124157015744108931431781623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82771343829405954287854415 124157015744108931431781623)
    ·
      refine ⟨186235523616163397147672435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124157015744108931431781623 186235523616163397147672435)
      ·
        refine ⟨279353285424245095721508653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186235523616163397147672435 279353285424245095721508653)
        ·
          refine ⟨104757482034091910895565745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 279353285424245095721508653 104757482034091910895565745)
          ·
            refine ⟨78568111525568933171674309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 104757482034091910895565745 78568111525568933171674309)
            ·
              refine ⟨14731520911044174969688933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 78568111525568933171674309 14731520911044174969688933)
              ·
                refine ⟨2762160170820782806816675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14731520911044174969688933 2762160170820782806816675)
                ·
                  refine ⟨4143240256231174210225013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2762160170820782806816675 4143240256231174210225013)
                  ·
                    refine ⟨388428774021672582208595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4143240256231174210225013 388428774021672582208595)
                    ·
                      rfl

theorem cell23_2269387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 4, 4, 1, 5].length) (baseStart_2269387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269387 prefixEnd_2269387 := by exact prefixLift 2269387
  have htrace : WordTrace (prefixWord ++ tailWord_2269387) baseStart_2269387 baseEnd_2269387 := by
    simpa [prefixWord, tailWord_2269387, baseEnd_2269387] using wordTrace_append hprefix tailTrace_2269387
  have hstable : (prefixWord ++ tailWord_2269387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269387).length < 2 ^ (prefixWord ++ tailWord_2269387).sum := by decide
  have hdescent : baseEnd_2269387 < baseStart_2269387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269388 : List Nat := [2, 2, 1, 6, 1, 2, 1, 1, 2, 2, 3]
def baseStart_2269388 : Nat := 118140960795 + 2269388 * 2 ^ 59
def prefixEnd_2269388 : Nat := 4983230072969 + 3 ^ 40 * 2269388 * 2
def baseEnd_2269388 : Nat := 1165286835545672242713281

theorem tailTrace_2269388 : CollatzResearch.WordTrace tailWord_2269388 prefixEnd_2269388 1165286835545672242713281 := by
  unfold tailWord_2269388
  simp only [CollatzResearch.WordTrace]
  refine ⟨41385690151201165729320409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55180920201601554305760545 41385690151201165729320409)
  ·
    refine ⟨31039267613400874296990307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41385690151201165729320409 31039267613400874296990307)
    ·
      refine ⟨46558901420101311445485461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31039267613400874296990307 46558901420101311445485461)
      ·
        refine ⟨2182448504067248974007131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46558901420101311445485461 2182448504067248974007131)
        ·
          refine ⟨3273672756100873461010697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2182448504067248974007131 3273672756100873461010697)
          ·
            refine ⟨2455254567075655095758023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3273672756100873461010697 2455254567075655095758023)
            ·
              refine ⟨3682881850613482643637035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2455254567075655095758023 3682881850613482643637035)
              ·
                refine ⟨5524322775920223965455553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3682881850613482643637035 5524322775920223965455553)
                ·
                  refine ⟨4143242081940167974091665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5524322775920223965455553 4143242081940167974091665)
                  ·
                    refine ⟨3107431561455125980568749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4143242081940167974091665 3107431561455125980568749)
                    ·
                      refine ⟨1165286835545672242713281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3107431561455125980568749 1165286835545672242713281)
                      ·
                        rfl

theorem cell23_2269388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 2, 2, 3].length) (baseStart_2269388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269388 prefixEnd_2269388 := by exact prefixLift 2269388
  have htrace : WordTrace (prefixWord ++ tailWord_2269388) baseStart_2269388 baseEnd_2269388 := by
    simpa [prefixWord, tailWord_2269388, baseEnd_2269388] using wordTrace_append hprefix tailTrace_2269388
  have hstable : (prefixWord ++ tailWord_2269388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269388).length < 2 ^ (prefixWord ++ tailWord_2269388).sum := by decide
  have hdescent : baseEnd_2269388 < baseStart_2269388 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269401 : List Nat := [1, 2, 1, 2, 3, 1, 3, 5, 1, 1, 3]
def baseStart_2269401 : Nat := 118140960795 + 2269401 * 2 ^ 59
def prefixEnd_2269401 : Nat := 4983230072969 + 3 ^ 40 * 2269401 * 2
def baseEnd_2269401 : Nat := 1165293510794180691850721

theorem tailTrace_2269401 : CollatzResearch.WordTrace tailWord_2269401 prefixEnd_2269401 1165293510794180691850721 := by
  unfold tailWord_2269401
  simp only [CollatzResearch.WordTrace]
  refine ⟨82771854451355234678864057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55181236300903489785909371 82771854451355234678864057)
  ·
    refine ⟨62078890838516426009148043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82771854451355234678864057 62078890838516426009148043)
    ·
      refine ⟨93118336257774639013722065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62078890838516426009148043 93118336257774639013722065)
      ·
        refine ⟨69838752193330979260291549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93118336257774639013722065 69838752193330979260291549)
        ·
          refine ⟨26189532072499117222609331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69838752193330979260291549 26189532072499117222609331)
          ·
            refine ⟨39284298108748675833913997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26189532072499117222609331 39284298108748675833913997)
            ·
              refine ⟨14731611790780753437717749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39284298108748675833913997 14731611790780753437717749)
              ·
                refine ⟨1381088605385695634786039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14731611790780753437717749 1381088605385695634786039)
                ·
                  refine ⟨2071632908078543452179059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1381088605385695634786039 2071632908078543452179059)
                  ·
                    refine ⟨3107449362117815178268589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2071632908078543452179059 3107449362117815178268589)
                    ·
                      refine ⟨1165293510794180691850721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3107449362117815178268589 1165293510794180691850721)
                      ·
                        rfl

theorem cell23_2269401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 5, 1, 1, 3].length) (baseStart_2269401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269401 prefixEnd_2269401 := by exact prefixLift 2269401
  have htrace : WordTrace (prefixWord ++ tailWord_2269401) baseStart_2269401 baseEnd_2269401 := by
    simpa [prefixWord, tailWord_2269401, baseEnd_2269401] using wordTrace_append hprefix tailTrace_2269401
  have hstable : (prefixWord ++ tailWord_2269401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269401).length < 2 ^ (prefixWord ++ tailWord_2269401).sum := by decide
  have hdescent : baseEnd_2269401 < baseStart_2269401 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269417 : List Nat := [1, 2, 1, 1, 1, 2, 2, 5, 4, 4]
def baseStart_2269417 : Nat := 118140960795 + 2269417 * 2 ^ 59
def prefixEnd_2269417 : Nat := 4983230072969 + 3 ^ 40 * 2269417 * 2
def baseEnd_2269417 : Nat := 388433908828217543083549

theorem tailTrace_2269417 : CollatzResearch.WordTrace tailWord_2269417 prefixEnd_2269417 388433908828217543083549 := by
  unfold tailWord_2269417
  simp only [CollatzResearch.WordTrace]
  refine ⟨82772438019297269411446505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55181625346198179607631003 82772438019297269411446505)
  ·
    refine ⟨62079328514472952058584879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82772438019297269411446505 62079328514472952058584879)
    ·
      refine ⟨93118992771709428087877319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62079328514472952058584879 93118992771709428087877319)
      ·
        refine ⟨139678489157564142131815979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93118992771709428087877319 139678489157564142131815979)
        ·
          refine ⟨209517733736346213197723969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139678489157564142131815979 209517733736346213197723969)
          ·
            refine ⟨157138300302259659898292977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 209517733736346213197723969 157138300302259659898292977)
            ·
              refine ⟨117853725226694744923719733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157138300302259659898292977 117853725226694744923719733)
              ·
                refine ⟨11048786740002632336598725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 117853725226694744923719733 11048786740002632336598725)
                ·
                  refine ⟨2071647513750493563112261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11048786740002632336598725 2071647513750493563112261)
                  ·
                    refine ⟨388433908828217543083549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2071647513750493563112261 388433908828217543083549)
                    ·
                      rfl

theorem cell23_2269417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 2, 5, 4, 4].length) (baseStart_2269417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269417 prefixEnd_2269417 := by exact prefixLift 2269417
  have htrace : WordTrace (prefixWord ++ tailWord_2269417) baseStart_2269417 baseEnd_2269417 := by
    simpa [prefixWord, tailWord_2269417, baseEnd_2269417] using wordTrace_append hprefix tailTrace_2269417
  have hstable : (prefixWord ++ tailWord_2269417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269417).length < 2 ^ (prefixWord ++ tailWord_2269417).sum := by decide
  have hdescent : baseEnd_2269417 < baseStart_2269417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269427 : List Nat := [1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 5]
def baseStart_2269427 : Nat := 118140960795 + 2269427 * 2 ^ 59
def prefixEnd_2269427 : Nat := 4983230072969 + 3 ^ 40 * 2269427 * 2
def baseEnd_2269427 : Nat := 1165306861291197590125601

theorem tailTrace_2269427 : CollatzResearch.WordTrace tailWord_2269427 prefixEnd_2269427 1165306861291197590125601 := by
  unfold tailWord_2269427
  simp only [CollatzResearch.WordTrace]
  refine ⟨82772802749261041119310535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55181868499507360746207023 82772802749261041119310535)
  ·
    refine ⟨124159204123891561678965803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82772802749261041119310535 124159204123891561678965803)
    ·
      refine ⟨186238806185837342518448705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124159204123891561678965803 186238806185837342518448705)
      ·
        refine ⟨139679104639378006888836529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186238806185837342518448705 139679104639378006888836529)
        ·
          refine ⟨104759328479533505166627397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 139679104639378006888836529 104759328479533505166627397)
          ·
            refine ⟨19642374089912532218742637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 104759328479533505166627397 19642374089912532218742637)
            ·
              refine ⟨7365890283717199582028489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19642374089912532218742637 7365890283717199582028489)
              ·
                refine ⟨5524417712787899686521367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7365890283717199582028489 5524417712787899686521367)
                ·
                  refine ⟨8286626569181849529782051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5524417712787899686521367 8286626569181849529782051)
                  ·
                    refine ⟨12429939853772774294673077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8286626569181849529782051 12429939853772774294673077)
                    ·
                      refine ⟨1165306861291197590125601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12429939853772774294673077 1165306861291197590125601)
                      ·
                        rfl

theorem cell23_2269427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 3, 2, 1, 1, 5].length) (baseStart_2269427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269427 prefixEnd_2269427 := by exact prefixLift 2269427
  have htrace : WordTrace (prefixWord ++ tailWord_2269427) baseStart_2269427 baseEnd_2269427 := by
    simpa [prefixWord, tailWord_2269427, baseEnd_2269427] using wordTrace_append hprefix tailTrace_2269427
  have hstable : (prefixWord ++ tailWord_2269427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269427).length < 2 ^ (prefixWord ++ tailWord_2269427).sum := by decide
  have hdescent : baseEnd_2269427 < baseStart_2269427 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269434 : List Nat := [3, 1, 1, 1, 1, 7, 1, 1, 1, 6]
def baseStart_2269434 : Nat := 118140960795 + 2269434 * 2 ^ 59
def prefixEnd_2269434 : Nat := 4983230072969 + 3 ^ 40 * 2269434 * 2
def baseEnd_2269434 : Nat := 388436818551926354246023

theorem tailTrace_2269434 : CollatzResearch.WordTrace tailWord_2269434 prefixEnd_2269434 388436818551926354246023 := by
  unfold tailWord_2269434
  simp only [CollatzResearch.WordTrace]
  refine ⟨20693264515058920328703839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55182038706823787543210237 20693264515058920328703839)
  ·
    refine ⟨31039896772588380493055759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20693264515058920328703839 31039896772588380493055759)
    ·
      refine ⟨46559845158882570739583639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31039896772588380493055759 46559845158882570739583639)
      ·
        refine ⟨69839767738323856109375459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46559845158882570739583639 69839767738323856109375459)
        ·
          refine ⟨104759651607485784164063189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69839767738323856109375459 104759651607485784164063189)
          ·
            refine ⟨2455304334550448066345231, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 104759651607485784164063189 2455304334550448066345231)
            ·
              refine ⟨3682956501825672099517847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2455304334550448066345231 3682956501825672099517847)
              ·
                refine ⟨5524434752738508149276771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3682956501825672099517847 5524434752738508149276771)
                ·
                  refine ⟨8286652129107762223915157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5524434752738508149276771 8286652129107762223915157)
                  ·
                    refine ⟨388436818551926354246023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8286652129107762223915157 388436818551926354246023)
                    ·
                      rfl

theorem cell23_2269434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 1, 1, 1, 6].length) (baseStart_2269434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269434 prefixEnd_2269434 := by exact prefixLift 2269434
  have htrace : WordTrace (prefixWord ++ tailWord_2269434) baseStart_2269434 baseEnd_2269434 := by
    simpa [prefixWord, tailWord_2269434, baseEnd_2269434] using wordTrace_append hprefix tailTrace_2269434
  have hstable : (prefixWord ++ tailWord_2269434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269434).length < 2 ^ (prefixWord ++ tailWord_2269434).sum := by decide
  have hdescent : baseEnd_2269434 < baseStart_2269434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269441 : List Nat := [1, 2, 4, 1, 1, 2, 1, 4, 3, 2, 2]
def baseStart_2269441 : Nat := 118140960795 + 2269441 * 2 ^ 59
def prefixEnd_2269441 : Nat := 4983230072969 + 3 ^ 40 * 2269441 * 2
def baseEnd_2269441 : Nat := 1165314050020360535350537

theorem tailTrace_2269441 : CollatzResearch.WordTrace tailWord_2269441 prefixEnd_2269441 1165314050020360535350537 := by
  unfold tailWord_2269441
  simp only [CollatzResearch.WordTrace]
  refine ⟨82773313371210321510320177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55182208914140214340213451 82773313371210321510320177)
  ·
    refine ⟨62079985028407741132740133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82773313371210321510320177 62079985028407741132740133)
    ·
      refine ⟨11639997192826451462388775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62079985028407741132740133 11639997192826451462388775)
      ·
        refine ⟨17459995789239677193583163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11639997192826451462388775 17459995789239677193583163)
        ·
          refine ⟨26189993683859515790374745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17459995789239677193583163 26189993683859515790374745)
          ·
            refine ⟨19642495262894636842781059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26189993683859515790374745 19642495262894636842781059)
            ·
              refine ⟨29463742894341955264171589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19642495262894636842781059 29463742894341955264171589)
              ·
                refine ⟨5524451792689116612032173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29463742894341955264171589 5524451792689116612032173)
                ·
                  refine ⟨2071669422258418729512065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5524451792689116612032173 2071669422258418729512065)
                  ·
                    refine ⟨1553752066693814047134049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2071669422258418729512065 1553752066693814047134049)
                    ·
                      refine ⟨1165314050020360535350537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1553752066693814047134049 1165314050020360535350537)
                      ·
                        rfl

theorem cell23_2269441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 4, 3, 2, 2].length) (baseStart_2269441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269441 prefixEnd_2269441 := by exact prefixLift 2269441
  have htrace : WordTrace (prefixWord ++ tailWord_2269441) baseStart_2269441 baseEnd_2269441 := by
    simpa [prefixWord, tailWord_2269441, baseEnd_2269441] using wordTrace_append hprefix tailTrace_2269441
  have hstable : (prefixWord ++ tailWord_2269441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269441).length < 2 ^ (prefixWord ++ tailWord_2269441).sum := by decide
  have hdescent : baseEnd_2269441 < baseStart_2269441 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269475 : List Nat := [1, 1, 1, 4, 2, 2, 5, 2, 1, 2, 2]
def baseStart_2269475 : Nat := 118140960795 + 2269475 * 2 ^ 59
def prefixEnd_2269475 : Nat := 4983230072969 + 3 ^ 40 * 2269475 * 2
def baseEnd_2269475 : Nat := 1165331508362613402325381

theorem tailTrace_2269475 : CollatzResearch.WordTrace tailWord_2269475 prefixEnd_2269475 1165331508362613402325381 := by
  unfold tailWord_2269475
  simp only [CollatzResearch.WordTrace]
  refine ⟨82774553453087145317057879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55183035635391430211371919 82774553453087145317057879)
  ·
    refine ⟨124161830179630717975586819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82774553453087145317057879 124161830179630717975586819)
    ·
      refine ⟨186242745269446076963380229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124161830179630717975586819 186242745269446076963380229)
      ·
        refine ⟨34920514738021139430633793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 186242745269446076963380229 34920514738021139430633793)
        ·
          refine ⟨26190386053515854572975345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34920514738021139430633793 26190386053515854572975345)
          ·
            refine ⟨19642789540136890929731509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26190386053515854572975345 19642789540136890929731509)
            ·
              refine ⟨1841511519387833524662329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 19642789540136890929731509 1841511519387833524662329)
              ·
                refine ⟨1381133639540875143496747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1841511519387833524662329 1381133639540875143496747)
                ·
                  refine ⟨2071700459311312715245121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1381133639540875143496747 2071700459311312715245121)
                  ·
                    refine ⟨1553775344483484536433841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2071700459311312715245121 1553775344483484536433841)
                    ·
                      refine ⟨1165331508362613402325381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1553775344483484536433841 1165331508362613402325381)
                      ·
                        rfl

theorem cell23_2269475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 5, 2, 1, 2, 2].length) (baseStart_2269475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269475 prefixEnd_2269475 := by exact prefixLift 2269475
  have htrace : WordTrace (prefixWord ++ tailWord_2269475) baseStart_2269475 baseEnd_2269475 := by
    simpa [prefixWord, tailWord_2269475, baseEnd_2269475] using wordTrace_append hprefix tailTrace_2269475
  have hstable : (prefixWord ++ tailWord_2269475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269475).length < 2 ^ (prefixWord ++ tailWord_2269475).sum := by decide
  have hdescent : baseEnd_2269475 < baseStart_2269475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269491 : List Nat := [1, 1, 1, 2, 5, 1, 3, 3, 2, 1, 3]
def baseStart_2269491 : Nat := 118140960795 + 2269491 * 2 ^ 59
def prefixEnd_2269491 : Nat := 4983230072969 + 3 ^ 40 * 2269491 * 2
def baseEnd_2269491 : Nat := 1165339724053085339725307

theorem tailTrace_2269491 : CollatzResearch.WordTrace tailWord_2269491 prefixEnd_2269491 1165339724053085339725307 := by
  unfold tailWord_2269491
  simp only [CollatzResearch.WordTrace]
  refine ⟨82775137021029180049640327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55183424680686120033093551 82775137021029180049640327)
  ·
    refine ⟨124162705531543770074460491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82775137021029180049640327 124162705531543770074460491)
    ·
      refine ⟨186244058297315655111690737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124162705531543770074460491 186244058297315655111690737)
      ·
        refine ⟨139683043722986741333768053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186244058297315655111690737 139683043722986741333768053)
        ·
          refine ⟨13095285349030007000040755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 139683043722986741333768053 13095285349030007000040755)
          ·
            refine ⟨19642928023545010500061133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13095285349030007000040755 19642928023545010500061133)
            ·
              refine ⟨7366098008829378937522925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19642928023545010500061133 7366098008829378937522925)
              ·
                refine ⟨2762286753311017101571097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7366098008829378937522925 2762286753311017101571097)
                ·
                  refine ⟨2071715064983262826178323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2762286753311017101571097 2071715064983262826178323)
                  ·
                    refine ⟨3107572597474894239267485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2071715064983262826178323 3107572597474894239267485)
                    ·
                      refine ⟨1165339724053085339725307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3107572597474894239267485 1165339724053085339725307)
                      ·
                        rfl

theorem cell23_2269491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 2, 1, 3].length) (baseStart_2269491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269491 prefixEnd_2269491 := by exact prefixLift 2269491
  have htrace : WordTrace (prefixWord ++ tailWord_2269491) baseStart_2269491 baseEnd_2269491 := by
    simpa [prefixWord, tailWord_2269491, baseEnd_2269491] using wordTrace_append hprefix tailTrace_2269491
  have hstable : (prefixWord ++ tailWord_2269491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269491).length < 2 ^ (prefixWord ++ tailWord_2269491).sum := by decide
  have hdescent : baseEnd_2269491 < baseStart_2269491 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269508 : List Nat := [2, 3, 4, 1, 2, 1, 1, 2, 1, 3, 3]
def baseStart_2269508 : Nat := 118140960795 + 2269508 * 2 ^ 59
def prefixEnd_2269508 : Nat := 4983230072969 + 3 ^ 40 * 2269508 * 2
def baseEnd_2269508 : Nat := 1165348453224211773212729

theorem tailTrace_2269508 : CollatzResearch.WordTrace tailWord_2269508 prefixEnd_2269508 1165348453224211773212729 := by
  unfold tailWord_2269508
  simp only [CollatzResearch.WordTrace]
  refine ⟨41387878530983795976504589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55183838041311727968672785 41387878530983795976504589)
  ·
    refine ⟨15520454449118923491189221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41387878530983795976504589 15520454449118923491189221)
    ·
      refine ⟨2910085209209798154597979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15520454449118923491189221 2910085209209798154597979)
      ·
        refine ⟨4365127813814697231896969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2910085209209798154597979 4365127813814697231896969)
        ·
          refine ⟨3273845860361022923922727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4365127813814697231896969 3273845860361022923922727)
          ·
            refine ⟨4910768790541534385884091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3273845860361022923922727 4910768790541534385884091)
            ·
              refine ⟨7366153185812301578826137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4910768790541534385884091 7366153185812301578826137)
              ·
                refine ⟨5524614889359226184119603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7366153185812301578826137 5524614889359226184119603)
                ·
                  refine ⟨8286922334038839276179405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5524614889359226184119603 8286922334038839276179405)
                  ·
                    refine ⟨3107595875264564728567277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8286922334038839276179405 3107595875264564728567277)
                    ·
                      refine ⟨1165348453224211773212729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3107595875264564728567277 1165348453224211773212729)
                      ·
                        rfl

theorem cell23_2269508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_2269508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269508 prefixEnd_2269508 := by exact prefixLift 2269508
  have htrace : WordTrace (prefixWord ++ tailWord_2269508) baseStart_2269508 baseEnd_2269508 := by
    simpa [prefixWord, tailWord_2269508, baseEnd_2269508] using wordTrace_append hprefix tailTrace_2269508
  have hstable : (prefixWord ++ tailWord_2269508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269508).length < 2 ^ (prefixWord ++ tailWord_2269508).sum := by decide
  have hdescent : baseEnd_2269508 < baseStart_2269508 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269544 : List Nat := [2, 1, 4, 2, 2, 1, 1, 1, 1, 4, 4]
def baseStart_2269544 : Nat := 118140960795 + 2269544 * 2 ^ 59
def prefixEnd_2269544 : Nat := 4983230072969 + 3 ^ 40 * 2269544 * 2
def baseEnd_2269544 : Nat := 1165366938527773632362563

theorem tailTrace_2269544 : CollatzResearch.WordTrace tailWord_2269544 prefixEnd_2269544 1165366938527773632362563 := by
  unfold tailWord_2269544
  simp only [CollatzResearch.WordTrace]
  refine ⟨41388535044918585050659843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55184713393224780067546457 41388535044918585050659843)
  ·
    refine ⟨62082802567377877575989765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41388535044918585050659843 62082802567377877575989765)
    ·
      refine ⟨11640525481383352045498081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62082802567377877575989765 11640525481383352045498081)
      ·
        refine ⟨8730394111037514034123561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11640525481383352045498081 8730394111037514034123561)
        ·
          refine ⟨6547795583278135525592671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8730394111037514034123561 6547795583278135525592671)
          ·
            refine ⟨9821693374917203288389007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6547795583278135525592671 9821693374917203288389007)
            ·
              refine ⟨14732540062375804932583511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9821693374917203288389007 14732540062375804932583511)
              ·
                refine ⟨22098810093563707398875267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14732540062375804932583511 22098810093563707398875267)
                ·
                  refine ⟨33148215140345561098312901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22098810093563707398875267 33148215140345561098312901)
                  ·
                    refine ⟨6215290338814792705933669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33148215140345561098312901 6215290338814792705933669)
                    ·
                      refine ⟨1165366938527773632362563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6215290338814792705933669 1165366938527773632362563)
                      ·
                        rfl

theorem cell23_2269544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 1, 1, 1, 4, 4].length) (baseStart_2269544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269544 prefixEnd_2269544 := by exact prefixLift 2269544
  have htrace : WordTrace (prefixWord ++ tailWord_2269544) baseStart_2269544 baseEnd_2269544 := by
    simpa [prefixWord, tailWord_2269544, baseEnd_2269544] using wordTrace_append hprefix tailTrace_2269544
  have hstable : (prefixWord ++ tailWord_2269544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269544).length < 2 ^ (prefixWord ++ tailWord_2269544).sum := by decide
  have hdescent : baseEnd_2269544 < baseStart_2269544 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269548 : List Nat := [2, 2, 1, 1, 6, 1, 2, 1, 1, 4, 2]
def baseStart_2269548 : Nat := 118140960795 + 2269548 * 2 ^ 59
def prefixEnd_2269548 : Nat := 4983230072969 + 3 ^ 40 * 2269548 * 2
def baseEnd_2269548 : Nat := 1165368992450391616712545

theorem tailTrace_2269548 : CollatzResearch.WordTrace tailWord_2269548 prefixEnd_2269548 1165368992450391616712545 := by
  unfold tailWord_2269548
  simp only [CollatzResearch.WordTrace]
  refine ⟨41388607990911339392232649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55184810654548452522976865 41388607990911339392232649)
  ·
    refine ⟨31041455993183504544174487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41388607990911339392232649 31041455993183504544174487)
    ·
      refine ⟨46562183989775256816261731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31041455993183504544174487 46562183989775256816261731)
      ·
        refine ⟨69843275984662885224392597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46562183989775256816261731 69843275984662885224392597)
        ·
          refine ⟨3273903561781072744893403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 69843275984662885224392597 3273903561781072744893403)
          ·
            refine ⟨4910855342671609117340105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3273903561781072744893403 4910855342671609117340105)
            ·
              refine ⟨3683141507003706838005079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4910855342671609117340105 3683141507003706838005079)
              ·
                refine ⟨5524712260505560257007619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3683141507003706838005079 5524712260505560257007619)
                ·
                  refine ⟨8287068390758340385511429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5524712260505560257007619 8287068390758340385511429)
                  ·
                    refine ⟨1553825323267188822283393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8287068390758340385511429 1553825323267188822283393)
                    ·
                      refine ⟨1165368992450391616712545, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1553825323267188822283393 1165368992450391616712545)
                      ·
                        rfl

theorem cell23_2269548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 4, 2].length) (baseStart_2269548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269548 prefixEnd_2269548 := by exact prefixLift 2269548
  have htrace : WordTrace (prefixWord ++ tailWord_2269548) baseStart_2269548 baseEnd_2269548 := by
    simpa [prefixWord, tailWord_2269548, baseEnd_2269548] using wordTrace_append hprefix tailTrace_2269548
  have hstable : (prefixWord ++ tailWord_2269548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269548).length < 2 ^ (prefixWord ++ tailWord_2269548).sum := by decide
  have hdescent : baseEnd_2269548 < baseStart_2269548 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269554 : List Nat := [3, 2, 1, 2, 1, 4, 1, 2, 7]
def baseStart_2269554 : Nat := 118140960795 + 2269554 * 2 ^ 59
def prefixEnd_2269554 : Nat := 4983230072969 + 3 ^ 40 * 2269554 * 2
def baseEnd_2269554 : Nat := 129485785926035399248613

theorem tailTrace_2269554 : CollatzResearch.WordTrace tailWord_2269554 prefixEnd_2269554 129485785926035399248613 := by
  unfold tailWord_2269554
  simp only [CollatzResearch.WordTrace]
  refine ⟨20694358704950235452295929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55184956546533961206122477 20694358704950235452295929)
  ·
    refine ⟨15520769028712676589221947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20694358704950235452295929 15520769028712676589221947)
    ·
      refine ⟨23281153543069014883832921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15520769028712676589221947 23281153543069014883832921)
      ·
        refine ⟨17460865157301761162874691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23281153543069014883832921 17460865157301761162874691)
        ·
          refine ⟨26191297735952641744312037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17460865157301761162874691 26191297735952641744312037)
          ·
            refine ⟨4910868325491120327058507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26191297735952641744312037 4910868325491120327058507)
            ·
              refine ⟨7366302488236680490587761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4910868325491120327058507 7366302488236680490587761)
              ·
                refine ⟨5524726866177510367940821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7366302488236680490587761 5524726866177510367940821)
                ·
                  refine ⟨129485785926035399248613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5524726866177510367940821 129485785926035399248613)
                  ·
                    rfl

theorem cell23_2269554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 4, 1, 2, 7].length) (baseStart_2269554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269554 prefixEnd_2269554 := by exact prefixLift 2269554
  have htrace : WordTrace (prefixWord ++ tailWord_2269554) baseStart_2269554 baseEnd_2269554 := by
    simpa [prefixWord, tailWord_2269554, baseEnd_2269554] using wordTrace_append hprefix tailTrace_2269554
  have hstable : (prefixWord ++ tailWord_2269554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269554).length < 2 ^ (prefixWord ++ tailWord_2269554).sum := by decide
  have hdescent : baseEnd_2269554 < baseStart_2269554 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269567 : List Nat := [1, 1, 2, 2, 1, 1, 2, 5, 1, 7]
def baseStart_2269567 : Nat := 118140960795 + 2269567 * 2 ^ 59
def prefixEnd_2269567 : Nat := 4983230072969 + 3 ^ 40 * 2269567 * 2
def baseEnd_2269567 : Nat := 388459582860942347458319

theorem tailTrace_2269567 : CollatzResearch.WordTrace tailWord_2269567 prefixEnd_2269567 388459582860942347458319 := by
  unfold tailWord_2269567
  simp only [CollatzResearch.WordTrace]
  refine ⟨82777908968753845029406955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55185272645835896686271303 82777908968753845029406955)
  ·
    refine ⟨124166863453130767544110433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82777908968753845029406955 124166863453130767544110433)
    ·
      refine ⟨93125147589848075658082825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124166863453130767544110433 93125147589848075658082825)
      ·
        refine ⟨69843860692386056743562119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93125147589848075658082825 69843860692386056743562119)
        ·
          refine ⟨104765791038579085115343179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69843860692386056743562119 104765791038579085115343179)
          ·
            refine ⟨157148686557868627673014769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 104765791038579085115343179 157148686557868627673014769)
            ·
              refine ⟨117861514918401470754761077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 157148686557868627673014769 117861514918401470754761077)
              ·
                refine ⟨11049517023600137883258851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 117861514918401470754761077 11049517023600137883258851)
                ·
                  refine ⟨16574275535400206824888277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11049517023600137883258851 16574275535400206824888277)
                  ·
                    refine ⟨388459582860942347458319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 16574275535400206824888277 388459582860942347458319)
                    ·
                      rfl

theorem cell23_2269567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 5, 1, 7].length) (baseStart_2269567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269567 prefixEnd_2269567 := by exact prefixLift 2269567
  have htrace : WordTrace (prefixWord ++ tailWord_2269567) baseStart_2269567 baseEnd_2269567 := by
    simpa [prefixWord, tailWord_2269567, baseEnd_2269567] using wordTrace_append hprefix tailTrace_2269567
  have hstable : (prefixWord ++ tailWord_2269567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269567).length < 2 ^ (prefixWord ++ tailWord_2269567).sum := by decide
  have hdescent : baseEnd_2269567 < baseStart_2269567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269582 : List Nat := [4, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2]
def baseStart_2269582 : Nat := 118140960795 + 2269582 * 2 ^ 59
def prefixEnd_2269582 : Nat := 4983230072969 + 3 ^ 40 * 2269582 * 2
def baseEnd_2269582 : Nat := 1165386450792644483687389

theorem tailTrace_2269582 : CollatzResearch.WordTrace tailWord_2269582 prefixEnd_2269582 1165386450792644483687389 := by
  unfold tailWord_2269582
  simp only [CollatzResearch.WordTrace]
  refine ⟨10347307007962437823900375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55185637375799668394135333 10347307007962437823900375)
  ·
    refine ⟨15520960511943656735850563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10347307007962437823900375 15520960511943656735850563)
    ·
      refine ⟨23281440767915485103775845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15520960511943656735850563 23281440767915485103775845)
      ·
        refine ⟨4365270143984153456957971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23281440767915485103775845 4365270143984153456957971)
        ·
          refine ⟨6547905215976230185436957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4365270143984153456957971 6547905215976230185436957)
          ·
            refine ⟨2455464455991086319538859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6547905215976230185436957 2455464455991086319538859)
            ·
              refine ⟨3683196683986629479308289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2455464455991086319538859 3683196683986629479308289)
              ·
                refine ⟨2762397512989972109481217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3683196683986629479308289 2762397512989972109481217)
                ·
                  refine ⟨2071798134742479082110913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2762397512989972109481217 2071798134742479082110913)
                  ·
                    refine ⟨1553848601056859311583185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2071798134742479082110913 1553848601056859311583185)
                    ·
                      refine ⟨1165386450792644483687389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1553848601056859311583185 1165386450792644483687389)
                      ·
                        rfl

theorem cell23_2269582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 1, 2, 2, 2, 2].length) (baseStart_2269582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269582 prefixEnd_2269582 := by exact prefixLift 2269582
  have htrace : WordTrace (prefixWord ++ tailWord_2269582) baseStart_2269582 baseEnd_2269582 := by
    simpa [prefixWord, tailWord_2269582, baseEnd_2269582] using wordTrace_append hprefix tailTrace_2269582
  have hstable : (prefixWord ++ tailWord_2269582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269582).length < 2 ^ (prefixWord ++ tailWord_2269582).sum := by decide
  have hdescent : baseEnd_2269582 < baseStart_2269582 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269598 : List Nat := [4, 3, 1, 2, 1, 1, 2, 1, 2, 3, 3]
def baseStart_2269598 : Nat := 118140960795 + 2269598 * 2 ^ 59
def prefixEnd_2269598 : Nat := 4983230072969 + 3 ^ 40 * 2269598 * 2
def baseEnd_2269598 : Nat := 1165394666483116421087315

theorem tailTrace_2269598 : CollatzResearch.WordTrace tailWord_2269598 prefixEnd_2269598 1165394666483116421087315 := by
  unfold tailWord_2269598
  simp only [CollatzResearch.WordTrace]
  refine ⟨10347379953955192165473181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55186026421094358215856965 10347379953955192165473181)
  ·
    refine ⟨3880267482733197062052443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10347379953955192165473181 3880267482733197062052443)
    ·
      refine ⟨5820401224099795593078665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3880267482733197062052443 5820401224099795593078665)
      ·
        refine ⟨4365300918074846694808999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5820401224099795593078665 4365300918074846694808999)
        ·
          refine ⟨6547951377112270042213499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4365300918074846694808999 6547951377112270042213499)
          ·
            refine ⟨9821927065668405063320249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6547951377112270042213499 9821927065668405063320249)
            ·
              refine ⟨7366445299251303797490187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9821927065668405063320249 7366445299251303797490187)
              ·
                refine ⟨11049667948876955696235281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7366445299251303797490187 11049667948876955696235281)
                ·
                  refine ⟨8287250961657716772176461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11049667948876955696235281 8287250961657716772176461)
                  ·
                    refine ⟨3107719110621643789566173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8287250961657716772176461 3107719110621643789566173)
                    ·
                      refine ⟨1165394666483116421087315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3107719110621643789566173 1165394666483116421087315)
                      ·
                        rfl

theorem cell23_2269598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_2269598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269598 prefixEnd_2269598 := by exact prefixLift 2269598
  have htrace : WordTrace (prefixWord ++ tailWord_2269598) baseStart_2269598 baseEnd_2269598 := by
    simpa [prefixWord, tailWord_2269598, baseEnd_2269598] using wordTrace_append hprefix tailTrace_2269598
  have hstable : (prefixWord ++ tailWord_2269598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269598).length < 2 ^ (prefixWord ++ tailWord_2269598).sum := by decide
  have hdescent : baseEnd_2269598 < baseStart_2269598 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269604 : List Nat := [2, 3, 1, 2, 1, 1, 3, 2, 1, 3, 4]
def baseStart_2269604 : Nat := 118140960795 + 2269604 * 2 ^ 59
def prefixEnd_2269604 : Nat := 4983230072969 + 3 ^ 40 * 2269604 * 2
def baseEnd_2269604 : Nat := 1165397747367043397612287

theorem tailTrace_2269604 : CollatzResearch.WordTrace tailWord_2269604 prefixEnd_2269604 1165397747367043397612287 := by
  unfold tailWord_2269604
  simp only [CollatzResearch.WordTrace]
  refine ⟨41389629234809900174251933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55186172313079866899002577 41389629234809900174251933)
  ·
    refine ⟨15521110963053712565344475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41389629234809900174251933 15521110963053712565344475)
    ·
      refine ⟨23281666444580568848016713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15521110963053712565344475 23281666444580568848016713)
      ·
        refine ⟨17461249833435426636012535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23281666444580568848016713 17461249833435426636012535)
        ·
          refine ⟨26191874750153139954018803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17461249833435426636012535 26191874750153139954018803)
          ·
            refine ⟨39287812125229709931028205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26191874750153139954018803 39287812125229709931028205)
            ·
              refine ⟨14732929546961141224135577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39287812125229709931028205 14732929546961141224135577)
              ·
                refine ⟨11049697160220855918101683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14732929546961141224135577 11049697160220855918101683)
                ·
                  refine ⟨16574545740331283877152525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11049697160220855918101683 16574545740331283877152525)
                  ·
                    refine ⟨6215454652624231453932197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16574545740331283877152525 6215454652624231453932197)
                    ·
                      refine ⟨1165397747367043397612287, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6215454652624231453932197 1165397747367043397612287)
                      ·
                        rfl

theorem cell23_2269604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 3, 2, 1, 3, 4].length) (baseStart_2269604 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269604 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269604 prefixEnd_2269604 := by exact prefixLift 2269604
  have htrace : WordTrace (prefixWord ++ tailWord_2269604) baseStart_2269604 baseEnd_2269604 := by
    simpa [prefixWord, tailWord_2269604, baseEnd_2269604] using wordTrace_append hprefix tailTrace_2269604
  have hstable : (prefixWord ++ tailWord_2269604).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269604).length < 2 ^ (prefixWord ++ tailWord_2269604).sum := by decide
  have hdescent : baseEnd_2269604 < baseStart_2269604 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269661 : List Nat := [1, 4, 3, 1, 1, 1, 3, 3, 6]
def baseStart_2269661 : Nat := 118140960795 + 2269661 * 2 ^ 59
def prefixEnd_2269661 : Nat := 4983230072969 + 3 ^ 40 * 2269661 * 2
def baseEnd_2269661 : Nat := 129491890640483297177725

theorem tailTrace_2269661 : CollatzResearch.WordTrace tailWord_2269661 prefixEnd_2269661 129491890640483297177725 := by
  unfold tailWord_2269661
  simp only [CollatzResearch.WordTrace]
  refine ⟨82781337430413299083328837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55187558286942199388885891 82781337430413299083328837)
  ·
    refine ⟨15521500768202493578124157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82781337430413299083328837 15521500768202493578124157)
    ·
      refine ⟨5820562788075935091796559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15521500768202493578124157 5820562788075935091796559)
      ·
        refine ⟨8730844182113902637694839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5820562788075935091796559 8730844182113902637694839)
        ·
          refine ⟨13096266273170853956542259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8730844182113902637694839 13096266273170853956542259)
          ·
            refine ⟨19644399409756280934813389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13096266273170853956542259 19644399409756280934813389)
            ·
              refine ⟨7366649778658605350555021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19644399409756280934813389 7366649778658605350555021)
              ·
                refine ⟨2762493666996977006458133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7366649778658605350555021 2762493666996977006458133)
                ·
                  refine ⟨129491890640483297177725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2762493666996977006458133 129491890640483297177725)
                  ·
                    rfl

theorem cell23_2269661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 3, 6].length) (baseStart_2269661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269661 prefixEnd_2269661 := by exact prefixLift 2269661
  have htrace : WordTrace (prefixWord ++ tailWord_2269661) baseStart_2269661 baseEnd_2269661 := by
    simpa [prefixWord, tailWord_2269661, baseEnd_2269661] using wordTrace_append hprefix tailTrace_2269661
  have hstable : (prefixWord ++ tailWord_2269661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269661).length < 2 ^ (prefixWord ++ tailWord_2269661).sum := by decide
  have hdescent : baseEnd_2269661 < baseStart_2269661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269704 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 5, 6]
def baseStart_2269704 : Nat := 118140960795 + 2269704 * 2 ^ 59
def prefixEnd_2269704 : Nat := 4983230072969 + 3 ^ 40 * 2269704 * 2
def baseEnd_2269704 : Nat := 388483031810831002120609

theorem tailTrace_2269704 : CollatzResearch.WordTrace tailWord_2269704 prefixEnd_2269704 388483031810831002120609 := by
  unfold tailWord_2269704
  simp only [CollatzResearch.WordTrace]
  refine ⟨41391452884628758713572083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55188603846171678284762777 41391452884628758713572083)
  ·
    refine ⟨62087179326943138070358125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41391452884628758713572083 62087179326943138070358125)
    ·
      refine ⟨23282692247603676776384297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62087179326943138070358125 23282692247603676776384297)
      ·
        refine ⟨17462019185702757582288223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23282692247603676776384297 17462019185702757582288223)
        ·
          refine ⟨26193028778554136373432335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17462019185702757582288223 26193028778554136373432335)
          ·
            refine ⟨39289543167831204560148503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26193028778554136373432335 39289543167831204560148503)
            ·
              refine ⟨58934314751746806840222755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39289543167831204560148503 58934314751746806840222755)
              ·
                refine ⟨88401472127620210260334133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58934314751746806840222755 88401472127620210260334133)
                ·
                  refine ⟨8287638011964394711906325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88401472127620210260334133 8287638011964394711906325)
                  ·
                    refine ⟨388483031810831002120609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8287638011964394711906325 388483031810831002120609)
                    ·
                      rfl

theorem cell23_2269704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 5, 6].length) (baseStart_2269704 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269704 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269704 prefixEnd_2269704 := by exact prefixLift 2269704
  have htrace : WordTrace (prefixWord ++ tailWord_2269704) baseStart_2269704 baseEnd_2269704 := by
    simpa [prefixWord, tailWord_2269704, baseEnd_2269704] using wordTrace_append hprefix tailTrace_2269704
  have hstable : (prefixWord ++ tailWord_2269704).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269704).length < 2 ^ (prefixWord ++ tailWord_2269704).sum := by decide
  have hdescent : baseEnd_2269704 < baseStart_2269704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269742 : List Nat := [4, 1, 3, 1, 3, 2, 2, 1, 1, 5]
def baseStart_2269742 : Nat := 118140960795 + 2269742 * 2 ^ 59
def prefixEnd_2269742 : Nat := 4983230072969 + 3 ^ 40 * 2269742 * 2
def baseEnd_2269742 : Nat := 388489535899121285895551

theorem tailTrace_2269742 : CollatzResearch.WordTrace tailWord_2269742 prefixEnd_2269742 388489535899121285895551 := by
  unfold tailWord_2269742
  simp only [CollatzResearch.WordTrace]
  refine ⟨10348036467889981239628435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55189527828746566611351653 10348036467889981239628435)
  ·
    refine ⟨15522054701834971859442653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10348036467889981239628435 15522054701834971859442653)
    ·
      refine ⟨5820770513188114447290995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15522054701834971859442653 5820770513188114447290995)
      ·
        refine ⟨8731155769782171670936493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5820770513188114447290995 8731155769782171670936493)
        ·
          refine ⟨3274183413668314376601185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8731155769782171670936493 3274183413668314376601185)
          ·
            refine ⟨2455637560251235782450889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3274183413668314376601185 2455637560251235782450889)
            ·
              refine ⟨1841728170188426836838167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2455637560251235782450889 1841728170188426836838167)
              ·
                refine ⟨2762592255282640255257251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1841728170188426836838167 2762592255282640255257251)
                ·
                  refine ⟨4143888382923960382885877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2762592255282640255257251 4143888382923960382885877)
                  ·
                    refine ⟨388489535899121285895551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 4143888382923960382885877 388489535899121285895551)
                    ·
                      rfl

theorem cell23_2269742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_2269742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269742 prefixEnd_2269742 := by exact prefixLift 2269742
  have htrace : WordTrace (prefixWord ++ tailWord_2269742) baseStart_2269742 baseEnd_2269742 := by
    simpa [prefixWord, tailWord_2269742, baseEnd_2269742] using wordTrace_append hprefix tailTrace_2269742
  have hstable : (prefixWord ++ tailWord_2269742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269742).length < 2 ^ (prefixWord ++ tailWord_2269742).sum := by decide
  have hdescent : baseEnd_2269742 < baseStart_2269742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269790 : List Nat := [4, 4, 1, 2, 2, 1, 1, 3, 1, 1, 3]
def baseStart_2269790 : Nat := 118140960795 + 2269790 * 2 ^ 59
def prefixEnd_2269790 : Nat := 4983230072969 + 3 ^ 40 * 2269790 * 2
def baseEnd_2269790 : Nat := 1165493254768779669886433

theorem tailTrace_2269790 : CollatzResearch.WordTrace tailWord_2269790 prefixEnd_2269790 1165493254768779669886433 := by
  unfold tailWord_2269790
  simp only [CollatzResearch.WordTrace]
  refine ⟨10348255305868244264346853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55190694964630636076516549 10348255305868244264346853)
  ·
    refine ⟨1940297869850295799565035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 10348255305868244264346853 1940297869850295799565035)
    ·
      refine ⟨2910446804775443699347553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1940297869850295799565035 2910446804775443699347553)
      ·
        refine ⟨2182835103581582774510665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2910446804775443699347553 2182835103581582774510665)
        ·
          refine ⟨1637126327686187080882999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2182835103581582774510665 1637126327686187080882999)
          ·
            refine ⟨2455689491529280621324499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1637126327686187080882999 2455689491529280621324499)
            ·
              refine ⟨3683534237293920931986749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2455689491529280621324499 3683534237293920931986749)
              ·
                refine ⟨1381325338985220349495031, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3683534237293920931986749 1381325338985220349495031)
                ·
                  refine ⟨2071988008477830524242547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1381325338985220349495031 2071988008477830524242547)
                  ·
                    refine ⟨3107982012716745786363821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2071988008477830524242547 3107982012716745786363821)
                    ·
                      refine ⟨1165493254768779669886433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3107982012716745786363821 1165493254768779669886433)
                      ·
                        rfl

theorem cell23_2269790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_2269790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269790 prefixEnd_2269790 := by exact prefixLift 2269790
  have htrace : WordTrace (prefixWord ++ tailWord_2269790) baseStart_2269790 baseEnd_2269790 := by
    simpa [prefixWord, tailWord_2269790, baseEnd_2269790] using wordTrace_append hprefix tailTrace_2269790
  have hstable : (prefixWord ++ tailWord_2269790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269790).length < 2 ^ (prefixWord ++ tailWord_2269790).sum := by decide
  have hdescent : baseEnd_2269790 < baseStart_2269790 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269831 : List Nat := [1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 4]
def baseStart_2269831 : Nat := 118140960795 + 2269831 * 2 ^ 59
def prefixEnd_2269831 : Nat := 4983230072969 + 3 ^ 40 * 2269831 * 2
def baseEnd_2269831 : Nat := 1165514307475614009473743

theorem tailTrace_2269831 : CollatzResearch.WordTrace tailWord_2269831 prefixEnd_2269831 1165514307475614009473743 := by
  unfold tailWord_2269831
  simp only [CollatzResearch.WordTrace]
  refine ⟨82787537839797418117017347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55191691893198278744678231 82787537839797418117017347)
  ·
    refine ⟨124181306759696127175526021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82787537839797418117017347 124181306759696127175526021)
    ·
      refine ⟨23283995017443023845411129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124181306759696127175526021 23283995017443023845411129)
      ·
        refine ⟨17462996263082267884058347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23283995017443023845411129 17462996263082267884058347)
        ·
          refine ⟨26194494394623401826087521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17462996263082267884058347 26194494394623401826087521)
          ·
            refine ⟨19645870795967551369565641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26194494394623401826087521 19645870795967551369565641)
            ·
              refine ⟨14734403096975663527174231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19645870795967551369565641 14734403096975663527174231)
              ·
                refine ⟨22101604645463495290761347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14734403096975663527174231 22101604645463495290761347)
                ·
                  refine ⟨33152406968195242936142021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22101604645463495290761347 33152406968195242936142021)
                  ·
                    refine ⟨6216076306536608050526629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 33152406968195242936142021 6216076306536608050526629)
                    ·
                      refine ⟨1165514307475614009473743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6216076306536608050526629 1165514307475614009473743)
                      ·
                        rfl

theorem cell23_2269831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_2269831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269831 prefixEnd_2269831 := by exact prefixLift 2269831
  have htrace : WordTrace (prefixWord ++ tailWord_2269831) baseStart_2269831 baseEnd_2269831 := by
    simpa [prefixWord, tailWord_2269831, baseEnd_2269831] using wordTrace_append hprefix tailTrace_2269831
  have hstable : (prefixWord ++ tailWord_2269831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269831).length < 2 ^ (prefixWord ++ tailWord_2269831).sum := by decide
  have hdescent : baseEnd_2269831 < baseStart_2269831 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269869 : List Nat := [1, 5, 2, 1, 1, 3, 2, 2, 2, 2, 2]
def baseStart_2269869 : Nat := 118140960795 + 2269869 * 2 ^ 59
def prefixEnd_2269869 : Nat := 4983230072969 + 3 ^ 40 * 2269869 * 2
def baseEnd_2269869 : Nat := 1165533819740484860798569

theorem tailTrace_2269869 : CollatzResearch.WordTrace tailWord_2269869 prefixEnd_2269869 1165533819740484860798569 := by
  unfold tailWord_2269869
  simp only [CollatzResearch.WordTrace]
  refine ⟨82788923813659750606900661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55192615875773167071267107 82788923813659750606900661)
  ·
    refine ⟨7761461607530601619396937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 82788923813659750606900661 7761461607530601619396937)
    ·
      refine ⟨5821096205647951214547703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7761461607530601619396937 5821096205647951214547703)
      ·
        refine ⟨8731644308471926821821555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5821096205647951214547703 8731644308471926821821555)
        ·
          refine ⟨13097466462707890232732333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8731644308471926821821555 13097466462707890232732333)
          ·
            refine ⟨4911549923515458837274625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13097466462707890232732333 4911549923515458837274625)
            ·
              refine ⟨3683662442636594127955969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4911549923515458837274625 3683662442636594127955969)
              ·
                refine ⟨2762746831977445595966977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3683662442636594127955969 2762746831977445595966977)
                ·
                  refine ⟨2072060123983084196975233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2762746831977445595966977 2072060123983084196975233)
                  ·
                    refine ⟨1554045092987313147731425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2072060123983084196975233 1554045092987313147731425)
                    ·
                      refine ⟨1165533819740484860798569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1554045092987313147731425 1165533819740484860798569)
                      ·
                        rfl

theorem cell23_2269869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 2, 2, 2, 2, 2].length) (baseStart_2269869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269869 prefixEnd_2269869 := by exact prefixLift 2269869
  have htrace : WordTrace (prefixWord ++ tailWord_2269869) baseStart_2269869 baseEnd_2269869 := by
    simpa [prefixWord, tailWord_2269869, baseEnd_2269869] using wordTrace_append hprefix tailTrace_2269869
  have hstable : (prefixWord ++ tailWord_2269869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269869).length < 2 ^ (prefixWord ++ tailWord_2269869).sum := by decide
  have hdescent : baseEnd_2269869 < baseStart_2269869 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269875 : List Nat := [1, 1, 1, 2, 3, 4, 4, 2, 5]
def baseStart_2269875 : Nat := 118140960795 + 2269875 * 2 ^ 59
def prefixEnd_2269875 : Nat := 4983230072969 + 3 ^ 40 * 2269875 * 2
def baseEnd_2269875 : Nat := 129504100069379093035949

theorem tailTrace_2269875 : CollatzResearch.WordTrace tailWord_2269875 prefixEnd_2269875 129504100069379093035949 := by
  unfold tailWord_2269875
  simp only [CollatzResearch.WordTrace]
  refine ⟨82789142651638013631619079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55192761767758675754412719 82789142651638013631619079)
  ·
    refine ⟨124183713977457020447428619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82789142651638013631619079 124183713977457020447428619)
    ·
      refine ⟨186275570966185530671142929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124183713977457020447428619 186275570966185530671142929)
      ·
        refine ⟨139706678224639148003357197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186275570966185530671142929 139706678224639148003357197)
        ·
          refine ⟨52390004334239680501258949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 139706678224639148003357197 52390004334239680501258949)
          ·
            refine ⟨9823125812669940093986053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52390004334239680501258949 9823125812669940093986053)
            ·
              refine ⟨1841836089875613767622385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9823125812669940093986053 1841836089875613767622385)
              ·
                refine ⟨1381377067406710325716789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1841836089875613767622385 1381377067406710325716789)
                ·
                  refine ⟨129504100069379093035949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1381377067406710325716789 129504100069379093035949)
                  ·
                    rfl

theorem cell23_2269875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 4, 4, 2, 5].length) (baseStart_2269875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269875 prefixEnd_2269875 := by exact prefixLift 2269875
  have htrace : WordTrace (prefixWord ++ tailWord_2269875) baseStart_2269875 baseEnd_2269875 := by
    simpa [prefixWord, tailWord_2269875, baseEnd_2269875] using wordTrace_append hprefix tailTrace_2269875
  have hstable : (prefixWord ++ tailWord_2269875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269875).length < 2 ^ (prefixWord ++ tailWord_2269875).sum := by decide
  have hdescent : baseEnd_2269875 < baseStart_2269875 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269925 : List Nat := [1, 3, 1, 4, 1, 2, 1, 2, 2, 4, 2]
def baseStart_2269925 : Nat := 118140960795 + 2269925 * 2 ^ 59
def prefixEnd_2269925 : Nat := 4983230072969 + 3 ^ 40 * 2269925 * 2
def baseEnd_2269925 : Nat := 1165562574657136641698311

theorem tailTrace_2269925 : CollatzResearch.WordTrace tailWord_2269925 prefixEnd_2269925 1165562574657136641698311 := by
  unfold tailWord_2269925
  simp only [CollatzResearch.WordTrace]
  refine ⟨82790966301456872170939229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55193977534304581447292819 82790966301456872170939229)
  ·
    refine ⟨31046612363046327064102211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82790966301456872170939229 31046612363046327064102211)
    ·
      refine ⟨46569918544569490596153317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31046612363046327064102211 46569918544569490596153317)
      ·
        refine ⟨8731859727106779486778747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46569918544569490596153317 8731859727106779486778747)
        ·
          refine ⟨13097789590660169230168121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8731859727106779486778747 13097789590660169230168121)
          ·
            refine ⟨9823342192995126922626091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13097789590660169230168121 9823342192995126922626091)
            ·
              refine ⟨14735013289492690383939137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9823342192995126922626091 14735013289492690383939137)
              ·
                refine ⟨11051259967119517787954353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14735013289492690383939137 11051259967119517787954353)
                ·
                  refine ⟨8288444975339638340965765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11051259967119517787954353 8288444975339638340965765)
                  ·
                    refine ⟨1554083432876182188931081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8288444975339638340965765 1554083432876182188931081)
                    ·
                      refine ⟨1165562574657136641698311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1554083432876182188931081 1165562574657136641698311)
                      ·
                        rfl

theorem cell23_2269925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 2, 2, 4, 2].length) (baseStart_2269925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269925 prefixEnd_2269925 := by exact prefixLift 2269925
  have htrace : WordTrace (prefixWord ++ tailWord_2269925) baseStart_2269925 baseEnd_2269925 := by
    simpa [prefixWord, tailWord_2269925, baseEnd_2269925] using wordTrace_append hprefix tailTrace_2269925
  have hstable : (prefixWord ++ tailWord_2269925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269925).length < 2 ^ (prefixWord ++ tailWord_2269925).sum := by decide
  have hdescent : baseEnd_2269925 < baseStart_2269925 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269935 : List Nat := [1, 1, 2, 1, 5, 3, 2, 1, 3, 4]
def baseStart_2269935 : Nat := 118140960795 + 2269935 * 2 ^ 59
def prefixEnd_2269935 : Nat := 4983230072969 + 3 ^ 40 * 2269935 * 2
def baseEnd_2269935 : Nat := 388522569821227200857755

theorem tailTrace_2269935 : CollatzResearch.WordTrace tailWord_2269935 prefixEnd_2269935 388522569821227200857755 := by
  unfold tailWord_2269935
  simp only [CollatzResearch.WordTrace]
  refine ⟨82791331031420643878803259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55194220687613762585868839 82791331031420643878803259)
  ·
    refine ⟨124186996547130965818204889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82791331031420643878803259 124186996547130965818204889)
    ·
      refine ⟨93140247410348224363653667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124186996547130965818204889 93140247410348224363653667)
      ·
        refine ⟨139710371115522336545480501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93140247410348224363653667 139710371115522336545480501)
        ·
          refine ⟨13097847292080219051138797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 139710371115522336545480501 13097847292080219051138797)
          ·
            refine ⟨4911692734530082144177049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13097847292080219051138797 4911692734530082144177049)
            ·
              refine ⟨3683769550897561608132787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4911692734530082144177049 3683769550897561608132787)
              ·
                refine ⟨5525654326346342412199181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3683769550897561608132787 5525654326346342412199181)
                ·
                  refine ⟨2072120372379878404574693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5525654326346342412199181 2072120372379878404574693)
                  ·
                    refine ⟨388522569821227200857755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2072120372379878404574693 388522569821227200857755)
                    ·
                      rfl

theorem cell23_2269935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 3, 2, 1, 3, 4].length) (baseStart_2269935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269935 prefixEnd_2269935 := by exact prefixLift 2269935
  have htrace : WordTrace (prefixWord ++ tailWord_2269935) baseStart_2269935 baseEnd_2269935 := by
    simpa [prefixWord, tailWord_2269935, baseEnd_2269935] using wordTrace_append hprefix tailTrace_2269935
  have hstable : (prefixWord ++ tailWord_2269935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269935).length < 2 ^ (prefixWord ++ tailWord_2269935).sum := by decide
  have hdescent : baseEnd_2269935 < baseStart_2269935 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2269951 : List Nat := [1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 6]
def baseStart_2269951 : Nat := 118140960795 + 2269951 * 2 ^ 59
def prefixEnd_2269951 : Nat := 4983230072969 + 3 ^ 40 * 2269951 * 2
def baseEnd_2269951 : Nat := 1165575925154153539973191

theorem tailTrace_2269951 : CollatzResearch.WordTrace tailWord_2269951 prefixEnd_2269951 1165575925154153539973191 := by
  unfold tailWord_2269951
  simp only [CollatzResearch.WordTrace]
  refine ⟨82791914599362678611385707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55194609732908452407590471 82791914599362678611385707)
  ·
    refine ⟨124187871899044017917078561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82791914599362678611385707 124187871899044017917078561)
    ·
      refine ⟨93140903924283013437808921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124187871899044017917078561 93140903924283013437808921)
      ·
        refine ⟨69855677943212260078356691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93140903924283013437808921 69855677943212260078356691)
        ·
          refine ⟨104783516914818390117535037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69855677943212260078356691 104783516914818390117535037)
          ·
            refine ⟨39293818843056896294075639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104783516914818390117535037 39293818843056896294075639)
            ·
              refine ⟨58940728264585344441113459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39293818843056896294075639 58940728264585344441113459)
              ·
                refine ⟨88411092396878016661670189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 58940728264585344441113459 88411092396878016661670189)
                ·
                  refine ⟨33154159648829256248126321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 88411092396878016661670189 33154159648829256248126321)
                  ·
                    refine ⟨24865619736621942186094741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 33154159648829256248126321 24865619736621942186094741)
                    ·
                      refine ⟨1165575925154153539973191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 24865619736621942186094741 1165575925154153539973191)
                      ·
                        rfl

theorem cell23_2269951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 1, 1, 3, 2, 6].length) (baseStart_2269951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2269951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2269951 prefixEnd_2269951 := by exact prefixLift 2269951
  have htrace : WordTrace (prefixWord ++ tailWord_2269951) baseStart_2269951 baseEnd_2269951 := by
    simpa [prefixWord, tailWord_2269951, baseEnd_2269951] using wordTrace_append hprefix tailTrace_2269951
  have hstable : (prefixWord ++ tailWord_2269951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2269951).length < 2 ^ (prefixWord ++ tailWord_2269951).sum := by decide
  have hdescent : baseEnd_2269951 < baseStart_2269951 := by decide
  rcases family_descends (prefixWord ++ tailWord_2269951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270008 : List Nat := [2, 1, 2, 1, 3, 2, 2, 3, 1, 6]
def baseStart_2270008 : Nat := 118140960795 + 2270008 * 2 ^ 59
def prefixEnd_2270008 : Nat := 4983230072969 + 3 ^ 40 * 2270008 * 2
def baseEnd_2270008 : Nat := 388535064517153272320143

theorem tailTrace_2270008 : CollatzResearch.WordTrace tailWord_2270008 prefixEnd_2270008 388535064517153272320143 := by
  unfold tailWord_2270008
  simp only [CollatzResearch.WordTrace]
  refine ⟨41396996780078088673105339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55195995706770784897473785 41396996780078088673105339)
  ·
    refine ⟨62095495170117133009658009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41396996780078088673105339 62095495170117133009658009)
    ·
      refine ⟨46571621377587849757243507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62095495170117133009658009 46571621377587849757243507)
      ·
        refine ⟨69857432066381774635865261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46571621377587849757243507 69857432066381774635865261)
        ·
          refine ⟨26196537024893165488449473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 69857432066381774635865261 26196537024893165488449473)
          ·
            refine ⟨19647402768669874116337105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26196537024893165488449473 19647402768669874116337105)
            ·
              refine ⟨14735552076502405587252829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19647402768669874116337105 14735552076502405587252829)
              ·
                refine ⟨5525832028688402095219811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14735552076502405587252829 5525832028688402095219811)
                ·
                  refine ⟨8288748043032603142829717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5525832028688402095219811 8288748043032603142829717)
                  ·
                    refine ⟨388535064517153272320143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 8288748043032603142829717 388535064517153272320143)
                    ·
                      rfl

theorem cell23_2270008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 2, 3, 1, 6].length) (baseStart_2270008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270008 prefixEnd_2270008 := by exact prefixLift 2270008
  have htrace : WordTrace (prefixWord ++ tailWord_2270008) baseStart_2270008 baseEnd_2270008 := by
    simpa [prefixWord, tailWord_2270008, baseEnd_2270008] using wordTrace_append hprefix tailTrace_2270008
  have hstable : (prefixWord ++ tailWord_2270008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270008).length < 2 ^ (prefixWord ++ tailWord_2270008).sum := by decide
  have hdescent : baseEnd_2270008 < baseStart_2270008 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270015 : List Nat := [1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 4]
def baseStart_2270015 : Nat := 118140960795 + 2270015 * 2 ^ 59
def prefixEnd_2270015 : Nat := 4983230072969 + 3 ^ 40 * 2270015 * 2
def baseEnd_2270015 : Nat := 1165608787916041289572897

theorem tailTrace_2270015 : CollatzResearch.WordTrace tailWord_2270015 prefixEnd_2270015 1165608787916041289572897 := by
  unfold tailWord_2270015
  simp only [CollatzResearch.WordTrace]
  refine ⟨82794248871130817541715499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55196165914087211694476999 82794248871130817541715499)
  ·
    refine ⟨124191373306696226312573249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82794248871130817541715499 124191373306696226312573249)
    ·
      refine ⟨93143529980022169734429937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124191373306696226312573249 93143529980022169734429937)
      ·
        refine ⟨69857647485016627300822453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93143529980022169734429937 69857647485016627300822453)
        ·
          refine ⟨6549154451720308809452105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 69857647485016627300822453 6549154451720308809452105)
          ·
            refine ⟨4911865838790231607089079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6549154451720308809452105 4911865838790231607089079)
            ·
              refine ⟨7367798758185347410633619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4911865838790231607089079 7367798758185347410633619)
              ·
                refine ⟨11051698137278021115950429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7367798758185347410633619 11051698137278021115950429)
                ·
                  refine ⟨4144386801479257918481411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11051698137278021115950429 4144386801479257918481411)
                  ·
                    refine ⟨6216580202218886877722117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4144386801479257918481411 6216580202218886877722117)
                    ·
                      refine ⟨1165608787916041289572897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6216580202218886877722117 1165608787916041289572897)
                      ·
                        rfl

theorem cell23_2270015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 3, 1, 4].length) (baseStart_2270015 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270015 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270015 prefixEnd_2270015 := by exact prefixLift 2270015
  have htrace : WordTrace (prefixWord ++ tailWord_2270015) baseStart_2270015 baseEnd_2270015 := by
    simpa [prefixWord, tailWord_2270015, baseEnd_2270015] using wordTrace_append hprefix tailTrace_2270015
  have hstable : (prefixWord ++ tailWord_2270015).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270015).length < 2 ^ (prefixWord ++ tailWord_2270015).sum := by decide
  have hdescent : baseEnd_2270015 < baseStart_2270015 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270035 : List Nat := [1, 1, 1, 2, 1, 1, 3, 7, 1, 2, 3]
def baseStart_2270035 : Nat := 118140960795 + 2270035 * 2 ^ 59
def prefixEnd_2270035 : Nat := 4983230072969 + 3 ^ 40 * 2270035 * 2
def baseEnd_2270035 : Nat := 1165619057529131211322805

theorem tailTrace_2270035 : CollatzResearch.WordTrace tailWord_2270035 prefixEnd_2270035 1165619057529131211322805 := by
  unfold tailWord_2270035
  simp only [CollatzResearch.WordTrace]
  refine ⟨82794978331058360957443559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55196652220705573971629039 82794978331058360957443559)
  ·
    refine ⟨124192467496587541436165339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82794978331058360957443559 124192467496587541436165339)
    ·
      refine ⟨186288701244881312154248009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124192467496587541436165339 186288701244881312154248009)
      ·
        refine ⟨139716525933660984115686007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 186288701244881312154248009 139716525933660984115686007)
        ·
          refine ⟨209574788900491476173529011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139716525933660984115686007 209574788900491476173529011)
          ·
            refine ⟨314362183350737214260293517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 209574788900491476173529011 314362183350737214260293517)
            ·
              refine ⟨117885818756526455347610069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 314362183350737214260293517 117885818756526455347610069)
              ·
                refine ⟨2762948877106088797209611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 117885818756526455347610069 2762948877106088797209611)
                ·
                  refine ⟨4144423315659133195814417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2762948877106088797209611 4144423315659133195814417)
                  ·
                    refine ⟨3108317486744349896860813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4144423315659133195814417 3108317486744349896860813)
                    ·
                      refine ⟨1165619057529131211322805, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3108317486744349896860813 1165619057529131211322805)
                      ·
                        rfl

theorem cell23_2270035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 2, 3].length) (baseStart_2270035 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270035 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270035 prefixEnd_2270035 := by exact prefixLift 2270035
  have htrace : WordTrace (prefixWord ++ tailWord_2270035) baseStart_2270035 baseEnd_2270035 := by
    simpa [prefixWord, tailWord_2270035, baseEnd_2270035] using wordTrace_append hprefix tailTrace_2270035
  have hstable : (prefixWord ++ tailWord_2270035).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270035).length < 2 ^ (prefixWord ++ tailWord_2270035).sum := by decide
  have hdescent : baseEnd_2270035 < baseStart_2270035 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270038 : List Nat := [5, 2, 16]
def baseStart_2270038 : Nat := 118140960795 + 2270038 * 2 ^ 59
def prefixEnd_2270038 : Nat := 4983230072969 + 3 ^ 40 * 2270038 * 2
def baseEnd_2270038 : Nat := 177658984601599557931

theorem tailTrace_2270038 : CollatzResearch.WordTrace tailWord_2270038 prefixEnd_2270038 177658984601599557931 := by
  unfold tailWord_2270038
  simp only [CollatzResearch.WordTrace]
  refine ⟨5174692984377968279362673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55196725166698328313201845 5174692984377968279362673)
  ·
    refine ⟨3881019738283476209522005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5174692984377968279362673 3881019738283476209522005)
    ·
      refine ⟨177658984601599557931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 16 3881019738283476209522005 177658984601599557931)
      ·
        rfl

theorem cell23_2270038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 16].length) (baseStart_2270038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270038 prefixEnd_2270038 := by exact prefixLift 2270038
  have htrace : WordTrace (prefixWord ++ tailWord_2270038) baseStart_2270038 baseEnd_2270038 := by
    simpa [prefixWord, tailWord_2270038, baseEnd_2270038] using wordTrace_append hprefix tailTrace_2270038
  have hstable : (prefixWord ++ tailWord_2270038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270038).length < 2 ^ (prefixWord ++ tailWord_2270038).sum := by decide
  have hdescent : baseEnd_2270038 < baseStart_2270038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270042 : List Nat := [3, 1, 1, 2, 1, 5, 2, 2, 2, 4]
def baseStart_2270042 : Nat := 118140960795 + 2270042 * 2 ^ 59
def prefixEnd_2270042 : Nat := 4983230072969 + 3 ^ 40 * 2270042 * 2
def baseEnd_2270042 : Nat := 388540883964570894645091

theorem tailTrace_2270042 : CollatzResearch.WordTrace tailWord_2270042 prefixEnd_2270042 388540883964570894645091 := by
  unfold tailWord_2270042
  simp only [CollatzResearch.WordTrace]
  refine ⟨20698808410508250288237095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55196822428022000768632253 20698808410508250288237095)
  ·
    refine ⟨31048212615762375432355643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20698808410508250288237095 31048212615762375432355643)
    ·
      refine ⟨46572318923643563148533465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31048212615762375432355643 46572318923643563148533465)
      ·
        refine ⟨34929239192732672361400099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46572318923643563148533465 34929239192732672361400099)
        ·
          refine ⟨52393858789099008542100149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34929239192732672361400099 52393858789099008542100149)
          ·
            refine ⟨4911924261478032050821889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52393858789099008542100149 4911924261478032050821889)
            ·
              refine ⟨3683943196108524038116417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4911924261478032050821889 3683943196108524038116417)
              ·
                refine ⟨2762957397081393028587313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3683943196108524038116417 2762957397081393028587313)
                ·
                  refine ⟨2072218047811044771440485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2762957397081393028587313 2072218047811044771440485)
                  ·
                    refine ⟨388540883964570894645091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 2072218047811044771440485 388540883964570894645091)
                    ·
                      rfl

theorem cell23_2270042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 2, 2, 2, 4].length) (baseStart_2270042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270042 prefixEnd_2270042 := by exact prefixLift 2270042
  have htrace : WordTrace (prefixWord ++ tailWord_2270042) baseStart_2270042 baseEnd_2270042 := by
    simpa [prefixWord, tailWord_2270042, baseEnd_2270042] using wordTrace_append hprefix tailTrace_2270042
  have hstable : (prefixWord ++ tailWord_2270042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270042).length < 2 ^ (prefixWord ++ tailWord_2270042).sum := by decide
  have hdescent : baseEnd_2270042 < baseStart_2270042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270055 : List Nat := [1, 1, 5, 1, 2, 4, 1, 8]
def baseStart_2270055 : Nat := 118140960795 + 2270055 * 2 ^ 59
def prefixEnd_2270055 : Nat := 4983230072969 + 3 ^ 40 * 2270055 * 2
def baseEnd_2270055 : Nat := 43171456560823004928619

theorem tailTrace_2270055 : CollatzResearch.WordTrace tailWord_2270055 prefixEnd_2270055 43171456560823004928619 := by
  unfold tailWord_2270055
  simp only [CollatzResearch.WordTrace]
  refine ⟨82795707790985904373171619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55197138527323936248781079 82795707790985904373171619)
  ·
    refine ⟨124193561686478856559757429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82795707790985904373171619 124193561686478856559757429)
    ·
      refine ⟨11643146408107392802477259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 124193561686478856559757429 11643146408107392802477259)
      ·
        refine ⟨17464719612161089203715889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11643146408107392802477259 17464719612161089203715889)
        ·
          refine ⟨13098539709120816902786917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17464719612161089203715889 13098539709120816902786917)
          ·
            refine ⟨2455976195460153169272547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13098539709120816902786917 2455976195460153169272547)
            ·
              refine ⟨3683964293190229753908821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2455976195460153169272547 3683964293190229753908821)
              ·
                refine ⟨43171456560823004928619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 3683964293190229753908821 43171456560823004928619)
                ·
                  rfl

theorem cell23_2270055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 8].length) (baseStart_2270055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270055 prefixEnd_2270055 := by exact prefixLift 2270055
  have htrace : WordTrace (prefixWord ++ tailWord_2270055) baseStart_2270055 baseEnd_2270055 := by
    simpa [prefixWord, tailWord_2270055, baseEnd_2270055] using wordTrace_append hprefix tailTrace_2270055
  have hstable : (prefixWord ++ tailWord_2270055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270055).length < 2 ^ (prefixWord ++ tailWord_2270055).sum := by decide
  have hdescent : baseEnd_2270055 < baseStart_2270055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270065 : List Nat := [1, 2, 2, 2, 1, 4, 1, 3, 1, 3, 3]
def baseStart_2270065 : Nat := 118140960795 + 2270065 * 2 ^ 59
def prefixEnd_2270065 : Nat := 4983230072969 + 3 ^ 40 * 2270065 * 2
def baseEnd_2270065 : Nat := 1165634461948766093947667

theorem tailTrace_2270065 : CollatzResearch.WordTrace tailWord_2270065 prefixEnd_2270065 1165634461948766093947667 := by
  unfold tailWord_2270065
  simp only [CollatzResearch.WordTrace]
  refine ⟨82796072520949676081035649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55197381680633117387357099 82796072520949676081035649)
  ·
    refine ⟨62097054390712257060776737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82796072520949676081035649 62097054390712257060776737)
    ·
      refine ⟨46572790793034192795582553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62097054390712257060776737 46572790793034192795582553)
      ·
        refine ⟨34929593094775644596686915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46572790793034192795582553 34929593094775644596686915)
        ·
          refine ⟨52394389642163466895030373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34929593094775644596686915 52394389642163466895030373)
          ·
            refine ⟨9823948057905650042818195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52394389642163466895030373 9823948057905650042818195)
            ·
              refine ⟨14735922086858475064227293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9823948057905650042818195 14735922086858475064227293)
              ·
                refine ⟨5525970782571928149085235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14735922086858475064227293 5525970782571928149085235)
                ·
                  refine ⟨8288956173857892223627853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5525970782571928149085235 8288956173857892223627853)
                  ·
                    refine ⟨3108358565196709583860445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8288956173857892223627853 3108358565196709583860445)
                    ·
                      refine ⟨1165634461948766093947667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3108358565196709583860445 1165634461948766093947667)
                      ·
                        rfl

theorem cell23_2270065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 1, 3, 1, 3, 3].length) (baseStart_2270065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270065 prefixEnd_2270065 := by exact prefixLift 2270065
  have htrace : WordTrace (prefixWord ++ tailWord_2270065) baseStart_2270065 baseEnd_2270065 := by
    simpa [prefixWord, tailWord_2270065, baseEnd_2270065] using wordTrace_append hprefix tailTrace_2270065
  have hstable : (prefixWord ++ tailWord_2270065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270065).length < 2 ^ (prefixWord ++ tailWord_2270065).sum := by decide
  have hdescent : baseEnd_2270065 < baseStart_2270065 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270134 : List Nat := [5, 1, 4, 1, 1, 2, 1, 3, 1, 2, 2]
def baseStart_2270134 : Nat := 118140960795 + 2270134 * 2 ^ 59
def prefixEnd_2270134 : Nat := 4983230072969 + 3 ^ 40 * 2270134 * 2
def baseEnd_2270134 : Nat := 1165669892113926323984851

theorem tailTrace_2270134 : CollatzResearch.WordTrace tailWord_2270134 prefixEnd_2270134 1165669892113926323984851 := by
  unfold tailWord_2270134
  simp only [CollatzResearch.WordTrace]
  refine ⟨5174911822356231304081091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55199059438466467243531637 5174911822356231304081091)
  ·
    refine ⟨7762367733534346956121637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5174911822356231304081091 7762367733534346956121637)
    ·
      refine ⟨1455443950037690054272807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7762367733534346956121637 1455443950037690054272807)
      ·
        refine ⟨2183165925056535081409211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1455443950037690054272807 2183165925056535081409211)
        ·
          refine ⟨3274748887584802622113817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2183165925056535081409211 3274748887584802622113817)
          ·
            refine ⟨2456061665688601966585363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3274748887584802622113817 2456061665688601966585363)
            ·
              refine ⟨3684092498532902949878045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2456061665688601966585363 3684092498532902949878045)
              ·
                refine ⟨1381534686949838606204267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3684092498532902949878045 1381534686949838606204267)
                ·
                  refine ⟨2072302030424757909306401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1381534686949838606204267 2072302030424757909306401)
                  ·
                    refine ⟨1554226522818568431979801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2072302030424757909306401 1554226522818568431979801)
                    ·
                      refine ⟨1165669892113926323984851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1554226522818568431979801 1165669892113926323984851)
                      ·
                        rfl

theorem cell23_2270134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_2270134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270134 prefixEnd_2270134 := by exact prefixLift 2270134
  have htrace : WordTrace (prefixWord ++ tailWord_2270134) baseStart_2270134 baseEnd_2270134 := by
    simpa [prefixWord, tailWord_2270134, baseEnd_2270134] using wordTrace_append hprefix tailTrace_2270134
  have hstable : (prefixWord ++ tailWord_2270134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270134).length < 2 ^ (prefixWord ++ tailWord_2270134).sum := by decide
  have hdescent : baseEnd_2270134 < baseStart_2270134 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270162 : List Nat := [3, 2, 2, 3, 1, 1, 3, 1, 7]
def baseStart_2270162 : Nat := 118140960795 + 2270162 * 2 ^ 59
def prefixEnd_2270162 : Nat := 4983230072969 + 3 ^ 40 * 2270162 * 2
def baseEnd_2270162 : Nat := 129520474396916912714969

theorem tailTrace_2270162 : CollatzResearch.WordTrace tailWord_2270162 prefixEnd_2270162 129520474396916912714969 := by
  unfold tailWord_2270162
  simp only [CollatzResearch.WordTrace]
  refine ⟨20699902600399565411829185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55199740267732174431544493 20699902600399565411829185)
  ·
    refine ⟨15524926950299674058871889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20699902600399565411829185 15524926950299674058871889)
    ·
      refine ⟨11643695212724755544153917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15524926950299674058871889 11643695212724755544153917)
      ·
        refine ⟨4366385704771783329057719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11643695212724755544153917 4366385704771783329057719)
        ·
          refine ⟨6549578557157674993586579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4366385704771783329057719 6549578557157674993586579)
          ·
            refine ⟨9824367835736512490379869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6549578557157674993586579 9824367835736512490379869)
            ·
              refine ⟨3684137938401192183892451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9824367835736512490379869 3684137938401192183892451)
              ·
                refine ⟨5526206907601788275838677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3684137938401192183892451 5526206907601788275838677)
                ·
                  refine ⟨129520474396916912714969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 5526206907601788275838677 129520474396916912714969)
                  ·
                    rfl

theorem cell23_2270162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 3, 1, 7].length) (baseStart_2270162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270162 prefixEnd_2270162 := by exact prefixLift 2270162
  have htrace : WordTrace (prefixWord ++ tailWord_2270162) baseStart_2270162 baseEnd_2270162 := by
    simpa [prefixWord, tailWord_2270162, baseEnd_2270162] using wordTrace_append hprefix tailTrace_2270162
  have hstable : (prefixWord ++ tailWord_2270162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270162).length < 2 ^ (prefixWord ++ tailWord_2270162).sum := by decide
  have hdescent : baseEnd_2270162 < baseStart_2270162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270173 : List Nat := [1, 4, 3, 1, 2, 1, 4, 1, 2, 2, 2]
def baseStart_2270173 : Nat := 118140960795 + 2270173 * 2 ^ 59
def prefixEnd_2270173 : Nat := 4983230072969 + 3 ^ 40 * 2270173 * 2
def baseEnd_2270173 : Nat := 1165689917859451671397171

theorem tailTrace_2270173 : CollatzResearch.WordTrace tailWord_2270173 prefixEnd_2270173 1165689917859451671397171 := by
  unfold tailWord_2270173
  simp only [CollatzResearch.WordTrace]
  refine ⟨82800011604558410525967173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55200007736372273683978115 82800011604558410525967173)
  ·
    refine ⟨15525002175854701973618845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82800011604558410525967173 15525002175854701973618845)
    ·
      refine ⟨5821875815945513240107067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15525002175854701973618845 5821875815945513240107067)
      ·
        refine ⟨8732813723918269860160601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5821875815945513240107067 8732813723918269860160601)
        ·
          refine ⟨6549610292938702395120451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8732813723918269860160601 6549610292938702395120451)
          ·
            refine ⟨9824415439408053592680677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6549610292938702395120451 9824415439408053592680677)
            ·
              refine ⟨1842077894889010048627627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9824415439408053592680677 1842077894889010048627627)
              ·
                refine ⟨2763116842333515072941441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1842077894889010048627627 2763116842333515072941441)
                ·
                  refine ⟨2072337631750136304706081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2763116842333515072941441 2072337631750136304706081)
                  ·
                    refine ⟨1554253223812602228529561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2072337631750136304706081 1554253223812602228529561)
                    ·
                      refine ⟨1165689917859451671397171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1554253223812602228529561 1165689917859451671397171)
                      ·
                        rfl

theorem cell23_2270173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 4, 1, 2, 2, 2].length) (baseStart_2270173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270173 prefixEnd_2270173 := by exact prefixLift 2270173
  have htrace : WordTrace (prefixWord ++ tailWord_2270173) baseStart_2270173 baseEnd_2270173 := by
    simpa [prefixWord, tailWord_2270173, baseEnd_2270173] using wordTrace_append hprefix tailTrace_2270173
  have hstable : (prefixWord ++ tailWord_2270173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270173).length < 2 ^ (prefixWord ++ tailWord_2270173).sum := by decide
  have hdescent : baseEnd_2270173 < baseStart_2270173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270215 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 5]
def baseStart_2270215 : Nat := 118140960795 + 2270215 * 2 ^ 59
def prefixEnd_2270215 : Nat := 4983230072969 + 3 ^ 40 * 2270215 * 2
def baseEnd_2270215 : Nat := 1165711484046940507071977

theorem tailTrace_2270215 : CollatzResearch.WordTrace tailWord_2270215 prefixEnd_2270215 1165711484046940507071977 := by
  unfold tailWord_2270215
  simp only [CollatzResearch.WordTrace]
  refine ⟨82801543470406251698996099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55201028980270834465997399 82801543470406251698996099)
  ·
    refine ⟨124202315205609377548494149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82801543470406251698996099 124202315205609377548494149)
    ·
      refine ⟨23287934101051758290342653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124202315205609377548494149 23287934101051758290342653)
      ·
        refine ⟨8732975287894409358878495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23287934101051758290342653 8732975287894409358878495)
        ·
          refine ⟨13099462931841614038317743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8732975287894409358878495 13099462931841614038317743)
          ·
            refine ⟨19649194397762421057476615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13099462931841614038317743 19649194397762421057476615)
            ·
              refine ⟨29473791596643631586214923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19649194397762421057476615 29473791596643631586214923)
              ·
                refine ⟨44210687394965447379322385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29473791596643631586214923 44210687394965447379322385)
                ·
                  refine ⟨33158015546224085534491789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44210687394965447379322385 33158015546224085534491789)
                  ·
                    refine ⟨12434255829834032075434421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 33158015546224085534491789 12434255829834032075434421)
                    ·
                      refine ⟨1165711484046940507071977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 12434255829834032075434421 1165711484046940507071977)
                      ·
                        rfl

theorem cell23_2270215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_2270215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270215 prefixEnd_2270215 := by exact prefixLift 2270215
  have htrace : WordTrace (prefixWord ++ tailWord_2270215) baseStart_2270215 baseEnd_2270215 := by
    simpa [prefixWord, tailWord_2270215, baseEnd_2270215] using wordTrace_append hprefix tailTrace_2270215
  have hstable : (prefixWord ++ tailWord_2270215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270215).length < 2 ^ (prefixWord ++ tailWord_2270215).sum := by decide
  have hdescent : baseEnd_2270215 < baseStart_2270215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270229 : List Nat := [1, 3, 2, 1, 4, 2, 1, 1, 2, 4, 2]
def baseStart_2270229 : Nat := 118140960795 + 2270229 * 2 ^ 59
def prefixEnd_2270229 : Nat := 4983230072969 + 3 ^ 40 * 2270229 * 2
def baseEnd_2270229 : Nat := 1165718672776103452296913

theorem tailTrace_2270229 : CollatzResearch.WordTrace tailWord_2270229 prefixEnd_2270229 1165718672776103452296913 := by
  unfold tailWord_2270229
  simp only [CollatzResearch.WordTrace]
  refine ⟨82802054092355532090005741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55201369394903688060003827 82802054092355532090005741)
  ·
    refine ⟨31050770284633324533752153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 82802054092355532090005741 31050770284633324533752153)
    ·
      refine ⟨23288077713474993400314115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31050770284633324533752153 23288077713474993400314115)
      ·
        refine ⟨34932116570212490100471173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23288077713474993400314115 34932116570212490100471173)
        ·
          refine ⟨6549771856914841893838345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 34932116570212490100471173 6549771856914841893838345)
          ·
            refine ⟨4912328892686131420378759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6549771856914841893838345 4912328892686131420378759)
            ·
              refine ⟨7368493339029197130568139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4912328892686131420378759 7368493339029197130568139)
              ·
                refine ⟨11052740008543795695852209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7368493339029197130568139 11052740008543795695852209)
                ·
                  refine ⟨8289555006407846771889157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11052740008543795695852209 8289555006407846771889157)
                  ·
                    refine ⟨1554291563701471269729217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8289555006407846771889157 1554291563701471269729217)
                    ·
                      refine ⟨1165718672776103452296913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1554291563701471269729217 1165718672776103452296913)
                      ·
                        rfl

theorem cell23_2270229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 4, 2].length) (baseStart_2270229 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270229 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270229 prefixEnd_2270229 := by exact prefixLift 2270229
  have htrace : WordTrace (prefixWord ++ tailWord_2270229) baseStart_2270229 baseEnd_2270229 := by
    simpa [prefixWord, tailWord_2270229, baseEnd_2270229] using wordTrace_append hprefix tailTrace_2270229
  have hstable : (prefixWord ++ tailWord_2270229).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270229).length < 2 ^ (prefixWord ++ tailWord_2270229).sum := by decide
  have hdescent : baseEnd_2270229 < baseStart_2270229 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270269 : List Nat := [1, 4, 1, 3, 1, 4, 1, 2, 6]
def baseStart_2270269 : Nat := 118140960795 + 2270269 * 2 ^ 59
def prefixEnd_2270269 : Nat := 4983230072969 + 3 ^ 40 * 2270269 * 2
def baseEnd_2270269 : Nat := 129526579111364810644081

theorem tailTrace_2270269 : CollatzResearch.WordTrace tailWord_2270269 prefixEnd_2270269 129526579111364810644081 := by
  unfold tailWord_2270269
  simp only [CollatzResearch.WordTrace]
  refine ⟨82803513012210618921461861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55202342008140412614307907 82803513012210618921461861)
  ·
    refine ⟨15525658689789491047774099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 82803513012210618921461861 15525658689789491047774099)
    ·
      refine ⟨23288488034684236571661149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15525658689789491047774099 23288488034684236571661149)
      ·
        refine ⟨8733183013006588714372931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23288488034684236571661149 8733183013006588714372931)
        ·
          refine ⟨13099774519509883071559397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8733183013006588714372931 13099774519509883071559397)
          ·
            refine ⟨2456207722408103075917387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13099774519509883071559397 2456207722408103075917387)
            ·
              refine ⟨3684311583612154613876081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2456207722408103075917387 3684311583612154613876081)
              ·
                refine ⟨2763233687709115960407061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3684311583612154613876081 2763233687709115960407061)
                ·
                  refine ⟨129526579111364810644081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2763233687709115960407061 129526579111364810644081)
                  ·
                    rfl

theorem cell23_2270269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 1, 2, 6].length) (baseStart_2270269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270269 prefixEnd_2270269 := by exact prefixLift 2270269
  have htrace : WordTrace (prefixWord ++ tailWord_2270269) baseStart_2270269 baseEnd_2270269 := by
    simpa [prefixWord, tailWord_2270269, baseEnd_2270269] using wordTrace_append hprefix tailTrace_2270269
  have hstable : (prefixWord ++ tailWord_2270269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270269).length < 2 ^ (prefixWord ++ tailWord_2270269).sum := by decide
  have hdescent : baseEnd_2270269 < baseStart_2270269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270279 : List Nat := [1, 1, 4, 1, 3, 2, 1, 3, 3, 1, 3]
def baseStart_2270279 : Nat := 118140960795 + 2270279 * 2 ^ 59
def prefixEnd_2270279 : Nat := 4983230072969 + 3 ^ 40 * 2270279 * 2
def baseEnd_2270279 : Nat := 1165744346808828256671683

theorem tailTrace_2270279 : CollatzResearch.WordTrace tailWord_2270279 prefixEnd_2270279 1165744346808828256671683 := by
  unfold tailWord_2270279
  simp only [CollatzResearch.WordTrace]
  refine ⟨82803877742174390629325891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55202585161449593752883927 82803877742174390629325891)
  ·
    refine ⟨124205816613261585943988837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82803877742174390629325891 124205816613261585943988837)
    ·
      refine ⟨23288590614986547364497907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 124205816613261585943988837 23288590614986547364497907)
      ·
        refine ⟨34932885922479821046746861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23288590614986547364497907 34932885922479821046746861)
        ·
          refine ⟨13099832220929932892530073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 34932885922479821046746861 13099832220929932892530073)
          ·
            refine ⟨9824874165697449669397555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13099832220929932892530073 9824874165697449669397555)
            ·
              refine ⟨14737311248546174504096333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9824874165697449669397555 14737311248546174504096333)
              ·
                refine ⟨5526491718204815439036125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14737311248546174504096333 5526491718204815439036125)
                ·
                  refine ⟨2072434394326805789638547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5526491718204815439036125 2072434394326805789638547)
                  ·
                    refine ⟨3108651591490208684457821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2072434394326805789638547 3108651591490208684457821)
                    ·
                      refine ⟨1165744346808828256671683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3108651591490208684457821 1165744346808828256671683)
                      ·
                        rfl

theorem cell23_2270279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 3, 1, 3].length) (baseStart_2270279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270279 prefixEnd_2270279 := by exact prefixLift 2270279
  have htrace : WordTrace (prefixWord ++ tailWord_2270279) baseStart_2270279 baseEnd_2270279 := by
    simpa [prefixWord, tailWord_2270279, baseEnd_2270279] using wordTrace_append hprefix tailTrace_2270279
  have hstable : (prefixWord ++ tailWord_2270279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270279).length < 2 ^ (prefixWord ++ tailWord_2270279).sum := by decide
  have hdescent : baseEnd_2270279 < baseStart_2270279 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270306 : List Nat := [3, 3, 2, 2, 1, 1, 2, 1, 1, 5, 2]
def baseStart_2270306 : Nat := 118140960795 + 2270306 * 2 ^ 59
def prefixEnd_2270306 : Nat := 4983230072969 + 3 ^ 40 * 2270306 * 2
def baseEnd_2270306 : Nat := 1165758210786499651034059

theorem tailTrace_2270306 : CollatzResearch.WordTrace tailWord_2270306 prefixEnd_2270306 1165758210786499651034059 := by
  unfold tailWord_2270306
  simp only [CollatzResearch.WordTrace]
  refine ⟨20701215628269143560139693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55203241675384382827039181 20701215628269143560139693)
  ·
    refine ⟨7762955860600928835052385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20701215628269143560139693 7762955860600928835052385)
    ·
      refine ⟨5822216895450696626289289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7762955860600928835052385 5822216895450696626289289)
      ·
        refine ⟨4366662671588022469716967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5822216895450696626289289 4366662671588022469716967)
        ·
          refine ⟨6549994007382033704575451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4366662671588022469716967 6549994007382033704575451)
          ·
            refine ⟨9824991011073050556863177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6549994007382033704575451 9824991011073050556863177)
            ·
              refine ⟨7368743258304787917647383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9824991011073050556863177 7368743258304787917647383)
              ·
                refine ⟨11053114887457181876471075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7368743258304787917647383 11053114887457181876471075)
                ·
                  refine ⟨16579672331185772814706613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11053114887457181876471075 16579672331185772814706613)
                  ·
                    refine ⟨1554344281048666201378745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 16579672331185772814706613 1554344281048666201378745)
                    ·
                      refine ⟨1165758210786499651034059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1554344281048666201378745 1165758210786499651034059)
                      ·
                        rfl

theorem cell23_2270306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 1, 1, 2, 1, 1, 5, 2].length) (baseStart_2270306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270306 prefixEnd_2270306 := by exact prefixLift 2270306
  have htrace : WordTrace (prefixWord ++ tailWord_2270306) baseStart_2270306 baseEnd_2270306 := by
    simpa [prefixWord, tailWord_2270306, baseEnd_2270306] using wordTrace_append hprefix tailTrace_2270306
  have hstable : (prefixWord ++ tailWord_2270306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270306).length < 2 ^ (prefixWord ++ tailWord_2270306).sum := by decide
  have hdescent : baseEnd_2270306 < baseStart_2270306 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270313 : List Nat := [1, 2, 1, 1, 1, 8, 1, 3, 1, 1, 3]
def baseStart_2270313 : Nat := 118140960795 + 2270313 * 2 ^ 59
def prefixEnd_2270313 : Nat := 4983230072969 + 3 ^ 40 * 2270313 * 2
def baseEnd_2270313 : Nat := 1165761805151081123646527

theorem tailTrace_2270313 : CollatzResearch.WordTrace tailWord_2270313 prefixEnd_2270313 1165761805151081123646527 := by
  unfold tailWord_2270313
  simp only [CollatzResearch.WordTrace]
  refine ⟨82805117824051214436063593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55203411882700809624042395 82805117824051214436063593)
  ·
    refine ⟨62103838368038410827047695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82805117824051214436063593 62103838368038410827047695)
    ·
      refine ⟨93155757552057616240571543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62103838368038410827047695 93155757552057616240571543)
      ·
        refine ⟨139733636328086424360857315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93155757552057616240571543 139733636328086424360857315)
        ·
          refine ⟨209600454492129636541285973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 139733636328086424360857315 209600454492129636541285973)
          ·
            refine ⟨2456255326079644178218195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 209600454492129636541285973 2456255326079644178218195)
            ·
              refine ⟨3684382989119466267327293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2456255326079644178218195 3684382989119466267327293)
              ·
                refine ⟨1381643620919799850247735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3684382989119466267327293 1381643620919799850247735)
                ·
                  refine ⟨2072465431379699775371603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1381643620919799850247735 2072465431379699775371603)
                  ·
                    refine ⟨3108698147069549663057405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2072465431379699775371603 3108698147069549663057405)
                    ·
                      refine ⟨1165761805151081123646527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3108698147069549663057405 1165761805151081123646527)
                      ·
                        rfl

theorem cell23_2270313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 8, 1, 3, 1, 1, 3].length) (baseStart_2270313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270313 prefixEnd_2270313 := by exact prefixLift 2270313
  have htrace : WordTrace (prefixWord ++ tailWord_2270313) baseStart_2270313 baseEnd_2270313 := by
    simpa [prefixWord, tailWord_2270313, baseEnd_2270313] using wordTrace_append hprefix tailTrace_2270313
  have hstable : (prefixWord ++ tailWord_2270313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270313).length < 2 ^ (prefixWord ++ tailWord_2270313).sum := by decide
  have hdescent : baseEnd_2270313 < baseStart_2270313 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270336 : List Nat := [2, 1, 1, 2, 1, 3, 5, 1, 3, 2, 2]
def baseStart_2270336 : Nat := 118140960795 + 2270336 * 2 ^ 59
def prefixEnd_2270336 : Nat := 4983230072969 + 3 ^ 40 * 2270336 * 2
def baseEnd_2270336 : Nat := 1165773615206134533658921

theorem tailTrace_2270336 : CollatzResearch.WordTrace tailWord_2270336 prefixEnd_2270336 1165773615206134533658921 := by
  unfold tailWord_2270336
  simp only [CollatzResearch.WordTrace]
  refine ⟨41402978351483944682075431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55203971135311926242767241 41402978351483944682075431)
  ·
    refine ⟨62104467527225917023113147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41402978351483944682075431 62104467527225917023113147)
    ·
      refine ⟨93156701290838875534669721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62104467527225917023113147 93156701290838875534669721)
      ·
        refine ⟨69867525968129156651002291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93156701290838875534669721 69867525968129156651002291)
        ·
          refine ⟨104801288952193734976503437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 69867525968129156651002291 104801288952193734976503437)
          ·
            refine ⟨39300483357072650616188789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 104801288952193734976503437 39300483357072650616188789)
            ·
              refine ⟨3684420314725560995267699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39300483357072650616188789 3684420314725560995267699)
              ·
                refine ⟨5526630472088341492901549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3684420314725560995267699 5526630472088341492901549)
                ·
                  refine ⟨2072486427033128059838081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5526630472088341492901549 2072486427033128059838081)
                  ·
                    refine ⟨1554364820274846044878561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2072486427033128059838081 1554364820274846044878561)
                    ·
                      refine ⟨1165773615206134533658921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1554364820274846044878561 1165773615206134533658921)
                      ·
                        rfl

theorem cell23_2270336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 5, 1, 3, 2, 2].length) (baseStart_2270336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270336 prefixEnd_2270336 := by exact prefixLift 2270336
  have htrace : WordTrace (prefixWord ++ tailWord_2270336) baseStart_2270336 baseEnd_2270336 := by
    simpa [prefixWord, tailWord_2270336, baseEnd_2270336] using wordTrace_append hprefix tailTrace_2270336
  have hstable : (prefixWord ++ tailWord_2270336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270336).length < 2 ^ (prefixWord ++ tailWord_2270336).sum := by decide
  have hdescent : baseEnd_2270336 < baseStart_2270336 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270366 : List Nat := [4, 3, 1, 1, 2, 2, 1, 2, 1, 2, 4]
def baseStart_2270366 : Nat := 118140960795 + 2270366 * 2 ^ 59
def prefixEnd_2270366 : Nat := 4983230072969 + 3 ^ 40 * 2270366 * 2
def baseEnd_2270366 : Nat := 1165789019625769416283783

theorem tailTrace_2270366 : CollatzResearch.WordTrace tailWord_2270366 prefixEnd_2270366 1165789019625769416283783 := by
  unfold tailWord_2270366
  simp only [CollatzResearch.WordTrace]
  refine ⟨10350881361607400560967869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55204700595239469658495301 10350881361607400560967869)
  ·
    refine ⟨3881580510602775210362951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10350881361607400560967869 3881580510602775210362951)
    ·
      refine ⟨5822370765904162815544427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3881580510602775210362951 5822370765904162815544427)
      ·
        refine ⟨8733556148856244223316641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5822370765904162815544427 8733556148856244223316641)
        ·
          refine ⟨6550167111642183167487481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8733556148856244223316641 6550167111642183167487481)
          ·
            refine ⟨4912625333731637375615611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6550167111642183167487481 4912625333731637375615611)
            ·
              refine ⟨7368938000597456063423417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4912625333731637375615611 7368938000597456063423417)
              ·
                refine ⟨5526703500448092047567563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7368938000597456063423417 5526703500448092047567563)
                ·
                  refine ⟨8290055250672138071351345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5526703500448092047567563 8290055250672138071351345)
                  ·
                    refine ⟨6217541438004103553513509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8290055250672138071351345 6217541438004103553513509)
                    ·
                      refine ⟨1165789019625769416283783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 6217541438004103553513509 1165789019625769416283783)
                      ·
                        rfl

theorem cell23_2270366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_2270366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270366 prefixEnd_2270366 := by exact prefixLift 2270366
  have htrace : WordTrace (prefixWord ++ tailWord_2270366) baseStart_2270366 baseEnd_2270366 := by
    simpa [prefixWord, tailWord_2270366, baseEnd_2270366] using wordTrace_append hprefix tailTrace_2270366
  have hstable : (prefixWord ++ tailWord_2270366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270366).length < 2 ^ (prefixWord ++ tailWord_2270366).sum := by decide
  have hdescent : baseEnd_2270366 < baseStart_2270366 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270369 : List Nat := [1, 2, 3, 3, 1, 1, 3, 2, 1, 3, 3]
def baseStart_2270369 : Nat := 118140960795 + 2270369 * 2 ^ 59
def prefixEnd_2270369 : Nat := 4983230072969 + 3 ^ 40 * 2270369 * 2
def baseEnd_2270369 : Nat := 1165790560067732904546269

theorem tailTrace_2270369 : CollatzResearch.WordTrace tailWord_2270369 prefixEnd_2270369 1165790560067732904546269 := by
  unfold tailWord_2270369
  simp only [CollatzResearch.WordTrace]
  refine ⟨82807160311848336000102161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55204773541232224000068107 82807160311848336000102161)
  ·
    refine ⟨62105370233886252000076621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 82807160311848336000102161 62105370233886252000076621)
    ·
      refine ⟨23289513837707344500028733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62105370233886252000076621 23289513837707344500028733)
      ·
        refine ⟨8733567689140254187510775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23289513837707344500028733 8733567689140254187510775)
        ·
          refine ⟨13100351533710381281266163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8733567689140254187510775 13100351533710381281266163)
          ·
            refine ⟨19650527300565571921899245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13100351533710381281266163 19650527300565571921899245)
            ·
              refine ⟨7368947737712089470712217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19650527300565571921899245 7368947737712089470712217)
              ·
                refine ⟨5526710803284067103034163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7368947737712089470712217 5526710803284067103034163)
                ·
                  refine ⟨8290066204926100654551245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5526710803284067103034163 8290066204926100654551245)
                  ·
                    refine ⟨3108774826847287745456717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8290066204926100654551245 3108774826847287745456717)
                    ·
                      refine ⟨1165790560067732904546269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3108774826847287745456717 1165790560067732904546269)
                      ·
                        rfl

theorem cell23_2270369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 3, 3].length) (baseStart_2270369 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270369 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270369 prefixEnd_2270369 := by exact prefixLift 2270369
  have htrace : WordTrace (prefixWord ++ tailWord_2270369) baseStart_2270369 baseEnd_2270369 := by
    simpa [prefixWord, tailWord_2270369, baseEnd_2270369] using wordTrace_append hprefix tailTrace_2270369
  have hstable : (prefixWord ++ tailWord_2270369).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270369).length < 2 ^ (prefixWord ++ tailWord_2270369).sum := by decide
  have hdescent : baseEnd_2270369 < baseStart_2270369 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270386 : List Nat := [3, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3]
def baseStart_2270386 : Nat := 118140960795 + 2270386 * 2 ^ 59
def prefixEnd_2270386 : Nat := 4983230072969 + 3 ^ 40 * 2270386 * 2
def baseEnd_2270386 : Nat := 1165799289238859338033691

theorem tailTrace_2270386 : CollatzResearch.WordTrace tailWord_2270386 prefixEnd_2270386 1165799289238859338033691 := by
  unfold tailWord_2270386
  simp only [CollatzResearch.WordTrace]
  refine ⟨20701945088196686975867753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55205186901857831935647341 20701945088196686975867753)
  ·
    refine ⟨15526458816147515231900815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20701945088196686975867753 15526458816147515231900815)
    ·
      refine ⟨23289688224221272847851223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15526458816147515231900815 23289688224221272847851223)
      ·
        refine ⟨34934532336331909271776835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23289688224221272847851223 34934532336331909271776835)
        ·
          refine ⟨52401798504497863907665253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 34934532336331909271776835 52401798504497863907665253)
          ·
            refine ⟨9825337219593349482687235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52401798504497863907665253 9825337219593349482687235)
            ·
              refine ⟨14738005829390024224030853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9825337219593349482687235 14738005829390024224030853)
              ·
                refine ⟨2763376093010629542005785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14738005829390024224030853 2763376093010629542005785)
                ·
                  refine ⟨2072532069757972156504339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2763376093010629542005785 2072532069757972156504339)
                  ·
                    refine ⟨3108798104636958234756509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2072532069757972156504339 3108798104636958234756509)
                    ·
                      refine ⟨1165799289238859338033691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 3108798104636958234756509 1165799289238859338033691)
                      ·
                        rfl

theorem cell23_2270386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_2270386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270386 prefixEnd_2270386 := by exact prefixLift 2270386
  have htrace : WordTrace (prefixWord ++ tailWord_2270386) baseStart_2270386 baseEnd_2270386 := by
    simpa [prefixWord, tailWord_2270386, baseEnd_2270386] using wordTrace_append hprefix tailTrace_2270386
  have hstable : (prefixWord ++ tailWord_2270386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270386).length < 2 ^ (prefixWord ++ tailWord_2270386).sum := by decide
  have hdescent : baseEnd_2270386 < baseStart_2270386 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270396 : List Nat := [2, 2, 2, 3, 2, 1, 1, 2, 3, 3, 2]
def baseStart_2270396 : Nat := 118140960795 + 2270396 * 2 ^ 59
def prefixEnd_2270396 : Nat := 4983230072969 + 3 ^ 40 * 2270396 * 2
def baseEnd_2270396 : Nat := 1165804424045404298908645

theorem tailTrace_2270396 : CollatzResearch.WordTrace tailWord_2270396 prefixEnd_2270396 1165804424045404298908645 := by
  unfold tailWord_2270396
  simp only [CollatzResearch.WordTrace]
  refine ⟨41404072541375259805667521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55205430055167013074223361 41404072541375259805667521)
  ·
    refine ⟨31053054406031444854250641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41404072541375259805667521 31053054406031444854250641)
    ·
      refine ⟨23289790804523583640687981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31053054406031444854250641 23289790804523583640687981)
      ·
        refine ⟨8733671551696343865257993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23289790804523583640687981 8733671551696343865257993)
        ·
          refine ⟨6550253663772257898943495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8733671551696343865257993 6550253663772257898943495)
          ·
            refine ⟨9825380495658386848415243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6550253663772257898943495 9825380495658386848415243)
            ·
              refine ⟨14738070743487580272622865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9825380495658386848415243 14738070743487580272622865)
              ·
                refine ⟨11053553057615685204467149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14738070743487580272622865 11053553057615685204467149)
                ·
                  refine ⟨4145082396605881951675181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11053553057615685204467149 4145082396605881951675181)
                  ·
                    refine ⟨1554405898727205731878193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4145082396605881951675181 1554405898727205731878193)
                    ·
                      refine ⟨1165804424045404298908645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1554405898727205731878193 1165804424045404298908645)
                      ·
                        rfl

theorem cell23_2270396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 2, 3, 3, 2].length) (baseStart_2270396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270396 prefixEnd_2270396 := by exact prefixLift 2270396
  have htrace : WordTrace (prefixWord ++ tailWord_2270396) baseStart_2270396 baseEnd_2270396 := by
    simpa [prefixWord, tailWord_2270396, baseEnd_2270396] using wordTrace_append hprefix tailTrace_2270396
  have hstable : (prefixWord ++ tailWord_2270396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270396).length < 2 ^ (prefixWord ++ tailWord_2270396).sum := by decide
  have hdescent : baseEnd_2270396 < baseStart_2270396 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270426 : List Nat := [3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2]
def baseStart_2270426 : Nat := 118140960795 + 2270426 * 2 ^ 59
def prefixEnd_2270426 : Nat := 4983230072969 + 3 ^ 40 * 2270426 * 2
def baseEnd_2270426 : Nat := 1165819828465039181533507

theorem tailTrace_2270426 : CollatzResearch.WordTrace tailWord_2270426 prefixEnd_2270426 1165819828465039181533507 := by
  unfold tailWord_2270426
  simp only [CollatzResearch.WordTrace]
  refine ⟨20702309818160458683731783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55206159515094556489951421 20702309818160458683731783)
  ·
    refine ⟨31053464727240688025597675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20702309818160458683731783 31053464727240688025597675)
    ·
      refine ⟨46580197090861032038396513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31053464727240688025597675 46580197090861032038396513)
      ·
        refine ⟨34935147818145774028797385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46580197090861032038396513 34935147818145774028797385)
        ·
          refine ⟨26201360863609330521598039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 34935147818145774028797385 26201360863609330521598039)
          ·
            refine ⟨39302041295413995782397059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26201360863609330521598039 39302041295413995782397059)
            ·
              refine ⟨58953061943120993673595589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39302041295413995782397059 58953061943120993673595589)
              ·
                refine ⟨11053699114335186313799173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 58953061943120993673595589 11053699114335186313799173)
                ·
                  refine ⟨2072568583937847433837345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11053699114335186313799173 2072568583937847433837345)
                  ·
                    refine ⟨1554426437953385575378009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2072568583937847433837345 1554426437953385575378009)
                    ·
                      refine ⟨1165819828465039181533507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1554426437953385575378009 1165819828465039181533507)
                      ·
                        rfl

theorem cell23_2270426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 2].length) (baseStart_2270426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270426 prefixEnd_2270426 := by exact prefixLift 2270426
  have htrace : WordTrace (prefixWord ++ tailWord_2270426) baseStart_2270426 baseEnd_2270426 := by
    simpa [prefixWord, tailWord_2270426, baseEnd_2270426] using wordTrace_append hprefix tailTrace_2270426
  have hstable : (prefixWord ++ tailWord_2270426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270426).length < 2 ^ (prefixWord ++ tailWord_2270426).sum := by decide
  have hdescent : baseEnd_2270426 < baseStart_2270426 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270443 : List Nat := [1, 1, 1, 1, 2, 6, 3, 2, 2, 2, 2]
def baseStart_2270443 : Nat := 118140960795 + 2270443 * 2 ^ 59
def prefixEnd_2270443 : Nat := 4983230072969 + 3 ^ 40 * 2270443 * 2
def baseEnd_2270443 : Nat := 1165828557636165615020929

theorem tailTrace_2270443 : CollatzResearch.WordTrace tailWord_2270443 prefixEnd_2270443 1165828557636165615020929 := by
  unfold tailWord_2270443
  simp only [CollatzResearch.WordTrace]
  refine ⟨82809859313580246638295983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55206572875720164425530655 82809859313580246638295983)
  ·
    refine ⟨124214788970370369957443975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 82809859313580246638295983 124214788970370369957443975)
    ·
      refine ⟨186322183455555554936165963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124214788970370369957443975 186322183455555554936165963)
      ·
        refine ⟨279483275183333332404248945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 186322183455555554936165963 279483275183333332404248945)
        ·
          refine ⟨209612456387499999303186709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 279483275183333332404248945 209612456387499999303186709)
          ·
            refine ⟨9825583893164062467336877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 209612456387499999303186709 9825583893164062467336877)
            ·
              refine ⟨3684593959936523425251329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9825583893164062467336877 3684593959936523425251329)
              ·
                refine ⟨2763445469952392568938497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3684593959936523425251329 2763445469952392568938497)
                ·
                  refine ⟨2072584102464294426703873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2763445469952392568938497 2072584102464294426703873)
                  ·
                    refine ⟨1554438076848220820027905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2072584102464294426703873 1554438076848220820027905)
                    ·
                      refine ⟨1165828557636165615020929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1554438076848220820027905 1165828557636165615020929)
                      ·
                        rfl

theorem cell23_2270443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 3, 2, 2, 2, 2].length) (baseStart_2270443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270443 prefixEnd_2270443 := by exact prefixLift 2270443
  have htrace : WordTrace (prefixWord ++ tailWord_2270443) baseStart_2270443 baseEnd_2270443 := by
    simpa [prefixWord, tailWord_2270443, baseEnd_2270443] using wordTrace_append hprefix tailTrace_2270443
  have hstable : (prefixWord ++ tailWord_2270443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270443).length < 2 ^ (prefixWord ++ tailWord_2270443).sum := by decide
  have hdescent : baseEnd_2270443 < baseStart_2270443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2270460 : List Nat := [2, 2, 2, 1, 6, 1, 1, 1, 1, 4, 2]
def baseStart_2270460 : Nat := 118140960795 + 2270460 * 2 ^ 59
def prefixEnd_2270460 : Nat := 4983230072969 + 3 ^ 40 * 2270460 * 2
def baseEnd_2270460 : Nat := 1165837286807292048508351

theorem tailTrace_2270460 : CollatzResearch.WordTrace tailWord_2270460 prefixEnd_2270460 1165837286807292048508351 := by
  unfold tailWord_2270460
  simp only [CollatzResearch.WordTrace]
  refine ⟨41405239677259329270832417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55206986236345772361109889 41405239677259329270832417)
  ·
    refine ⟨31053929757944496953124313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41405239677259329270832417 31053929757944496953124313)
    ·
      refine ⟨23290447318458372714843235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31053929757944496953124313 23290447318458372714843235)
      ·
        refine ⟨34935670977687559072264853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23290447318458372714843235 34935670977687559072264853)
        ·
          refine ⟨1637609577079104331512415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 34935670977687559072264853 1637609577079104331512415)
          ·
            refine ⟨2456414365618656497268623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1637609577079104331512415 2456414365618656497268623)
            ·
              refine ⟨3684621548427984745902935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2456414365618656497268623 3684621548427984745902935)
              ·
                refine ⟨5526932322641977118854403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3684621548427984745902935 5526932322641977118854403)
                ·
                  refine ⟨8290398483962965678281605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5526932322641977118854403 8290398483962965678281605)
                  ·
                    refine ⟨1554449715743056064677801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 8290398483962965678281605 1554449715743056064677801)
                    ·
                      refine ⟨1165837286807292048508351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 1554449715743056064677801 1165837286807292048508351)
                      ·
                        rfl

theorem cell23_2270460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 6, 1, 1, 1, 1, 4, 2].length) (baseStart_2270460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_2270460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_2270460 prefixEnd_2270460 := by exact prefixLift 2270460
  have htrace : WordTrace (prefixWord ++ tailWord_2270460) baseStart_2270460 baseEnd_2270460 := by
    simpa [prefixWord, tailWord_2270460, baseEnd_2270460] using wordTrace_append hprefix tailTrace_2270460
  have hstable : (prefixWord ++ tailWord_2270460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2270460).length < 2 ^ (prefixWord ++ tailWord_2270460).sum := by decide
  have hdescent : baseEnd_2270460 < baseStart_2270460 := by decide
  rcases family_descends (prefixWord ++ tailWord_2270460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
