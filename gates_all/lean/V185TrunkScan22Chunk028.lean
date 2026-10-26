import V185TrunkScan22Chunk027

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_250727 : List Nat := [1, 1, 5, 1, 2, 3, 2, 2, 5]
def baseStart_250727 : Nat := 118140960795 + 250727 * 2 ^ 59
def prefixEnd_250727 : Nat := 4983230072969 + 3 ^ 40 * 250727 * 2
def baseEnd_250727 : Nat := 28609658679987947368763

theorem tailTrace_250727 : CollatzResearch.WordTrace tailWord_250727 prefixEnd_250727 28609658679987947368763 := by
  unfold tailWord_250727
  simp only [CollatzResearch.WordTrace]
  refine ⟨9144764962666374607574435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6096509975110916405049623 9144764962666374607574435)
  ·
    refine ⟨13717147443999561911361653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9144764962666374607574435 13717147443999561911361653)
    ·
      refine ⟨1285982572874958929190155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13717147443999561911361653 1285982572874958929190155)
      ·
        refine ⟨1928973859312438393785233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1285982572874958929190155 1928973859312438393785233)
        ·
          refine ⟨1446730394484328795338925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1928973859312438393785233 1446730394484328795338925)
          ·
            refine ⟨542523897931623298252097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1446730394484328795338925 542523897931623298252097)
            ·
              refine ⟨406892923448717473689073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 542523897931623298252097 406892923448717473689073)
              ·
                refine ⟨305169692586538105266805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 406892923448717473689073 305169692586538105266805)
                ·
                  refine ⟨28609658679987947368763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 305169692586538105266805 28609658679987947368763)
                  ·
                    rfl

theorem cell22_250727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 3, 2, 2, 5].length) (baseStart_250727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_250727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_250727 prefixEnd_250727 := by exact prefixLift 250727
  have htrace : WordTrace (prefixWord ++ tailWord_250727) baseStart_250727 baseEnd_250727 := by
    simpa [prefixWord, tailWord_250727, baseEnd_250727] using wordTrace_append hprefix tailTrace_250727
  have hstable : (prefixWord ++ tailWord_250727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250727).length < 2 ^ (prefixWord ++ tailWord_250727).sum := by decide
  have hdescent : baseEnd_250727 < baseStart_250727 := by decide
  rcases family_descends (prefixWord ++ tailWord_250727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250742 : List Nat := [5, 1, 1, 3, 1, 1, 1, 1, 1, 7]
def baseStart_250742 : Nat := 118140960795 + 250742 * 2 ^ 59
def prefixEnd_250742 : Nat := 4983230072969 + 3 ^ 40 * 250742 * 2
def baseEnd_250742 : Nat := 85834110846508802981243

theorem tailTrace_250742 : CollatzResearch.WordTrace tailWord_250742 prefixEnd_250742 85834110846508802981243 := by
  unfold tailWord_250742
  simp only [CollatzResearch.WordTrace]
  refine ⟨571582003600752010585655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6096874705074688112913653 571582003600752010585655)
  ·
    refine ⟨857373005401128015878483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 571582003600752010585655 857373005401128015878483)
    ·
      refine ⟨1286059508101692023817725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 857373005401128015878483 1286059508101692023817725)
      ·
        refine ⟨482272315538134508931647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1286059508101692023817725 482272315538134508931647)
        ·
          refine ⟨723408473307201763397471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 482272315538134508931647 723408473307201763397471)
          ·
            refine ⟨1085112709960802645096207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 723408473307201763397471 1085112709960802645096207)
            ·
              refine ⟨1627669064941203967644311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1085112709960802645096207 1627669064941203967644311)
              ·
                refine ⟨2441503597411805951466467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1627669064941203967644311 2441503597411805951466467)
                ·
                  refine ⟨3662255396117708927199701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2441503597411805951466467 3662255396117708927199701)
                  ·
                    refine ⟨85834110846508802981243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3662255396117708927199701 85834110846508802981243)
                    ·
                      rfl

theorem cell22_250742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 1, 1, 1, 7].length) (baseStart_250742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_250742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_250742 prefixEnd_250742 := by exact prefixLift 250742
  have htrace : WordTrace (prefixWord ++ tailWord_250742) baseStart_250742 baseEnd_250742 := by
    simpa [prefixWord, tailWord_250742, baseEnd_250742] using wordTrace_append hprefix tailTrace_250742
  have hstable : (prefixWord ++ tailWord_250742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250742).length < 2 ^ (prefixWord ++ tailWord_250742).sum := by decide
  have hdescent : baseEnd_250742 < baseStart_250742 := by decide
  rcases family_descends (prefixWord ++ tailWord_250742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250755 : List Nat := [1, 1, 1, 3, 4, 1, 3, 2, 6]
def baseStart_250755 : Nat := 118140960795 + 250755 * 2 ^ 59
def prefixEnd_250755 : Nat := 4983230072969 + 3 ^ 40 * 250755 * 2
def baseEnd_250755 : Nat := 28612853670727034135401

theorem tailTrace_250755 : CollatzResearch.WordTrace tailWord_250755 prefixEnd_250755 28612853670727034135401 := by
  unfold tailWord_250755
  simp only [CollatzResearch.WordTrace]
  refine ⟨9145786206564935389593719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6097190804376623593062479 9145786206564935389593719)
  ·
    refine ⟨13718679309847403084390579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9145786206564935389593719 13718679309847403084390579)
    ·
      refine ⟨20578018964771104626585869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13718679309847403084390579 20578018964771104626585869)
      ·
        refine ⟨7716757111789164234969701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20578018964771104626585869 7716757111789164234969701)
        ·
          refine ⟨1446891958460468294056819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7716757111789164234969701 1446891958460468294056819)
          ·
            refine ⟨2170337937690702441085229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1446891958460468294056819 2170337937690702441085229)
            ·
              refine ⟨813876726634013415406961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2170337937690702441085229 813876726634013415406961)
              ·
                refine ⟨610407544975510061555221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 813876726634013415406961 610407544975510061555221)
                ·
                  refine ⟨28612853670727034135401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 610407544975510061555221 28612853670727034135401)
                  ·
                    rfl

theorem cell22_250755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 2, 6].length) (baseStart_250755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_250755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_250755 prefixEnd_250755 := by exact prefixLift 250755
  have htrace : WordTrace (prefixWord ++ tailWord_250755) baseStart_250755 baseEnd_250755 := by
    simpa [prefixWord, tailWord_250755, baseEnd_250755] using wordTrace_append hprefix tailTrace_250755
  have hstable : (prefixWord ++ tailWord_250755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250755).length < 2 ^ (prefixWord ++ tailWord_250755).sum := by decide
  have hdescent : baseEnd_250755 < baseStart_250755 := by decide
  rcases family_descends (prefixWord ++ tailWord_250755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250941 : List Nat := [1, 4, 1, 3, 1, 3, 2, 3, 4]
def baseStart_250941 : Nat := 118140960795 + 250941 * 2 ^ 59
def prefixEnd_250941 : Nat := 4983230072969 + 3 ^ 40 * 250941 * 2
def baseEnd_250941 : Nat := 28634077537779539085211

theorem tailTrace_250941 : CollatzResearch.WordTrace tailWord_250941 prefixEnd_250941 28634077537779539085211 := by
  unfold tailWord_250941
  simp only [CollatzResearch.WordTrace]
  refine ⟨9152570183891089155864677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6101713455927392770576451 9152570183891089155864677)
  ·
    refine ⟨1716106909479579216724627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9152570183891089155864677 1716106909479579216724627)
    ·
      refine ⟨2574160364219368825086941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1716106909479579216724627 2574160364219368825086941)
      ·
        refine ⟨965310136582263309407603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2574160364219368825086941 965310136582263309407603)
        ·
          refine ⟨1447965204873394964111405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 965310136582263309407603 1447965204873394964111405)
          ·
            refine ⟨542986951827523111541777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1447965204873394964111405 542986951827523111541777)
            ·
              refine ⟨407240213870642333656333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 542986951827523111541777 407240213870642333656333)
              ·
                refine ⟨152715080201490875121125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 407240213870642333656333 152715080201490875121125)
                ·
                  refine ⟨28634077537779539085211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152715080201490875121125 28634077537779539085211)
                  ·
                    rfl

theorem cell22_250941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 3, 2, 3, 4].length) (baseStart_250941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_250941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_250941 prefixEnd_250941 := by exact prefixLift 250941
  have htrace : WordTrace (prefixWord ++ tailWord_250941) baseStart_250941 baseEnd_250941 := by
    simpa [prefixWord, tailWord_250941, baseEnd_250941] using wordTrace_append hprefix tailTrace_250941
  have hstable : (prefixWord ++ tailWord_250941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250941).length < 2 ^ (prefixWord ++ tailWord_250941).sum := by decide
  have hdescent : baseEnd_250941 < baseStart_250941 := by decide
  rcases family_descends (prefixWord ++ tailWord_250941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250973 : List Nat := [1, 4, 4, 1, 2, 2, 1, 1, 1, 5]
def baseStart_250973 : Nat := 118140960795 + 250973 * 2 ^ 59
def prefixEnd_250973 : Nat := 4983230072969 + 3 ^ 40 * 250973 * 2
def baseEnd_250973 : Nat := 85913186867301200455535

theorem tailTrace_250973 : CollatzResearch.WordTrace tailWord_250973 prefixEnd_250973 85913186867301200455535 := by
  unfold tailWord_250973
  simp only [CollatzResearch.WordTrace]
  refine ⟨9153737319775158621029573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6102491546516772414019715 9153737319775158621029573)
  ·
    refine ⟨1716325747457842241443045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9153737319775158621029573 1716325747457842241443045)
    ·
      refine ⟨321811077648345420270571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1716325747457842241443045 321811077648345420270571)
      ·
        refine ⟨482716616472518130405857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 321811077648345420270571 482716616472518130405857)
        ·
          refine ⟨362037462354388597804393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 482716616472518130405857 362037462354388597804393)
          ·
            refine ⟨271528096765791448353295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362037462354388597804393 271528096765791448353295)
            ·
              refine ⟨407292145148687172529943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271528096765791448353295 407292145148687172529943)
              ·
                refine ⟨610938217723030758794915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407292145148687172529943 610938217723030758794915)
                ·
                  refine ⟨916407326584546138192373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 610938217723030758794915 916407326584546138192373)
                  ·
                    refine ⟨85913186867301200455535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 916407326584546138192373 85913186867301200455535)
                    ·
                      rfl

theorem cell22_250973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_250973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_250973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_250973 prefixEnd_250973 := by exact prefixLift 250973
  have htrace : WordTrace (prefixWord ++ tailWord_250973) baseStart_250973 baseEnd_250973 := by
    simpa [prefixWord, tailWord_250973, baseEnd_250973] using wordTrace_append hprefix tailTrace_250973
  have hstable : (prefixWord ++ tailWord_250973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250973).length < 2 ^ (prefixWord ++ tailWord_250973).sum := by decide
  have hdescent : baseEnd_250973 < baseStart_250973 := by decide
  rcases family_descends (prefixWord ++ tailWord_250973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_250986 : List Nat := [3, 1, 3, 2, 2, 3, 2, 6]
def baseStart_250986 : Nat := 118140960795 + 250986 * 2 ^ 59
def prefixEnd_250986 : Nat := 4983230072969 + 3 ^ 40 * 250986 * 2
def baseEnd_250986 : Nat := 9546404114774833320055

theorem tailTrace_250986 : CollatzResearch.WordTrace tailWord_250986 prefixEnd_250986 9546404114774833320055 := by
  unfold tailWord_250986
  simp only [CollatzResearch.WordTrace]
  refine ⟨2288552867182015460313203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6102807645818707894168541 2288552867182015460313203)
  ·
    refine ⟨3432829300773023190469805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2288552867182015460313203 3432829300773023190469805)
    ·
      refine ⟨1287310987789883696426177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3432829300773023190469805 1287310987789883696426177)
      ·
        refine ⟨965483240842412772319633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1287310987789883696426177 965483240842412772319633)
        ·
          refine ⟨724112430631809579239725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 965483240842412772319633 724112430631809579239725)
          ·
            refine ⟨271542161486928592214897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 724112430631809579239725 271542161486928592214897)
            ·
              refine ⟨203656621115196444161173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 271542161486928592214897 203656621115196444161173)
              ·
                refine ⟨9546404114774833320055, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 203656621115196444161173 9546404114774833320055)
                ·
                  rfl

theorem cell22_250986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 2, 6].length) (baseStart_250986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_250986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_250986 prefixEnd_250986 := by exact prefixLift 250986
  have htrace : WordTrace (prefixWord ++ tailWord_250986) baseStart_250986 baseEnd_250986 := by
    simpa [prefixWord, tailWord_250986, baseEnd_250986] using wordTrace_append hprefix tailTrace_250986
  have hstable : (prefixWord ++ tailWord_250986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_250986).length < 2 ^ (prefixWord ++ tailWord_250986).sum := by decide
  have hdescent : baseEnd_250986 < baseStart_250986 := by decide
  rcases family_descends (prefixWord ++ tailWord_250986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251031 : List Nat := [1, 1, 3, 3, 3, 1, 4, 1, 5]
def baseStart_251031 : Nat := 118140960795 + 251031 * 2 ^ 59
def prefixEnd_251031 : Nat := 4983230072969 + 3 ^ 40 * 251031 * 2
def baseEnd_251031 : Nat := 28644347150869460835119

theorem tailTrace_251031 : CollatzResearch.WordTrace tailWord_251031 prefixEnd_251031 28644347150869460835119 := by
  unfold tailWord_251031
  simp only [CollatzResearch.WordTrace]
  refine ⟨9155852753565034526640947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6103901835710023017760631 9155852753565034526640947)
  ·
    refine ⟨13733779130347551789961421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9155852753565034526640947 13733779130347551789961421)
    ·
      refine ⟨5150167173880331921235533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13733779130347551789961421 5150167173880331921235533)
      ·
        refine ⟨1931312690205124470463325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5150167173880331921235533 1931312690205124470463325)
        ·
          refine ⟨724242258826921676423747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1931312690205124470463325 724242258826921676423747)
          ·
            refine ⟨1086363388240382514635621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 724242258826921676423747 1086363388240382514635621)
            ·
              refine ⟨203693135295071721494179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1086363388240382514635621 203693135295071721494179)
              ·
                refine ⟨305539702942607582241269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 203693135295071721494179 305539702942607582241269)
                ·
                  refine ⟨28644347150869460835119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 305539702942607582241269 28644347150869460835119)
                  ·
                    rfl

theorem cell22_251031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 4, 1, 5].length) (baseStart_251031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251031 prefixEnd_251031 := by exact prefixLift 251031
  have htrace : WordTrace (prefixWord ++ tailWord_251031) baseStart_251031 baseEnd_251031 := by
    simpa [prefixWord, tailWord_251031, baseEnd_251031] using wordTrace_append hprefix tailTrace_251031
  have hstable : (prefixWord ++ tailWord_251031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251031).length < 2 ^ (prefixWord ++ tailWord_251031).sum := by decide
  have hdescent : baseEnd_251031 < baseStart_251031 := by decide
  rcases family_descends (prefixWord ++ tailWord_251031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251087 : List Nat := [1, 1, 2, 1, 1, 3, 2, 11]
def baseStart_251087 : Nat := 118140960795 + 251087 * 2 ^ 59
def prefixEnd_251087 : Nat := 4983230072969 + 3 ^ 40 * 251087 * 2
def baseEnd_251087 : Nat := 9550245710782544789465

theorem tailTrace_251087 : CollatzResearch.WordTrace tailWord_251087 prefixEnd_251087 9550245710782544789465 := by
  unfold tailWord_251087
  simp only [CollatzResearch.WordTrace]
  refine ⟨9157895241362156090679515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6105263494241437393786343 9157895241362156090679515)
  ·
    refine ⟨13736842862043234136019273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9157895241362156090679515 13736842862043234136019273)
    ·
      refine ⟨10302632146532425602014455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13736842862043234136019273 10302632146532425602014455)
      ·
        refine ⟨15453948219798638403021683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10302632146532425602014455 15453948219798638403021683)
        ·
          refine ⟨23180922329697957604532525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15453948219798638403021683 23180922329697957604532525)
          ·
            refine ⟨8692845873636734101699697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 23180922329697957604532525 8692845873636734101699697)
            ·
              refine ⟨6519634405227550576274773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8692845873636734101699697 6519634405227550576274773)
              ·
                refine ⟨9550245710782544789465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 6519634405227550576274773 9550245710782544789465)
                ·
                  rfl

theorem cell22_251087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 2, 11].length) (baseStart_251087 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251087 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251087 prefixEnd_251087 := by exact prefixLift 251087
  have htrace : WordTrace (prefixWord ++ tailWord_251087) baseStart_251087 baseEnd_251087 := by
    simpa [prefixWord, tailWord_251087, baseEnd_251087] using wordTrace_append hprefix tailTrace_251087
  have hstable : (prefixWord ++ tailWord_251087).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251087).length < 2 ^ (prefixWord ++ tailWord_251087).sum := by decide
  have hdescent : baseEnd_251087 < baseStart_251087 := by decide
  rcases family_descends (prefixWord ++ tailWord_251087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251164 : List Nat := [2, 2, 3, 1, 1, 1, 2, 2, 1, 7]
def baseStart_251164 : Nat := 118140960795 + 251164 * 2 ^ 59
def prefixEnd_251164 : Nat := 4983230072969 + 3 ^ 40 * 251164 * 2
def baseEnd_251164 : Nat := 85978570070640368929949

theorem tailTrace_251164 : CollatzResearch.WordTrace tailWord_251164 prefixEnd_251164 85978570070640368929949 := by
  unfold tailWord_251164
  simp only [CollatzResearch.WordTrace]
  refine ⟨4580351831041599120616273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6107135774722132160821697 4580351831041599120616273)
  ·
    refine ⟨3435263873281199340462205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4580351831041599120616273 3435263873281199340462205)
    ·
      refine ⟨1288223952480449752673327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3435263873281199340462205 1288223952480449752673327)
      ·
        refine ⟨1932335928720674629009991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1288223952480449752673327 1932335928720674629009991)
        ·
          refine ⟨2898503893081011943514987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1932335928720674629009991 2898503893081011943514987)
          ·
            refine ⟨4347755839621517915272481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2898503893081011943514987 4347755839621517915272481)
            ·
              refine ⟨3260816879716138436454361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4347755839621517915272481 3260816879716138436454361)
              ·
                refine ⟨2445612659787103827340771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3260816879716138436454361 2445612659787103827340771)
                ·
                  refine ⟨3668418989680655741011157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2445612659787103827340771 3668418989680655741011157)
                  ·
                    refine ⟨85978570070640368929949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3668418989680655741011157 85978570070640368929949)
                    ·
                      rfl

theorem cell22_251164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_251164 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251164 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251164 prefixEnd_251164 := by exact prefixLift 251164
  have htrace : WordTrace (prefixWord ++ tailWord_251164) baseStart_251164 baseEnd_251164 := by
    simpa [prefixWord, tailWord_251164, baseEnd_251164] using wordTrace_append hprefix tailTrace_251164
  have hstable : (prefixWord ++ tailWord_251164).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251164).length < 2 ^ (prefixWord ++ tailWord_251164).sum := by decide
  have hdescent : baseEnd_251164 < baseStart_251164 := by decide
  rcases family_descends (prefixWord ++ tailWord_251164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251226 : List Nat := [3, 1, 1, 2, 1, 2, 2, 1, 6, 3]
def baseStart_251226 : Nat := 118140960795 + 251226 * 2 ^ 59
def prefixEnd_251226 : Nat := 4983230072969 + 3 ^ 40 * 251226 * 2
def baseEnd_251226 : Nat := 85999793937692873879759

theorem tailTrace_251226 : CollatzResearch.WordTrace tailWord_251226 prefixEnd_251226 85999793937692873879759 := by
  unfold tailWord_251226
  simp only [CollatzResearch.WordTrace]
  refine ⟨2290741246964645707497383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6108643325239055219993021 2290741246964645707497383)
  ·
    refine ⟨3436111870446968561246075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2290741246964645707497383 3436111870446968561246075)
    ·
      refine ⟨5154167805670452841869113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3436111870446968561246075 5154167805670452841869113)
      ·
        refine ⟨3865625854252839631401835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5154167805670452841869113 3865625854252839631401835)
        ·
          refine ⟨5798438781379259447102753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3865625854252839631401835 5798438781379259447102753)
          ·
            refine ⟨4348829086034444585327065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5798438781379259447102753 4348829086034444585327065)
            ·
              refine ⟨3261621814525833438995299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4348829086034444585327065 3261621814525833438995299)
              ·
                refine ⟨4892432721788750158492949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3261621814525833438995299 4892432721788750158492949)
                ·
                  refine ⟨229332783833847663679357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4892432721788750158492949 229332783833847663679357)
                  ·
                    refine ⟨85999793937692873879759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 229332783833847663679357 85999793937692873879759)
                    ·
                      rfl

theorem cell22_251226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 2, 1, 6, 3].length) (baseStart_251226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251226 prefixEnd_251226 := by exact prefixLift 251226
  have htrace : WordTrace (prefixWord ++ tailWord_251226) baseStart_251226 baseEnd_251226 := by
    simpa [prefixWord, tailWord_251226, baseEnd_251226] using wordTrace_append hprefix tailTrace_251226
  have hstable : (prefixWord ++ tailWord_251226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251226).length < 2 ^ (prefixWord ++ tailWord_251226).sum := by decide
  have hdescent : baseEnd_251226 < baseStart_251226 := by decide
  rcases family_descends (prefixWord ++ tailWord_251226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251239 : List Nat := [1, 1, 5, 1, 14]
def baseStart_251239 : Nat := 118140960795 + 251239 * 2 ^ 59
def prefixEnd_251239 : Nat := 4983230072969 + 3 ^ 40 * 251239 * 2
def baseEnd_251239 : Nat := 353926930466523346933

theorem tailTrace_251239 : CollatzResearch.WordTrace tailWord_251239 prefixEnd_251239 353926930466523346933 := by
  unfold tailWord_251239
  simp only [CollatzResearch.WordTrace]
  refine ⟨9163439136811486050212771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6108959424540990700141847 9163439136811486050212771)
  ·
    refine ⟨13745158705217229075319157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9163439136811486050212771 13745158705217229075319157)
    ·
      refine ⟨1288608628614115225811171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13745158705217229075319157 1288608628614115225811171)
      ·
        refine ⟨1932912942921172838716757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1288608628614115225811171 1932912942921172838716757)
        ·
          refine ⟨353926930466523346933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 1932912942921172838716757 353926930466523346933)
          ·
            rfl

theorem cell22_251239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 14].length) (baseStart_251239 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251239 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251239 prefixEnd_251239 := by exact prefixLift 251239
  have htrace : WordTrace (prefixWord ++ tailWord_251239) baseStart_251239 baseEnd_251239 := by
    simpa [prefixWord, tailWord_251239, baseEnd_251239] using wordTrace_append hprefix tailTrace_251239
  have hstable : (prefixWord ++ tailWord_251239).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251239).length < 2 ^ (prefixWord ++ tailWord_251239).sum := by decide
  have hdescent : baseEnd_251239 < baseStart_251239 := by decide
  rcases family_descends (prefixWord ++ tailWord_251239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251245 : List Nat := [1, 5, 1, 1, 1, 3, 4, 2, 4]
def baseStart_251245 : Nat := 118140960795 + 251245 * 2 ^ 59
def prefixEnd_251245 : Nat := 4983230072969 + 3 ^ 40 * 251245 * 2
def baseEnd_251245 : Nat := 28668766008661052551567

theorem tailTrace_251245 : CollatzResearch.WordTrace tailWord_251245 prefixEnd_251245 28668766008661052551567 := by
  unfold tailWord_251245
  simp only [CollatzResearch.WordTrace]
  refine ⟨9163657974789749074931189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6109105316526499383287459 9163657974789749074931189)
  ·
    refine ⟨859092935136538975774799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9163657974789749074931189 859092935136538975774799)
    ·
      refine ⟨1288639402704808463662199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 859092935136538975774799 1288639402704808463662199)
      ·
        refine ⟨1932959104057212695493299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1288639402704808463662199 1932959104057212695493299)
        ·
          refine ⟨2899438656085819043239949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1932959104057212695493299 2899438656085819043239949)
          ·
            refine ⟨1087289496032182141214981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2899438656085819043239949 1087289496032182141214981)
            ·
              refine ⟨203866780506034151477809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1087289496032182141214981 203866780506034151477809)
              ·
                refine ⟨152900085379525613608357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 203866780506034151477809 152900085379525613608357)
                ·
                  refine ⟨28668766008661052551567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 152900085379525613608357 28668766008661052551567)
                  ·
                    rfl

theorem cell22_251245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 3, 4, 2, 4].length) (baseStart_251245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251245 prefixEnd_251245 := by exact prefixLift 251245
  have htrace : WordTrace (prefixWord ++ tailWord_251245) baseStart_251245 baseEnd_251245 := by
    simpa [prefixWord, tailWord_251245, baseEnd_251245] using wordTrace_append hprefix tailTrace_251245
  have hstable : (prefixWord ++ tailWord_251245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251245).length < 2 ^ (prefixWord ++ tailWord_251245).sum := by decide
  have hdescent : baseEnd_251245 < baseStart_251245 := by decide
  rcases family_descends (prefixWord ++ tailWord_251245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251273 : List Nat := [1, 2, 1, 1, 7, 1, 3, 6]
def baseStart_251273 : Nat := 118140960795 + 251273 * 2 ^ 59
def prefixEnd_251273 : Nat := 4983230072969 + 3 ^ 40 * 251273 * 2
def baseEnd_251273 : Nat := 9557320333133379772735

theorem tailTrace_251273 : CollatzResearch.WordTrace tailWord_251273 prefixEnd_251273 9557320333133379772735 := by
  unfold tailWord_251273
  simp only [CollatzResearch.WordTrace]
  refine ⟨9164679218688309856950473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6109786145792206571300315 9164679218688309856950473)
  ·
    refine ⟨6873509414016232392712855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9164679218688309856950473 6873509414016232392712855)
    ·
      refine ⟨10310264121024348589069283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6873509414016232392712855 10310264121024348589069283)
      ·
        refine ⟨15465396181536522883603925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10310264121024348589069283 15465396181536522883603925)
        ·
          refine ⟨362470223004762255084467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 15465396181536522883603925 362470223004762255084467)
          ·
            refine ⟨543705334507143382626701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 362470223004762255084467 543705334507143382626701)
            ·
              refine ⟨203889500440178768485013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 543705334507143382626701 203889500440178768485013)
              ·
                refine ⟨9557320333133379772735, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 203889500440178768485013 9557320333133379772735)
                ·
                  rfl

theorem cell22_251273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 3, 6].length) (baseStart_251273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251273 prefixEnd_251273 := by exact prefixLift 251273
  have htrace : WordTrace (prefixWord ++ tailWord_251273) baseStart_251273 baseEnd_251273 := by
    simpa [prefixWord, tailWord_251273, baseEnd_251273] using wordTrace_append hprefix tailTrace_251273
  have hstable : (prefixWord ++ tailWord_251273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251273).length < 2 ^ (prefixWord ++ tailWord_251273).sum := by decide
  have hdescent : baseEnd_251273 < baseStart_251273 := by decide
  rcases family_descends (prefixWord ++ tailWord_251273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251294 : List Nat := [4, 3, 1, 2, 2, 2, 1, 2, 2, 3]
def baseStart_251294 : Nat := 118140960795 + 251294 * 2 ^ 59
def prefixEnd_251294 : Nat := 4983230072969 + 3 ^ 40 * 251294 * 2
def baseEnd_251294 : Nat := 86023071727363363179551

theorem tailTrace_251294 : CollatzResearch.WordTrace tailWord_251294 prefixEnd_251294 86023071727363363179551 := by
  unfold tailWord_251294
  simp only [CollatzResearch.WordTrace]
  refine ⟨1145680643951528805433117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6110296767741486962309957 1145680643951528805433117)
  ·
    refine ⟨429630241481823302037419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1145680643951528805433117 429630241481823302037419)
    ·
      refine ⟨644445362222734953056129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 429630241481823302037419 644445362222734953056129)
      ·
        refine ⟨483334021667051214792097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 644445362222734953056129 483334021667051214792097)
        ·
          refine ⟨362500516250288411094073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 483334021667051214792097 362500516250288411094073)
          ·
            refine ⟨271875387187716308320555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 362500516250288411094073 271875387187716308320555)
            ·
              refine ⟨407813080781574462480833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271875387187716308320555 407813080781574462480833)
              ·
                refine ⟨305859810586180846860625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 407813080781574462480833 305859810586180846860625)
                ·
                  refine ⟨229394857939635635145469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 305859810586180846860625 229394857939635635145469)
                  ·
                    refine ⟨86023071727363363179551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 229394857939635635145469 86023071727363363179551)
                    ·
                      rfl

theorem cell22_251294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 1, 2, 2, 3].length) (baseStart_251294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251294 prefixEnd_251294 := by exact prefixLift 251294
  have htrace : WordTrace (prefixWord ++ tailWord_251294) baseStart_251294 baseEnd_251294 := by
    simpa [prefixWord, tailWord_251294, baseEnd_251294] using wordTrace_append hprefix tailTrace_251294
  have hstable : (prefixWord ++ tailWord_251294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251294).length < 2 ^ (prefixWord ++ tailWord_251294).sum := by decide
  have hdescent : baseEnd_251294 < baseStart_251294 := by decide
  rcases family_descends (prefixWord ++ tailWord_251294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251301 : List Nat := [1, 3, 1, 2, 1, 1, 2, 6, 5]
def baseStart_251301 : Nat := 118140960795 + 251301 * 2 ^ 59
def prefixEnd_251301 : Nat := 4983230072969 + 3 ^ 40 * 251301 * 2
def baseEnd_251301 : Nat := 28675155990139226084843

theorem tailTrace_251301 : CollatzResearch.WordTrace tailWord_251301 prefixEnd_251301 28675155990139226084843 := by
  unfold tailWord_251301
  simp only [CollatzResearch.WordTrace]
  refine ⟨9165700462586870638969757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6110466975057913759313171 9165700462586870638969757)
  ·
    refine ⟨3437137673470076489613659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9165700462586870638969757 3437137673470076489613659)
    ·
      refine ⟨5155706510205114734420489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3437137673470076489613659 5155706510205114734420489)
      ·
        refine ⟨3866779882653836050815367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5155706510205114734420489 3866779882653836050815367)
        ·
          refine ⟨5800169823980754076223051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3866779882653836050815367 5800169823980754076223051)
          ·
            refine ⟨8700254735971131114334577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5800169823980754076223051 8700254735971131114334577)
            ·
              refine ⟨6525191051978348335750933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8700254735971131114334577 6525191051978348335750933)
              ·
                refine ⟨305868330561485078238325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6525191051978348335750933 305868330561485078238325)
                ·
                  refine ⟨28675155990139226084843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 305868330561485078238325 28675155990139226084843)
                  ·
                    rfl

theorem cell22_251301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 2, 6, 5].length) (baseStart_251301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251301 prefixEnd_251301 := by exact prefixLift 251301
  have htrace : WordTrace (prefixWord ++ tailWord_251301) baseStart_251301 baseEnd_251301 := by
    simpa [prefixWord, tailWord_251301, baseEnd_251301] using wordTrace_append hprefix tailTrace_251301
  have hstable : (prefixWord ++ tailWord_251301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251301).length < 2 ^ (prefixWord ++ tailWord_251301).sum := by decide
  have hdescent : baseEnd_251301 < baseStart_251301 := by decide
  rcases family_descends (prefixWord ++ tailWord_251301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251331 : List Nat := [1, 1, 1, 3, 1, 1, 4, 3, 3, 4]
def baseStart_251331 : Nat := 118140960795 + 251331 * 2 ^ 59
def prefixEnd_251331 : Nat := 4983230072969 + 3 ^ 40 * 251331 * 2
def baseEnd_251331 : Nat := 86035737583507600004437

theorem tailTrace_251331 : CollatzResearch.WordTrace tailWord_251331 prefixEnd_251331 86035737583507600004437 := by
  unfold tailWord_251331
  simp only [CollatzResearch.WordTrace]
  refine ⟨9166794652478185762561847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6111196434985457175041231 9166794652478185762561847)
  ·
    refine ⟨13750191978717278643842771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9166794652478185762561847 13750191978717278643842771)
    ·
      refine ⟨20625287968075917965764157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13750191978717278643842771 20625287968075917965764157)
      ·
        refine ⟨7734482988028469237161559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20625287968075917965764157 7734482988028469237161559)
        ·
          refine ⟨11601724482042703855742339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7734482988028469237161559 11601724482042703855742339)
          ·
            refine ⟨17402586723064055783613509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11601724482042703855742339 17402586723064055783613509)
            ·
              refine ⟨3262985010574510459427533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17402586723064055783613509 3262985010574510459427533)
              ·
                refine ⟨1223619378965441422285325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3262985010574510459427533 1223619378965441422285325)
                ·
                  refine ⟨458857267112040533356997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1223619378965441422285325 458857267112040533356997)
                  ·
                    refine ⟨86035737583507600004437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 458857267112040533356997 86035737583507600004437)
                    ·
                      rfl

theorem cell22_251331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 4, 3, 3, 4].length) (baseStart_251331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251331 prefixEnd_251331 := by exact prefixLift 251331
  have htrace : WordTrace (prefixWord ++ tailWord_251331) baseStart_251331 baseEnd_251331 := by
    simpa [prefixWord, tailWord_251331, baseEnd_251331] using wordTrace_append hprefix tailTrace_251331
  have hstable : (prefixWord ++ tailWord_251331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251331).length < 2 ^ (prefixWord ++ tailWord_251331).sum := by decide
  have hdescent : baseEnd_251331 < baseStart_251331 := by decide
  rcases family_descends (prefixWord ++ tailWord_251331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251363 : List Nat := [1, 1, 1, 6, 2, 1, 3, 1, 6]
def baseStart_251363 : Nat := 118140960795 + 251363 * 2 ^ 59
def prefixEnd_251363 : Nat := 4983230072969 + 3 ^ 40 * 251363 * 2
def baseEnd_251363 : Nat := 28682230612490061068113

theorem tailTrace_251363 : CollatzResearch.WordTrace tailWord_251363 prefixEnd_251363 28682230612490061068113 := by
  unfold tailWord_251363
  simp only [CollatzResearch.WordTrace]
  refine ⟨9167961788362255227726743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6111974525574836818484495 9167961788362255227726743)
  ·
    refine ⟨13751942682543382841590115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9167961788362255227726743 13751942682543382841590115)
    ·
      refine ⟨20627914023815074262385173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13751942682543382841590115 20627914023815074262385173)
      ·
        refine ⟨966933469866331606049305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 20627914023815074262385173 966933469866331606049305)
        ·
          refine ⟨725200102399748704536979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 966933469866331606049305 725200102399748704536979)
          ·
            refine ⟨1087800153599623056805469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 725200102399748704536979 1087800153599623056805469)
            ·
              refine ⟨407925057599858646302051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1087800153599623056805469 407925057599858646302051)
              ·
                refine ⟨611887586399787969453077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 407925057599858646302051 611887586399787969453077)
                ·
                  refine ⟨28682230612490061068113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 611887586399787969453077 28682230612490061068113)
                  ·
                    rfl

theorem cell22_251363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 1, 6].length) (baseStart_251363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251363 prefixEnd_251363 := by exact prefixLift 251363
  have htrace : WordTrace (prefixWord ++ tailWord_251363) baseStart_251363 baseEnd_251363 := by
    simpa [prefixWord, tailWord_251363, baseEnd_251363] using wordTrace_append hprefix tailTrace_251363
  have hstable : (prefixWord ++ tailWord_251363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251363).length < 2 ^ (prefixWord ++ tailWord_251363).sum := by decide
  have hdescent : baseEnd_251363 < baseStart_251363 := by decide
  rcases family_descends (prefixWord ++ tailWord_251363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251382 : List Nat := [5, 1, 1, 1, 2, 4, 1, 2, 1, 4]
def baseStart_251382 : Nat := 118140960795 + 251382 * 2 ^ 59
def prefixEnd_251382 : Nat := 4983230072969 + 3 ^ 40 * 251382 * 2
def baseEnd_251382 : Nat := 86053195925760466979281

theorem tailTrace_251382 : CollatzResearch.WordTrace tailWord_251382 prefixEnd_251382 86053195925760466979281 := by
  unfold tailWord_251382
  simp only [CollatzResearch.WordTrace]
  refine ⟨573040923455838842041775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6112436516862280981778933 573040923455838842041775)
  ·
    refine ⟨859561385183758263062663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 573040923455838842041775 859561385183758263062663)
    ·
      refine ⟨1289342077775637394593995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 859561385183758263062663 1289342077775637394593995)
      ·
        refine ⟨1934013116663456091890993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1289342077775637394593995 1934013116663456091890993)
        ·
          refine ⟨1450509837497592068918245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1934013116663456091890993 1450509837497592068918245)
          ·
            refine ⟨271970594530798512922171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1450509837497592068918245 271970594530798512922171)
            ·
              refine ⟨407955891796197769383257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 271970594530798512922171 407955891796197769383257)
              ·
                refine ⟨305966918847148327037443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 407955891796197769383257 305966918847148327037443)
                ·
                  refine ⟨458950378270722490556165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 305966918847148327037443 458950378270722490556165)
                  ·
                    refine ⟨86053195925760466979281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 458950378270722490556165 86053195925760466979281)
                    ·
                      rfl

theorem cell22_251382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 4, 1, 2, 1, 4].length) (baseStart_251382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251382 prefixEnd_251382 := by exact prefixLift 251382
  have htrace : WordTrace (prefixWord ++ tailWord_251382) baseStart_251382 baseEnd_251382 := by
    simpa [prefixWord, tailWord_251382, baseEnd_251382] using wordTrace_append hprefix tailTrace_251382
  have hstable : (prefixWord ++ tailWord_251382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251382).length < 2 ^ (prefixWord ++ tailWord_251382).sum := by decide
  have hdescent : baseEnd_251382 < baseStart_251382 := by decide
  rcases family_descends (prefixWord ++ tailWord_251382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251436 : List Nat := [2, 2, 1, 1, 1, 2, 1, 1, 11]
def baseStart_251436 : Nat := 118140960795 + 251436 * 2 ^ 59
def prefixEnd_251436 : Nat := 4983230072969 + 3 ^ 40 * 251436 * 2
def baseEnd_251436 : Nat := 28690560409774108709705

theorem tailTrace_251436 : CollatzResearch.WordTrace tailWord_251436 prefixEnd_251436 28690560409774108709705 := by
  unfold tailWord_251436
  simp only [CollatzResearch.WordTrace]
  refine ⟨4585312158548894347567081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6113749544731859130089441 4585312158548894347567081)
  ·
    refine ⟨3438984118911670760675311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4585312158548894347567081 3438984118911670760675311)
    ·
      refine ⟨5158476178367506141012967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3438984118911670760675311 5158476178367506141012967)
      ·
        refine ⟨7737714267551259211519451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5158476178367506141012967 7737714267551259211519451)
        ·
          refine ⟨11606571401326888817279177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7737714267551259211519451 11606571401326888817279177)
          ·
            refine ⟨8704928550995166612959383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11606571401326888817279177 8704928550995166612959383)
            ·
              refine ⟨13057392826492749919439075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8704928550995166612959383 13057392826492749919439075)
              ·
                refine ⟨19586089239739124879158613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13057392826492749919439075 19586089239739124879158613)
                ·
                  refine ⟨28690560409774108709705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 11 19586089239739124879158613 28690560409774108709705)
                  ·
                    rfl

theorem cell22_251436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 11].length) (baseStart_251436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251436 prefixEnd_251436 := by exact prefixLift 251436
  have htrace : WordTrace (prefixWord ++ tailWord_251436) baseStart_251436 baseEnd_251436 := by
    simpa [prefixWord, tailWord_251436, baseEnd_251436] using wordTrace_append hprefix tailTrace_251436
  have hstable : (prefixWord ++ tailWord_251436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251436).length < 2 ^ (prefixWord ++ tailWord_251436).sum := by decide
  have hdescent : baseEnd_251436 < baseStart_251436 := by decide
  rcases family_descends (prefixWord ++ tailWord_251436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251468 : List Nat := [2, 2, 1, 3, 1, 3, 1, 2, 2, 5]
def baseStart_251468 : Nat := 118140960795 + 251468 * 2 ^ 59
def prefixEnd_251468 : Nat := 4983230072969 + 3 ^ 40 * 251468 * 2
def baseEnd_251468 : Nat := 86082635483284909329017

theorem tailTrace_251468 : CollatzResearch.WordTrace tailWord_251468 prefixEnd_251468 86082635483284909329017 := by
  unfold tailWord_251468
  simp only [CollatzResearch.WordTrace]
  refine ⟨4585895726490929080149529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6114527635321238773532705 4585895726490929080149529)
  ·
    refine ⟨3439421794868196810112147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4585895726490929080149529 3439421794868196810112147)
    ·
      refine ⟨5159132692302295215168221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3439421794868196810112147 5159132692302295215168221)
      ·
        refine ⟨1934674759613360705688083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5159132692302295215168221 1934674759613360705688083)
        ·
          refine ⟨2902012139420041058532125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1934674759613360705688083 2902012139420041058532125)
          ·
            refine ⟨1088254552282515396949547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2902012139420041058532125 1088254552282515396949547)
            ·
              refine ⟨1632381828423773095424321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1088254552282515396949547 1632381828423773095424321)
              ·
                refine ⟨1224286371317829821568241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1632381828423773095424321 1224286371317829821568241)
                ·
                  refine ⟨918214778488372366176181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1224286371317829821568241 918214778488372366176181)
                  ·
                    refine ⟨86082635483284909329017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 918214778488372366176181 86082635483284909329017)
                    ·
                      rfl

theorem cell22_251468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 1, 2, 2, 5].length) (baseStart_251468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251468 prefixEnd_251468 := by exact prefixLift 251468
  have htrace : WordTrace (prefixWord ++ tailWord_251468) baseStart_251468 baseEnd_251468 := by
    simpa [prefixWord, tailWord_251468, baseEnd_251468] using wordTrace_append hprefix tailTrace_251468
  have hstable : (prefixWord ++ tailWord_251468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251468).length < 2 ^ (prefixWord ++ tailWord_251468).sum := by decide
  have hdescent : baseEnd_251468 < baseStart_251468 := by decide
  rcases family_descends (prefixWord ++ tailWord_251468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251513 : List Nat := [1, 2, 1, 3, 3, 1, 2, 1, 3, 5]
def baseStart_251513 : Nat := 118140960795 + 251513 * 2 ^ 59
def prefixEnd_251513 : Nat := 4983230072969 + 3 ^ 40 * 251513 * 2
def baseEnd_251513 : Nat := 86098039902919791953879

theorem tailTrace_251513 : CollatzResearch.WordTrace tailWord_251513 prefixEnd_251513 86098039902919791953879 := by
  unfold tailWord_251513
  simp only [CollatzResearch.WordTrace]
  refine ⟨9173432737818830845687193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6115621825212553897124795 9173432737818830845687193)
  ·
    refine ⟨6880074553364123134265395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9173432737818830845687193 6880074553364123134265395)
    ·
      refine ⟨10320111830046184701398093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6880074553364123134265395 10320111830046184701398093)
      ·
        refine ⟨3870041936267319263024285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10320111830046184701398093 3870041936267319263024285)
        ·
          refine ⟨1451265726100244723634107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3870041936267319263024285 1451265726100244723634107)
          ·
            refine ⟨2176898589150367085451161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1451265726100244723634107 2176898589150367085451161)
            ·
              refine ⟨1632673941862775314088371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2176898589150367085451161 1632673941862775314088371)
              ·
                refine ⟨2449010912794162971132557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1632673941862775314088371 2449010912794162971132557)
                ·
                  refine ⟨918379092297811114174709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2449010912794162971132557 918379092297811114174709)
                  ·
                    refine ⟨86098039902919791953879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 918379092297811114174709 86098039902919791953879)
                    ·
                      rfl

theorem cell22_251513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 2, 1, 3, 5].length) (baseStart_251513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251513 prefixEnd_251513 := by exact prefixLift 251513
  have htrace : WordTrace (prefixWord ++ tailWord_251513) baseStart_251513 baseEnd_251513 := by
    simpa [prefixWord, tailWord_251513, baseEnd_251513] using wordTrace_append hprefix tailTrace_251513
  have hstable : (prefixWord ++ tailWord_251513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251513).length < 2 ^ (prefixWord ++ tailWord_251513).sum := by decide
  have hdescent : baseEnd_251513 < baseStart_251513 := by decide
  rcases family_descends (prefixWord ++ tailWord_251513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251532 : List Nat := [2, 2, 1, 2, 1, 1, 7, 2, 4]
def baseStart_251532 : Nat := 118140960795 + 251532 * 2 ^ 59
def prefixEnd_251532 : Nat := 4983230072969 + 3 ^ 40 * 251532 * 2
def baseEnd_251532 : Nat := 28701514663736691909607

theorem tailTrace_251532 : CollatzResearch.WordTrace tailWord_251532 prefixEnd_251532 28701514663736691909607 := by
  unfold tailWord_251532
  simp only [CollatzResearch.WordTrace]
  refine ⟨4587062862374998545314425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6116083816499998060419233 4587062862374998545314425)
  ·
    refine ⟨3440297146781248908985819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4587062862374998545314425 3440297146781248908985819)
    ·
      refine ⟨5160445720171873363478729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3440297146781248908985819 5160445720171873363478729)
      ·
        refine ⟨3870334290128905022609047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5160445720171873363478729 3870334290128905022609047)
        ·
          refine ⟨5805501435193357533913571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3870334290128905022609047 5805501435193357533913571)
          ·
            refine ⟨8708252152790036300870357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5805501435193357533913571 8708252152790036300870357)
            ·
              refine ⟨204099659831016475801649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 8708252152790036300870357 204099659831016475801649)
              ·
                refine ⟨153074744873262356851237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204099659831016475801649 153074744873262356851237)
                ·
                  refine ⟨28701514663736691909607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153074744873262356851237 28701514663736691909607)
                  ·
                    rfl

theorem cell22_251532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 7, 2, 4].length) (baseStart_251532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251532 prefixEnd_251532 := by exact prefixLift 251532
  have htrace : WordTrace (prefixWord ++ tailWord_251532) baseStart_251532 baseEnd_251532 := by
    simpa [prefixWord, tailWord_251532, baseEnd_251532] using wordTrace_append hprefix tailTrace_251532
  have hstable : (prefixWord ++ tailWord_251532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251532).length < 2 ^ (prefixWord ++ tailWord_251532).sum := by decide
  have hdescent : baseEnd_251532 < baseStart_251532 := by decide
  rcases family_descends (prefixWord ++ tailWord_251532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251543 : List Nat := [1, 1, 3, 3, 2, 2, 1, 9]
def baseStart_251543 : Nat := 118140960795 + 251543 * 2 ^ 59
def prefixEnd_251543 : Nat := 4983230072969 + 3 ^ 40 * 251543 * 2
def baseEnd_251543 : Nat := 9567589946223301522643

theorem tailTrace_251543 : CollatzResearch.WordTrace tailWord_251543 prefixEnd_251543 9567589946223301522643 := by
  unfold tailWord_251543
  simp only [CollatzResearch.WordTrace]
  refine ⟨9174526927710145969279283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6116351285140097312852855 9174526927710145969279283)
  ·
    refine ⟨13761790391565218953918925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9174526927710145969279283 13761790391565218953918925)
    ·
      refine ⟨5160671396836957107719597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13761790391565218953918925 5160671396836957107719597)
      ·
        refine ⟨1935251773813858915394849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5160671396836957107719597 1935251773813858915394849)
        ·
          refine ⟨1451438830360394186546137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1935251773813858915394849 1451438830360394186546137)
          ·
            refine ⟨1088579122770295639909603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1451438830360394186546137 1088579122770295639909603)
            ·
              refine ⟨1632868684155443459864405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1088579122770295639909603 1632868684155443459864405)
              ·
                refine ⟨9567589946223301522643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1632868684155443459864405 9567589946223301522643)
                ·
                  rfl

theorem cell22_251543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 9].length) (baseStart_251543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251543 prefixEnd_251543 := by exact prefixLift 251543
  have htrace : WordTrace (prefixWord ++ tailWord_251543) baseStart_251543 baseEnd_251543 := by
    simpa [prefixWord, tailWord_251543, baseEnd_251543] using wordTrace_append hprefix tailTrace_251543
  have hstable : (prefixWord ++ tailWord_251543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251543).length < 2 ^ (prefixWord ++ tailWord_251543).sum := by decide
  have hdescent : baseEnd_251543 < baseStart_251543 := by decide
  rcases family_descends (prefixWord ++ tailWord_251543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251551 : List Nat := [1, 1, 2, 7, 2, 1, 1, 2, 1, 4]
def baseStart_251551 : Nat := 118140960795 + 251551 * 2 ^ 59
def prefixEnd_251551 : Nat := 4983230072969 + 3 ^ 40 * 251551 * 2
def baseEnd_251551 : Nat := 86111048079500359503763

theorem tailTrace_251551 : CollatzResearch.WordTrace tailWord_251551 prefixEnd_251551 86111048079500359503763 := by
  unfold tailWord_251551
  simp only [CollatzResearch.WordTrace]
  refine ⟨9174818711681163335570507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6116545807787442223713671 9174818711681163335570507)
  ·
    refine ⟨13762228067521745003355761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9174818711681163335570507 13762228067521745003355761)
    ·
      refine ⟨10321671050641308752516821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13762228067521745003355761 10321671050641308752516821)
      ·
        refine ⟨241914165249405673887113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 10321671050641308752516821 241914165249405673887113)
        ·
          refine ⟨181435623937054255415335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 241914165249405673887113 181435623937054255415335)
          ·
            refine ⟨272153435905581383123003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 181435623937054255415335 272153435905581383123003)
            ·
              refine ⟨408230153858372074684505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 272153435905581383123003 408230153858372074684505)
              ·
                refine ⟨306172615393779056013379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 408230153858372074684505 306172615393779056013379)
                ·
                  refine ⟨459258923090668584020069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306172615393779056013379 459258923090668584020069)
                  ·
                    refine ⟨86111048079500359503763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 459258923090668584020069 86111048079500359503763)
                    ·
                      rfl

theorem cell22_251551_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 7, 2, 1, 1, 2, 1, 4].length) (baseStart_251551 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251551 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251551 prefixEnd_251551 := by exact prefixLift 251551
  have htrace : WordTrace (prefixWord ++ tailWord_251551) baseStart_251551 baseEnd_251551 := by
    simpa [prefixWord, tailWord_251551, baseEnd_251551] using wordTrace_append hprefix tailTrace_251551
  have hstable : (prefixWord ++ tailWord_251551).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251551).length < 2 ^ (prefixWord ++ tailWord_251551).sum := by decide
  have hdescent : baseEnd_251551 < baseStart_251551 := by decide
  rcases family_descends (prefixWord ++ tailWord_251551) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251680 : List Nat := [2, 1, 1, 5, 1, 1, 1, 3, 1, 6]
def baseStart_251680 : Nat := 118140960795 + 251680 * 2 ^ 59
def prefixEnd_251680 : Nat := 4983230072969 + 3 ^ 40 * 251680 * 2
def baseEnd_251680 : Nat := 86155207415787023028367

theorem tailTrace_251680 : CollatzResearch.WordTrace tailWord_251680 prefixEnd_251680 86155207415787023028367 := by
  unfold tailWord_251680
  simp only [CollatzResearch.WordTrace]
  refine ⟨4589761864106909183508247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6119682485475878911344329 4589761864106909183508247)
  ·
    refine ⟨6884642796160363775262371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4589761864106909183508247 6884642796160363775262371)
    ·
      refine ⟨10326964194240545662893557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6884642796160363775262371 10326964194240545662893557)
      ·
        refine ⟨968152893210051155896271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10326964194240545662893557 968152893210051155896271)
        ·
          refine ⟨1452229339815076733844407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 968152893210051155896271 1452229339815076733844407)
          ·
            refine ⟨2178344009722615100766611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1452229339815076733844407 2178344009722615100766611)
            ·
              refine ⟨3267516014583922651149917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2178344009722615100766611 3267516014583922651149917)
              ·
                refine ⟨1225318505468970994181219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3267516014583922651149917 1225318505468970994181219)
                ·
                  refine ⟨1837977758203456491271829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1225318505468970994181219 1837977758203456491271829)
                  ·
                    refine ⟨86155207415787023028367, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1837977758203456491271829 86155207415787023028367)
                    ·
                      rfl

theorem cell22_251680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 3, 1, 6].length) (baseStart_251680 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251680 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251680 prefixEnd_251680 := by exact prefixLift 251680
  have htrace : WordTrace (prefixWord ++ tailWord_251680) baseStart_251680 baseEnd_251680 := by
    simpa [prefixWord, tailWord_251680, baseEnd_251680] using wordTrace_append hprefix tailTrace_251680
  have hstable : (prefixWord ++ tailWord_251680).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251680).length < 2 ^ (prefixWord ++ tailWord_251680).sum := by decide
  have hdescent : baseEnd_251680 < baseStart_251680 := by decide
  rcases family_descends (prefixWord ++ tailWord_251680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251682 : List Nat := [3, 3, 1, 1, 2, 1, 1, 1, 6, 3]
def baseStart_251682 : Nat := 118140960795 + 251682 * 2 ^ 59
def prefixEnd_251682 : Nat := 4983230072969 + 3 ^ 40 * 251682 * 2
def baseEnd_251682 : Nat := 86155892056659684478361

theorem tailTrace_251682 : CollatzResearch.WordTrace tailWord_251682 prefixEnd_251682 86155892056659684478361 := by
  unfold tailWord_251682
  simp only [CollatzResearch.WordTrace]
  refine ⟨2294899168551643177147325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6119731116137715139059533 2294899168551643177147325)
  ·
    refine ⟨860587188206866191430247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2294899168551643177147325 860587188206866191430247)
    ·
      refine ⟨1290880782310299287145371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 860587188206866191430247 1290880782310299287145371)
      ·
        refine ⟨1936321173465448930718057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1290880782310299287145371 1936321173465448930718057)
        ·
          refine ⟨1452240880099086698038543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1936321173465448930718057 1452240880099086698038543)
          ·
            refine ⟨2178361320148630047057815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1452240880099086698038543 2178361320148630047057815)
            ·
              refine ⟨3267541980222945070586723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2178361320148630047057815 3267541980222945070586723)
              ·
                refine ⟨4901312970334417605880085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3267541980222945070586723 4901312970334417605880085)
                ·
                  refine ⟨229749045484425825275629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4901312970334417605880085 229749045484425825275629)
                  ·
                    refine ⟨86155892056659684478361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 229749045484425825275629 86155892056659684478361)
                    ·
                      rfl

theorem cell22_251682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 1, 1, 6, 3].length) (baseStart_251682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251682 prefixEnd_251682 := by exact prefixLift 251682
  have htrace : WordTrace (prefixWord ++ tailWord_251682) baseStart_251682 baseEnd_251682 := by
    simpa [prefixWord, tailWord_251682, baseEnd_251682] using wordTrace_append hprefix tailTrace_251682
  have hstable : (prefixWord ++ tailWord_251682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251682).length < 2 ^ (prefixWord ++ tailWord_251682).sum := by decide
  have hdescent : baseEnd_251682 < baseStart_251682 := by decide
  rcases family_descends (prefixWord ++ tailWord_251682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251684 : List Nat := [2, 3, 1, 3, 2, 1, 3, 3, 4]
def baseStart_251684 : Nat := 118140960795 + 251684 * 2 ^ 59
def prefixEnd_251684 : Nat := 4983230072969 + 3 ^ 40 * 251684 * 2
def baseEnd_251684 : Nat := 28718858899177448642785

theorem tailTrace_251684 : CollatzResearch.WordTrace tailWord_251684 prefixEnd_251684 28718858899177448642785 := by
  unfold tailWord_251684
  simp only [CollatzResearch.WordTrace]
  refine ⟨4589834810099663525081053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6119779746799551366774737 4589834810099663525081053)
  ·
    refine ⟨1721188053787373821905395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4589834810099663525081053 1721188053787373821905395)
    ·
      refine ⟨2581782080681060732858093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1721188053787373821905395 2581782080681060732858093)
      ·
        refine ⟨968168280255397774821785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2581782080681060732858093 968168280255397774821785)
        ·
          refine ⟨726126210191548331116339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 968168280255397774821785 726126210191548331116339)
          ·
            refine ⟨1089189315287322496674509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 726126210191548331116339 1089189315287322496674509)
            ·
              refine ⟨408445993232745936252941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1089189315287322496674509 408445993232745936252941)
              ·
                refine ⟨153167247462279726094853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 408445993232745936252941 153167247462279726094853)
                ·
                  refine ⟨28718858899177448642785, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153167247462279726094853 28718858899177448642785)
                  ·
                    rfl

theorem cell22_251684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 3, 3, 4].length) (baseStart_251684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251684 prefixEnd_251684 := by exact prefixLift 251684
  have htrace : WordTrace (prefixWord ++ tailWord_251684) baseStart_251684 baseEnd_251684 := by
    simpa [prefixWord, tailWord_251684, baseEnd_251684] using wordTrace_append hprefix tailTrace_251684
  have hstable : (prefixWord ++ tailWord_251684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251684).length < 2 ^ (prefixWord ++ tailWord_251684).sum := by decide
  have hdescent : baseEnd_251684 < baseStart_251684 := by decide
  rcases family_descends (prefixWord ++ tailWord_251684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251697 : List Nat := [1, 2, 2, 3, 2, 3, 1, 2, 2, 4]
def baseStart_251697 : Nat := 118140960795 + 251697 * 2 ^ 59
def prefixEnd_251697 : Nat := 4983230072969 + 3 ^ 40 * 251697 * 2
def baseEnd_251697 : Nat := 86161026863204645353315

theorem tailTrace_251697 : CollatzResearch.WordTrace tailWord_251697 prefixEnd_251697 86161026863204645353315 := by
  unfold tailWord_251697
  simp only [CollatzResearch.WordTrace]
  refine ⟨9180143769152230270385345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6120095846101486846923563 9180143769152230270385345)
  ·
    refine ⟨6885107826864172702789009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9180143769152230270385345 6885107826864172702789009)
    ·
      refine ⟨5163830870148129527091757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6885107826864172702789009 5163830870148129527091757)
      ·
        refine ⟨1936436576305548572659409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5163830870148129527091757 1936436576305548572659409)
        ·
          refine ⟨1452327432229161429494557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1936436576305548572659409 1452327432229161429494557)
          ·
            refine ⟨544622787085935536060459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1452327432229161429494557 544622787085935536060459)
            ·
              refine ⟨816934180628903304090689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 544622787085935536060459 816934180628903304090689)
              ·
                refine ⟨612700635471677478068017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 816934180628903304090689 612700635471677478068017)
                ·
                  refine ⟨459525476603758108551013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 612700635471677478068017 459525476603758108551013)
                  ·
                    refine ⟨86161026863204645353315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 459525476603758108551013 86161026863204645353315)
                    ·
                      rfl

theorem cell22_251697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 2, 2, 4].length) (baseStart_251697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251697 prefixEnd_251697 := by exact prefixLift 251697
  have htrace : WordTrace (prefixWord ++ tailWord_251697) baseStart_251697 baseEnd_251697 := by
    simpa [prefixWord, tailWord_251697, baseEnd_251697] using wordTrace_append hprefix tailTrace_251697
  have hstable : (prefixWord ++ tailWord_251697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251697).length < 2 ^ (prefixWord ++ tailWord_251697).sum := by decide
  have hdescent : baseEnd_251697 < baseStart_251697 := by decide
  rcases family_descends (prefixWord ++ tailWord_251697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251701 : List Nat := [1, 3, 3, 1, 4, 1, 3, 2, 4]
def baseStart_251701 : Nat := 118140960795 + 251701 * 2 ^ 59
def prefixEnd_251701 : Nat := 4983230072969 + 3 ^ 40 * 251701 * 2
def baseEnd_251701 : Nat := 28720798714983322751101

theorem tailTrace_251701 : CollatzResearch.WordTrace tailWord_251701 prefixEnd_251701 28720798714983322751101 := by
  unfold tailWord_251701
  simp only [CollatzResearch.WordTrace]
  refine ⟨9180289661137738953530957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6120193107425159302353971 9180289661137738953530957)
  ·
    refine ⟨3442608622926652107574109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9180289661137738953530957 3442608622926652107574109)
    ·
      refine ⟨1290978233597494540340291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3442608622926652107574109 1290978233597494540340291)
      ·
        refine ⟨1936467350396241810510437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1290978233597494540340291 1936467350396241810510437)
        ·
          refine ⟨363087628199295339470707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1936467350396241810510437 363087628199295339470707)
          ·
            refine ⟨544631442298943009206061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 363087628199295339470707 544631442298943009206061)
            ·
              refine ⟨204236790862103628452273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 544631442298943009206061 204236790862103628452273)
              ·
                refine ⟨153177593146577721339205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204236790862103628452273 153177593146577721339205)
                ·
                  refine ⟨28720798714983322751101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153177593146577721339205 28720798714983322751101)
                  ·
                    rfl

theorem cell22_251701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 1, 3, 2, 4].length) (baseStart_251701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251701 prefixEnd_251701 := by exact prefixLift 251701
  have htrace : WordTrace (prefixWord ++ tailWord_251701) baseStart_251701 baseEnd_251701 := by
    simpa [prefixWord, tailWord_251701, baseEnd_251701] using wordTrace_append hprefix tailTrace_251701
  have hstable : (prefixWord ++ tailWord_251701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251701).length < 2 ^ (prefixWord ++ tailWord_251701).sum := by decide
  have hdescent : baseEnd_251701 < baseStart_251701 := by decide
  rcases family_descends (prefixWord ++ tailWord_251701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251755 : List Nat := [1, 1, 1, 1, 2, 2, 3, 4, 2, 5]
def baseStart_251755 : Nat := 118140960795 + 251755 * 2 ^ 59
def prefixEnd_251755 : Nat := 4983230072969 + 3 ^ 40 * 251755 * 2
def baseEnd_251755 : Nat := 86180881448511827403137

theorem tailTrace_251755 : CollatzResearch.WordTrace tailWord_251755 prefixEnd_251755 86180881448511827403137 := by
  unfold tailWord_251755
  simp only [CollatzResearch.WordTrace]
  refine ⟨9182259202942106175996719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6121506135294737450664479 9182259202942106175996719)
  ·
    refine ⟨13773388804413159263995079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9182259202942106175996719 13773388804413159263995079)
    ·
      refine ⟨20660083206619738895992619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13773388804413159263995079 20660083206619738895992619)
      ·
        refine ⟨30990124809929608343988929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20660083206619738895992619 30990124809929608343988929)
        ·
          refine ⟨23242593607447206257991697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 30990124809929608343988929 23242593607447206257991697)
          ·
            refine ⟨17431945205585404693493773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 23242593607447206257991697 17431945205585404693493773)
            ·
              refine ⟨6536979452094526760060165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 17431945205585404693493773 6536979452094526760060165)
              ·
                refine ⟨1225683647267723767511281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6536979452094526760060165 1225683647267723767511281)
                ·
                  refine ⟨919262735450792825633461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1225683647267723767511281 919262735450792825633461)
                  ·
                    refine ⟨86180881448511827403137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 919262735450792825633461 86180881448511827403137)
                    ·
                      rfl

theorem cell22_251755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 4, 2, 5].length) (baseStart_251755 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251755 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251755 prefixEnd_251755 := by exact prefixLift 251755
  have htrace : WordTrace (prefixWord ++ tailWord_251755) baseStart_251755 baseEnd_251755 := by
    simpa [prefixWord, tailWord_251755, baseEnd_251755] using wordTrace_append hprefix tailTrace_251755
  have hstable : (prefixWord ++ tailWord_251755).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251755).length < 2 ^ (prefixWord ++ tailWord_251755).sum := by decide
  have hdescent : baseEnd_251755 < baseStart_251755 := by decide
  rcases family_descends (prefixWord ++ tailWord_251755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251757 : List Nat := [1, 5, 1, 1, 1, 1, 3, 4, 5]
def baseStart_251757 : Nat := 118140960795 + 251757 * 2 ^ 59
def prefixEnd_251757 : Nat := 4983230072969 + 3 ^ 40 * 251757 * 2
def baseEnd_251757 : Nat := 28727188696461496284377

theorem tailTrace_251757 : CollatzResearch.WordTrace tailWord_251757 prefixEnd_251757 28727188696461496284377 := by
  unfold tailWord_251757
  simp only [CollatzResearch.WordTrace]
  refine ⟨9182332148934860517569525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6121554765956573678379683 9182332148934860517569525)
  ·
    refine ⟨860843638962643173522143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9182332148934860517569525 860843638962643173522143)
    ·
      refine ⟨1291265458443964760283215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 860843638962643173522143 1291265458443964760283215)
      ·
        refine ⟨1936898187665947140424823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1291265458443964760283215 1936898187665947140424823)
        ·
          refine ⟨2905347281498920710637235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1936898187665947140424823 2905347281498920710637235)
          ·
            refine ⟨4358020922248381065955853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2905347281498920710637235 4358020922248381065955853)
            ·
              refine ⟨1634257845843142899733445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4358020922248381065955853 1634257845843142899733445)
              ·
                refine ⟨306423346095589293700021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1634257845843142899733445 306423346095589293700021)
                ·
                  refine ⟨28727188696461496284377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 306423346095589293700021 28727188696461496284377)
                  ·
                    rfl

theorem cell22_251757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 3, 4, 5].length) (baseStart_251757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251757 prefixEnd_251757 := by exact prefixLift 251757
  have htrace : WordTrace (prefixWord ++ tailWord_251757) baseStart_251757 baseEnd_251757 := by
    simpa [prefixWord, tailWord_251757, baseEnd_251757] using wordTrace_append hprefix tailTrace_251757
  have hstable : (prefixWord ++ tailWord_251757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251757).length < 2 ^ (prefixWord ++ tailWord_251757).sum := by decide
  have hdescent : baseEnd_251757 < baseStart_251757 := by decide
  rcases family_descends (prefixWord ++ tailWord_251757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251787 : List Nat := [1, 1, 1, 1, 4, 2, 1, 6, 1, 4]
def baseStart_251787 : Nat := 118140960795 + 251787 * 2 ^ 59
def prefixEnd_251787 : Nat := 4983230072969 + 3 ^ 40 * 251787 * 2
def baseEnd_251787 : Nat := 86191835702474410603039

theorem tailTrace_251787 : CollatzResearch.WordTrace tailWord_251787 prefixEnd_251787 86191835702474410603039 := by
  unfold tailWord_251787
  simp only [CollatzResearch.WordTrace]
  refine ⟨9183426338826175641161615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6122284225884117094107743 9183426338826175641161615)
  ·
    refine ⟨13775139508239263461742423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9183426338826175641161615 13775139508239263461742423)
    ·
      refine ⟨20662709262358895192613635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13775139508239263461742423 20662709262358895192613635)
      ·
        refine ⟨30994063893538342788920453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20662709262358895192613635 30994063893538342788920453)
        ·
          refine ⟨5811386980038439272922585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 30994063893538342788920453 5811386980038439272922585)
          ·
            refine ⟨4358540235028829454691939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5811386980038439272922585 4358540235028829454691939)
            ·
              refine ⟨6537810352543244182037909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4358540235028829454691939 6537810352543244182037909)
              ·
                refine ⟨306459860275464571033027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6537810352543244182037909 306459860275464571033027)
                ·
                  refine ⟨459689790413196856549541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 306459860275464571033027 459689790413196856549541)
                  ·
                    refine ⟨86191835702474410603039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 459689790413196856549541 86191835702474410603039)
                    ·
                      rfl

theorem cell22_251787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 6, 1, 4].length) (baseStart_251787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251787 prefixEnd_251787 := by exact prefixLift 251787
  have htrace : WordTrace (prefixWord ++ tailWord_251787) baseStart_251787 baseEnd_251787 := by
    simpa [prefixWord, tailWord_251787, baseEnd_251787] using wordTrace_append hprefix tailTrace_251787
  have hstable : (prefixWord ++ tailWord_251787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251787).length < 2 ^ (prefixWord ++ tailWord_251787).sum := by decide
  have hdescent : baseEnd_251787 < baseStart_251787 := by decide
  rcases family_descends (prefixWord ++ tailWord_251787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251930 : List Nat := [3, 1, 1, 3, 1, 5, 2, 2, 1, 3]
def baseStart_251930 : Nat := 118140960795 + 251930 * 2 ^ 59
def prefixEnd_251930 : Nat := 4983230072969 + 3 ^ 40 * 251930 * 2
def baseEnd_251930 : Nat := 86240787524869704277601

theorem tailTrace_251930 : CollatzResearch.WordTrace tailWord_251930 prefixEnd_251930 86240787524869704277601 := by
  unfold tailWord_251930
  simp only [CollatzResearch.WordTrace]
  refine ⟨2297160494327027765904311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6125761318205407375744829 2297160494327027765904311)
  ·
    refine ⟨3445740741490541648856467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2297160494327027765904311 3445740741490541648856467)
    ·
      refine ⟨5168611112235812473284701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3445740741490541648856467 5168611112235812473284701)
      ·
        refine ⟨1938229167088429677481763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5168611112235812473284701 1938229167088429677481763)
        ·
          refine ⟨2907343750632644516222645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1938229167088429677481763 2907343750632644516222645)
          ·
            refine ⟨272563476621810423395873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2907343750632644516222645 272563476621810423395873)
            ·
              refine ⟨204422607466357817546905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272563476621810423395873 204422607466357817546905)
              ·
                refine ⟨153316955599768363160179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204422607466357817546905 153316955599768363160179)
                ·
                  refine ⟨229975433399652544740269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 153316955599768363160179 229975433399652544740269)
                  ·
                    refine ⟨86240787524869704277601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 229975433399652544740269 86240787524869704277601)
                    ·
                      rfl

theorem cell22_251930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 5, 2, 2, 1, 3].length) (baseStart_251930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251930 prefixEnd_251930 := by exact prefixLift 251930
  have htrace : WordTrace (prefixWord ++ tailWord_251930) baseStart_251930 baseEnd_251930 := by
    simpa [prefixWord, tailWord_251930, baseEnd_251930] using wordTrace_append hprefix tailTrace_251930
  have hstable : (prefixWord ++ tailWord_251930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251930).length < 2 ^ (prefixWord ++ tailWord_251930).sum := by decide
  have hdescent : baseEnd_251930 < baseStart_251930 := by decide
  rcases family_descends (prefixWord ++ tailWord_251930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_251954 : List Nat := [3, 2, 1, 1, 2, 4, 1, 2, 6]
def baseStart_251954 : Nat := 118140960795 + 251954 * 2 ^ 59
def prefixEnd_251954 : Nat := 4983230072969 + 3 ^ 40 * 251954 * 2
def baseEnd_251954 : Nat := 28749667738447213892509

theorem tailTrace_251954 : CollatzResearch.WordTrace tailWord_251954 prefixEnd_251954 28749667738447213892509 := by
  unfold tailWord_251954
  simp only [CollatzResearch.WordTrace]
  refine ⟨2297379332305290790622729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6126344886147442108327277 2297379332305290790622729)
  ·
    refine ⟨1723034499228968092967047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2297379332305290790622729 1723034499228968092967047)
    ·
      refine ⟨2584551748843452139450571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1723034499228968092967047 2584551748843452139450571)
      ·
        refine ⟨3876827623265178209175857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2584551748843452139450571 3876827623265178209175857)
        ·
          refine ⟨2907620717448883656881893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3876827623265178209175857 2907620717448883656881893)
          ·
            refine ⟨545178884521665685665355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2907620717448883656881893 545178884521665685665355)
            ·
              refine ⟨817768326782498528498033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545178884521665685665355 817768326782498528498033)
              ·
                refine ⟨613326245086873896373525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 817768326782498528498033 613326245086873896373525)
                ·
                  refine ⟨28749667738447213892509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 613326245086873896373525 28749667738447213892509)
                  ·
                    rfl

theorem cell22_251954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 2, 6].length) (baseStart_251954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_251954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_251954 prefixEnd_251954 := by exact prefixLift 251954
  have htrace : WordTrace (prefixWord ++ tailWord_251954) baseStart_251954 baseEnd_251954 := by
    simpa [prefixWord, tailWord_251954, baseEnd_251954] using wordTrace_append hprefix tailTrace_251954
  have hstable : (prefixWord ++ tailWord_251954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_251954).length < 2 ^ (prefixWord ++ tailWord_251954).sum := by decide
  have hdescent : baseEnd_251954 < baseStart_251954 := by decide
  rcases family_descends (prefixWord ++ tailWord_251954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252014 : List Nat := [4, 1, 2, 2, 1, 1, 1, 1, 2, 7]
def baseStart_252014 : Nat := 118140960795 + 252014 * 2 ^ 59
def prefixEnd_252014 : Nat := 4983230072969 + 3 ^ 40 * 252014 * 2
def baseEnd_252014 : Nat := 86269542441521485177343

theorem tailTrace_252014 : CollatzResearch.WordTrace tailWord_252014 prefixEnd_252014 86269542441521485177343 := by
  unfold tailWord_252014
  simp only [CollatzResearch.WordTrace]
  refine ⟨1148963213625474176209387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6127803806002528939783397 1148963213625474176209387)
  ·
    refine ⟨1723444820438211264314081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1148963213625474176209387 1723444820438211264314081)
    ·
      refine ⟨1292583615328658448235561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1723444820438211264314081 1292583615328658448235561)
      ·
        refine ⟨969437711496493836176671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1292583615328658448235561 969437711496493836176671)
        ·
          refine ⟨1454156567244740754265007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 969437711496493836176671 1454156567244740754265007)
          ·
            refine ⟨2181234850867111131397511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1454156567244740754265007 2181234850867111131397511)
            ·
              refine ⟨3271852276300666697096267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2181234850867111131397511 3271852276300666697096267)
              ·
                refine ⟨4907778414451000045644401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3271852276300666697096267 4907778414451000045644401)
                ·
                  refine ⟨3680833810838250034233301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4907778414451000045644401 3680833810838250034233301)
                  ·
                    refine ⟨86269542441521485177343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3680833810838250034233301 86269542441521485177343)
                    ·
                      rfl

theorem cell22_252014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 1, 1, 2, 7].length) (baseStart_252014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_252014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_252014 prefixEnd_252014 := by exact prefixLift 252014
  have htrace : WordTrace (prefixWord ++ tailWord_252014) baseStart_252014 baseEnd_252014 := by
    simpa [prefixWord, tailWord_252014, baseEnd_252014] using wordTrace_append hprefix tailTrace_252014
  have hstable : (prefixWord ++ tailWord_252014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252014).length < 2 ^ (prefixWord ++ tailWord_252014).sum := by decide
  have hdescent : baseEnd_252014 < baseStart_252014 := by decide
  rcases family_descends (prefixWord ++ tailWord_252014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252016 : List Nat := [2, 1, 1, 1, 5, 4, 2, 6]
def baseStart_252016 : Nat := 118140960795 + 252016 * 2 ^ 59
def prefixEnd_252016 : Nat := 4983230072969 + 3 ^ 40 * 252016 * 2
def baseEnd_252016 : Nat := 9585580786932682958593

theorem tailTrace_252016 : CollatzResearch.WordTrace tailWord_252016 prefixEnd_252016 9585580786932682958593 := by
  unfold tailWord_252016
  simp only [CollatzResearch.WordTrace]
  refine ⟨4595889327498273875623951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6127852436664365167498601 4595889327498273875623951)
  ·
    refine ⟨6893833991247410813435927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4595889327498273875623951 6893833991247410813435927)
    ·
      refine ⟨10340750986871116220153891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6893833991247410813435927 10340750986871116220153891)
      ·
        refine ⟨15511126480306674330230837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10340750986871116220153891 15511126480306674330230837)
        ·
          refine ⟨1454168107528750718459141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15511126480306674330230837 1454168107528750718459141)
          ·
            refine ⟨272656520161640759711089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1454168107528750718459141 272656520161640759711089)
            ·
              refine ⟨204492390121230569783317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 272656520161640759711089 204492390121230569783317)
              ·
                refine ⟨9585580786932682958593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 204492390121230569783317 9585580786932682958593)
                ·
                  rfl

theorem cell22_252016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 4, 2, 6].length) (baseStart_252016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_252016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_252016 prefixEnd_252016 := by exact prefixLift 252016
  have htrace : WordTrace (prefixWord ++ tailWord_252016) baseStart_252016 baseEnd_252016 := by
    simpa [prefixWord, tailWord_252016, baseEnd_252016] using wordTrace_append hprefix tailTrace_252016
  have hstable : (prefixWord ++ tailWord_252016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252016).length < 2 ^ (prefixWord ++ tailWord_252016).sum := by decide
  have hdescent : baseEnd_252016 < baseStart_252016 := by decide
  rcases family_descends (prefixWord ++ tailWord_252016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252061 : List Nat := [1, 4, 2, 1, 1, 4, 1, 3, 5]
def baseStart_252061 : Nat := 118140960795 + 252061 * 2 ^ 59
def prefixEnd_252061 : Nat := 4983230072969 + 3 ^ 40 * 252061 * 2
def baseEnd_252061 : Nat := 28761877167343009750733

theorem tailTrace_252061 : CollatzResearch.WordTrace tailWord_252061 prefixEnd_252061 28761877167343009750733 := by
  unfold tailWord_252061
  simp only [CollatzResearch.WordTrace]
  refine ⟨9193419939833520436636037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6128946626555680291090691 9193419939833520436636037)
  ·
    refine ⟨1723766238718785081869257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9193419939833520436636037 1723766238718785081869257)
    ·
      refine ⟨1292824679039088811401943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1723766238718785081869257 1292824679039088811401943)
      ·
        refine ⟨1939237018558633217102915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1292824679039088811401943 1939237018558633217102915)
        ·
          refine ⟨2908855527837949825654373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1939237018558633217102915 2908855527837949825654373)
          ·
            refine ⟨545410411469615592310195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2908855527837949825654373 545410411469615592310195)
            ·
              refine ⟨818115617204423388465293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545410411469615592310195 818115617204423388465293)
              ·
                refine ⟨306793356451658770674485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 818115617204423388465293 306793356451658770674485)
                ·
                  refine ⟨28761877167343009750733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 306793356451658770674485 28761877167343009750733)
                  ·
                    rfl

theorem cell22_252061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 4, 1, 3, 5].length) (baseStart_252061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_252061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_252061 prefixEnd_252061 := by exact prefixLift 252061
  have htrace : WordTrace (prefixWord ++ tailWord_252061) baseStart_252061 baseEnd_252061 := by
    simpa [prefixWord, tailWord_252061, baseEnd_252061] using wordTrace_append hprefix tailTrace_252061
  have hstable : (prefixWord ++ tailWord_252061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252061).length < 2 ^ (prefixWord ++ tailWord_252061).sum := by decide
  have hdescent : baseEnd_252061 < baseStart_252061 := by decide
  rcases family_descends (prefixWord ++ tailWord_252061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252104 : List Nat := [2, 1, 3, 1, 2, 1, 1, 1, 5, 5]
def baseStart_252104 : Nat := 118140960795 + 252104 * 2 ^ 59
def prefixEnd_252104 : Nat := 4983230072969 + 3 ^ 40 * 252104 * 2
def baseEnd_252104 : Nat := 86300351280791250427067

theorem tailTrace_252104 : CollatzResearch.WordTrace tailWord_252104 prefixEnd_252104 86300351280791250427067 := by
  unfold tailWord_252104
  simp only [CollatzResearch.WordTrace]
  refine ⟨4597494139338869390225683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6129992185785159186967577 4597494139338869390225683)
  ·
    refine ⟨6896241209008304085338525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4597494139338869390225683 6896241209008304085338525)
    ·
      refine ⟨2586090453378114032001947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6896241209008304085338525 2586090453378114032001947)
      ·
        refine ⟨3879135680067171048002921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2586090453378114032001947 3879135680067171048002921)
        ·
          refine ⟨2909351760050378286002191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3879135680067171048002921 2909351760050378286002191)
          ·
            refine ⟨4364027640075567429003287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2909351760050378286002191 4364027640075567429003287)
            ·
              refine ⟨6546041460113351143504931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4364027640075567429003287 6546041460113351143504931)
              ·
                refine ⟨9819062190170026715257397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6546041460113351143504931 9819062190170026715257397)
                ·
                  refine ⟨920537080328440004555381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 9819062190170026715257397 920537080328440004555381)
                  ·
                    refine ⟨86300351280791250427067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 920537080328440004555381 86300351280791250427067)
                    ·
                      rfl

theorem cell22_252104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 1, 1, 5, 5].length) (baseStart_252104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_252104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_252104 prefixEnd_252104 := by exact prefixLift 252104
  have htrace : WordTrace (prefixWord ++ tailWord_252104) baseStart_252104 baseEnd_252104 := by
    simpa [prefixWord, tailWord_252104, baseEnd_252104] using wordTrace_append hprefix tailTrace_252104
  have hstable : (prefixWord ++ tailWord_252104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252104).length < 2 ^ (prefixWord ++ tailWord_252104).sum := by decide
  have hdescent : baseEnd_252104 < baseStart_252104 := by decide
  rcases family_descends (prefixWord ++ tailWord_252104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252119 : List Nat := [1, 1, 3, 2, 1, 2, 1, 4, 1, 6]
def baseStart_252119 : Nat := 118140960795 + 252119 * 2 ^ 59
def prefixEnd_252119 : Nat := 4983230072969 + 3 ^ 40 * 252119 * 2
def baseEnd_252119 : Nat := 86305486087336211302021

theorem tailTrace_252119 : CollatzResearch.WordTrace tailWord_252119 prefixEnd_252119 86305486087336211302021 := by
  unfold tailWord_252119
  simp only [CollatzResearch.WordTrace]
  refine ⟨9195535373623396342247411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6130356915748930894831607 9195535373623396342247411)
  ·
    refine ⟨13793303060435094513371117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9195535373623396342247411 13793303060435094513371117)
    ·
      refine ⟨5172488647663160442514169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13793303060435094513371117 5172488647663160442514169)
      ·
        refine ⟨3879366485747370331885627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5172488647663160442514169 3879366485747370331885627)
        ·
          refine ⟨5819049728621055497828441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3879366485747370331885627 5819049728621055497828441)
          ·
            refine ⟨4364287296465791623371331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5819049728621055497828441 4364287296465791623371331)
            ·
              refine ⟨6546430944698687435056997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4364287296465791623371331 6546430944698687435056997)
              ·
                refine ⟨1227455802131003894073187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 6546430944698687435056997 1227455802131003894073187)
                ·
                  refine ⟨1841183703196505841109781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1227455802131003894073187 1841183703196505841109781)
                  ·
                    refine ⟨86305486087336211302021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1841183703196505841109781 86305486087336211302021)
                    ·
                      rfl

theorem cell22_252119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_252119 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_252119 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_252119 prefixEnd_252119 := by exact prefixLift 252119
  have htrace : WordTrace (prefixWord ++ tailWord_252119) baseStart_252119 baseEnd_252119 := by
    simpa [prefixWord, tailWord_252119, baseEnd_252119] using wordTrace_append hprefix tailTrace_252119
  have hstable : (prefixWord ++ tailWord_252119).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252119).length < 2 ^ (prefixWord ++ tailWord_252119).sum := by decide
  have hdescent : baseEnd_252119 < baseStart_252119 := by decide
  rcases family_descends (prefixWord ++ tailWord_252119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252136 : List Nat := [2, 1, 4, 1, 2, 3, 1, 1, 1, 6]
def baseStart_252136 : Nat := 118140960795 + 252136 * 2 ^ 59
def prefixEnd_252136 : Nat := 4983230072969 + 3 ^ 40 * 252136 * 2
def baseEnd_252136 : Nat := 86311305534753833626969

theorem tailTrace_252136 : CollatzResearch.WordTrace tailWord_252136 prefixEnd_252136 86311305534753833626969 := by
  unfold tailWord_252136
  simp only [CollatzResearch.WordTrace]
  refine ⟨4598077707280904122808131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6130770276374538830410841 4598077707280904122808131)
  ·
    refine ⟨6897116560921356184212197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4598077707280904122808131 6897116560921356184212197)
    ·
      refine ⟨1293209355172754284539787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6897116560921356184212197 1293209355172754284539787)
      ·
        refine ⟨1939814032759131426809681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1293209355172754284539787 1939814032759131426809681)
        ·
          refine ⟨1454860524569348570107261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1939814032759131426809681 1454860524569348570107261)
          ·
            refine ⟨545572696713505713790223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1454860524569348570107261 545572696713505713790223)
            ·
              refine ⟨818359045070258570685335, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 545572696713505713790223 818359045070258570685335)
              ·
                refine ⟨1227538567605387856028003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 818359045070258570685335 1227538567605387856028003)
                ·
                  refine ⟨1841307851408081784042005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1227538567605387856028003 1841307851408081784042005)
                  ·
                    refine ⟨86311305534753833626969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1841307851408081784042005 86311305534753833626969)
                    ·
                      rfl

theorem cell22_252136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 1, 1, 1, 6].length) (baseStart_252136 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_252136 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_252136 prefixEnd_252136 := by exact prefixLift 252136
  have htrace : WordTrace (prefixWord ++ tailWord_252136) baseStart_252136 baseEnd_252136 := by
    simpa [prefixWord, tailWord_252136, baseEnd_252136] using wordTrace_append hprefix tailTrace_252136
  have hstable : (prefixWord ++ tailWord_252136).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252136).length < 2 ^ (prefixWord ++ tailWord_252136).sum := by decide
  have hdescent : baseEnd_252136 < baseStart_252136 := by decide
  rcases family_descends (prefixWord ++ tailWord_252136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252183 : List Nat := [1, 1, 3, 4, 1, 2, 2, 2, 3, 3]
def baseStart_252183 : Nat := 118140960795 + 252183 * 2 ^ 59
def prefixEnd_252183 : Nat := 4983230072969 + 3 ^ 40 * 252183 * 2
def baseEnd_252183 : Nat := 86327394595261377701825

theorem tailTrace_252183 : CollatzResearch.WordTrace tailWord_252183 prefixEnd_252183 86327394595261377701825 := by
  unfold tailWord_252183
  simp only [CollatzResearch.WordTrace]
  refine ⟨9197869645391535272577203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6131913096927690181718135 9197869645391535272577203)
  ·
    refine ⟨13796804468087302908865805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9197869645391535272577203 13796804468087302908865805)
    ·
      refine ⟨5173801675532738590824677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13796804468087302908865805 5173801675532738590824677)
      ·
        refine ⟨970087814162388485779627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5173801675532738590824677 970087814162388485779627)
        ·
          refine ⟨1455131721243582728669441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 970087814162388485779627 1455131721243582728669441)
          ·
            refine ⟨1091348790932687046502081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1455131721243582728669441 1091348790932687046502081)
            ·
              refine ⟨818511593199515284876561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1091348790932687046502081 818511593199515284876561)
              ·
                refine ⟨613883694899636463657421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 818511593199515284876561 613883694899636463657421)
                ·
                  refine ⟨230206385587363673871533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 613883694899636463657421 230206385587363673871533)
                  ·
                    refine ⟨86327394595261377701825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 230206385587363673871533 86327394595261377701825)
                    ·
                      rfl

theorem cell22_252183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 2, 2, 3, 3].length) (baseStart_252183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_252183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_252183 prefixEnd_252183 := by exact prefixLift 252183
  have htrace : WordTrace (prefixWord ++ tailWord_252183) baseStart_252183 baseEnd_252183 := by
    simpa [prefixWord, tailWord_252183, baseEnd_252183] using wordTrace_append hprefix tailTrace_252183
  have hstable : (prefixWord ++ tailWord_252183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252183).length < 2 ^ (prefixWord ++ tailWord_252183).sum := by decide
  have hdescent : baseEnd_252183 < baseStart_252183 := by decide
  rcases family_descends (prefixWord ++ tailWord_252183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252196 : List Nat := [2, 3, 1, 3, 1, 2, 1, 2, 7]
def baseStart_252196 : Nat := 118140960795 + 252196 * 2 ^ 59
def prefixEnd_252196 : Nat := 4983230072969 + 3 ^ 40 * 252196 * 2
def baseEnd_252196 : Nat := 28777281586977892375595

theorem tailTrace_252196 : CollatzResearch.WordTrace tailWord_252196 prefixEnd_252196 28777281586977892375595 := by
  unfold tailWord_252196
  simp only [CollatzResearch.WordTrace]
  refine ⟨4599171897172219246400221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6132229196229625661866961 4599171897172219246400221)
  ·
    refine ⟨1724689461439582217400083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4599171897172219246400221 1724689461439582217400083)
    ·
      refine ⟨2587034192159373326100125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1724689461439582217400083 2587034192159373326100125)
      ·
        refine ⟨970137822059764997287547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2587034192159373326100125 970137822059764997287547)
        ·
          refine ⟨1455206733089647495931321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 970137822059764997287547 1455206733089647495931321)
          ·
            refine ⟨1091405049817235621948491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1455206733089647495931321 1091405049817235621948491)
            ·
              refine ⟨1637107574725853432922737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1091405049817235621948491 1637107574725853432922737)
              ·
                refine ⟨1227830681044390074692053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1637107574725853432922737 1227830681044390074692053)
                ·
                  refine ⟨28777281586977892375595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1227830681044390074692053 28777281586977892375595)
                  ·
                    rfl

theorem cell22_252196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 2, 7].length) (baseStart_252196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_252196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_252196 prefixEnd_252196 := by exact prefixLift 252196
  have htrace : WordTrace (prefixWord ++ tailWord_252196) baseStart_252196 baseEnd_252196 := by
    simpa [prefixWord, tailWord_252196, baseEnd_252196] using wordTrace_append hprefix tailTrace_252196
  have hstable : (prefixWord ++ tailWord_252196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252196).length < 2 ^ (prefixWord ++ tailWord_252196).sum := by decide
  have hdescent : baseEnd_252196 < baseStart_252196 := by decide
  rcases family_descends (prefixWord ++ tailWord_252196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252260 : List Nat := [2, 3, 1, 1, 3, 1, 5, 1, 1, 4]
def baseStart_252260 : Nat := 118140960795 + 252260 * 2 ^ 59
def prefixEnd_252260 : Nat := 4983230072969 + 3 ^ 40 * 252260 * 2
def baseEnd_252260 : Nat := 86353753268858843526589

theorem tailTrace_252260 : CollatzResearch.WordTrace tailWord_252260 prefixEnd_252260 86353753268858843526589 := by
  unfold tailWord_252260
  simp only [CollatzResearch.WordTrace]
  refine ⟨4600339033056288711565117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6133785377408384948753489 4600339033056288711565117)
  ·
    refine ⟨1725127137396108266836919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4600339033056288711565117 1725127137396108266836919)
    ·
      refine ⟨2587690706094162400255379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1725127137396108266836919 2587690706094162400255379)
      ·
        refine ⟨3881536059141243600383069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2587690706094162400255379 3881536059141243600383069)
        ·
          refine ⟨1455576022177966350143651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3881536059141243600383069 1455576022177966350143651)
          ·
            refine ⟨2183364033266949525215477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1455576022177966350143651 2183364033266949525215477)
            ·
              refine ⟨204690378118776517988951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2183364033266949525215477 204690378118776517988951)
              ·
                refine ⟨307035567178164776983427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204690378118776517988951 307035567178164776983427)
                ·
                  refine ⟨460553350767247165475141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307035567178164776983427 460553350767247165475141)
                  ·
                    refine ⟨86353753268858843526589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 460553350767247165475141 86353753268858843526589)
                    ·
                      rfl

theorem cell22_252260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 5, 1, 1, 4].length) (baseStart_252260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_252260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_252260 prefixEnd_252260 := by exact prefixLift 252260
  have htrace : WordTrace (prefixWord ++ tailWord_252260) baseStart_252260 baseEnd_252260 := by
    simpa [prefixWord, tailWord_252260, baseEnd_252260] using wordTrace_append hprefix tailTrace_252260
  have hstable : (prefixWord ++ tailWord_252260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252260).length < 2 ^ (prefixWord ++ tailWord_252260).sum := by decide
  have hdescent : baseEnd_252260 < baseStart_252260 := by decide
  rcases family_descends (prefixWord ++ tailWord_252260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252271 : List Nat := [1, 1, 2, 1, 3, 1, 2, 3, 4, 4]
def baseStart_252271 : Nat := 118140960795 + 252271 * 2 ^ 59
def prefixEnd_252271 : Nat := 4983230072969 + 3 ^ 40 * 252271 * 2
def baseEnd_252271 : Nat := 86357518793658481501555

theorem tailTrace_252271 : CollatzResearch.WordTrace tailWord_252271 prefixEnd_252271 86357518793658481501555 := by
  unfold tailWord_252271
  simp only [CollatzResearch.WordTrace]
  refine ⟨9201079269072726301780667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6134052846048484201187111 9201079269072726301780667)
  ·
    refine ⟨13801618903609089452671001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9201079269072726301780667 13801618903609089452671001)
    ·
      refine ⟨10351214177706817089503251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13801618903609089452671001 10351214177706817089503251)
      ·
        refine ⟨15526821266560225634254877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10351214177706817089503251 15526821266560225634254877)
        ·
          refine ⟨5822557974960084612845579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15526821266560225634254877 5822557974960084612845579)
          ·
            refine ⟨8733836962440126919268369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5822557974960084612845579 8733836962440126919268369)
            ·
              refine ⟨6550377721830095189451277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8733836962440126919268369 6550377721830095189451277)
              ·
                refine ⟨2456391645686285696044229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6550377721830095189451277 2456391645686285696044229)
                ·
                  refine ⟨460573433566178568008293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2456391645686285696044229 460573433566178568008293)
                  ·
                    refine ⟨86357518793658481501555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 460573433566178568008293 86357518793658481501555)
                    ·
                      rfl

theorem cell22_252271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 2, 3, 4, 4].length) (baseStart_252271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_252271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_252271 prefixEnd_252271 := by exact prefixLift 252271
  have htrace : WordTrace (prefixWord ++ tailWord_252271) baseStart_252271 baseEnd_252271 := by
    simpa [prefixWord, tailWord_252271, baseEnd_252271] using wordTrace_append hprefix tailTrace_252271
  have hstable : (prefixWord ++ tailWord_252271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252271).length < 2 ^ (prefixWord ++ tailWord_252271).sum := by decide
  have hdescent : baseEnd_252271 < baseStart_252271 := by decide
  rcases family_descends (prefixWord ++ tailWord_252271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252386 : List Nat := [3, 3, 3, 2, 1, 2, 1, 1, 3, 3]
def baseStart_252386 : Nat := 118140960795 + 252386 * 2 ^ 59
def prefixEnd_252386 : Nat := 4983230072969 + 3 ^ 40 * 252386 * 2
def baseEnd_252386 : Nat := 86396885643836514876203

theorem tailTrace_252386 : CollatzResearch.WordTrace tailWord_252386 prefixEnd_252386 86396885643836514876203 := by
  unfold tailWord_252386
  simp only [CollatzResearch.WordTrace]
  refine ⟨2301318415914025235554253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6136849109104067294811341 2301318415914025235554253)
  ·
    refine ⟨862994405967759463332845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2301318415914025235554253 862994405967759463332845)
    ·
      refine ⟨323622902237909798749817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 862994405967759463332845 323622902237909798749817)
      ·
        refine ⟨242717176678432349062363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323622902237909798749817 242717176678432349062363)
        ·
          refine ⟨364075765017648523593545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242717176678432349062363 364075765017648523593545)
          ·
            refine ⟨273056823763236392695159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 364075765017648523593545 273056823763236392695159)
            ·
              refine ⟨409585235644854589042739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 273056823763236392695159 409585235644854589042739)
              ·
                refine ⟨614377853467281883564109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 409585235644854589042739 614377853467281883564109)
                ·
                  refine ⟨230391695050230706336541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 614377853467281883564109 230391695050230706336541)
                  ·
                    refine ⟨86396885643836514876203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 230391695050230706336541 86396885643836514876203)
                    ·
                      rfl

theorem cell22_252386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 1, 3, 3].length) (baseStart_252386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_252386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_252386 prefixEnd_252386 := by exact prefixLift 252386
  have htrace : WordTrace (prefixWord ++ tailWord_252386) baseStart_252386 baseEnd_252386 := by
    simpa [prefixWord, tailWord_252386, baseEnd_252386] using wordTrace_append hprefix tailTrace_252386
  have hstable : (prefixWord ++ tailWord_252386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252386).length < 2 ^ (prefixWord ++ tailWord_252386).sum := by decide
  have hdescent : baseEnd_252386 < baseStart_252386 := by decide
  rcases family_descends (prefixWord ++ tailWord_252386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252408 : List Nat := [2, 1, 2, 1, 1, 4, 2, 3, 1, 5]
def baseStart_252408 : Nat := 118140960795 + 252408 * 2 ^ 59
def prefixEnd_252408 : Nat := 4983230072969 + 3 ^ 40 * 252408 * 2
def baseEnd_252408 : Nat := 86404416693435790826135

theorem tailTrace_252408 : CollatzResearch.WordTrace tailWord_252408 prefixEnd_252408 86404416693435790826135 := by
  unfold tailWord_252408
  simp only [CollatzResearch.WordTrace]
  refine ⟨4603038034788199349758939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6137384046384265799678585 4603038034788199349758939)
  ·
    refine ⟨6904557052182299024638409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4603038034788199349758939 6904557052182299024638409)
    ·
      refine ⟨5178417789136724268478807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6904557052182299024638409 5178417789136724268478807)
      ·
        refine ⟨7767626683705086402718211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5178417789136724268478807 7767626683705086402718211)
        ·
          refine ⟨11651440025557629604077317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7767626683705086402718211 11651440025557629604077317)
          ·
            refine ⟨2184645004792055550764497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 11651440025557629604077317 2184645004792055550764497)
            ·
              refine ⟨1638483753594041663073373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2184645004792055550764497 1638483753594041663073373)
              ·
                refine ⟨614431407597765623652515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1638483753594041663073373 614431407597765623652515)
                ·
                  refine ⟨921647111396648435478773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 614431407597765623652515 921647111396648435478773)
                  ·
                    refine ⟨86404416693435790826135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 921647111396648435478773 86404416693435790826135)
                    ·
                      rfl

theorem cell22_252408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 3, 1, 5].length) (baseStart_252408 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_252408 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_252408 prefixEnd_252408 := by exact prefixLift 252408
  have htrace : WordTrace (prefixWord ++ tailWord_252408) baseStart_252408 baseEnd_252408 := by
    simpa [prefixWord, tailWord_252408, baseEnd_252408] using wordTrace_append hprefix tailTrace_252408
  have hstable : (prefixWord ++ tailWord_252408).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252408).length < 2 ^ (prefixWord ++ tailWord_252408).sum := by decide
  have hdescent : baseEnd_252408 < baseStart_252408 := by decide
  rcases family_descends (prefixWord ++ tailWord_252408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252440 : List Nat := [2, 1, 2, 3, 3, 1, 2, 2, 2, 4]
def baseStart_252440 : Nat := 118140960795 + 252440 * 2 ^ 59
def prefixEnd_252440 : Nat := 4983230072969 + 3 ^ 40 * 252440 * 2
def baseEnd_252440 : Nat := 86415370947398374026037

theorem tailTrace_252440 : CollatzResearch.WordTrace tailWord_252440 prefixEnd_252440 86415370947398374026037 := by
  unfold tailWord_252440
  simp only [CollatzResearch.WordTrace]
  refine ⟨4603621602730234082341387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6138162136973645443121849 4603621602730234082341387)
  ·
    refine ⟨6905432404095351123512081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4603621602730234082341387 6905432404095351123512081)
    ·
      refine ⟨5179074303071513342634061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6905432404095351123512081 5179074303071513342634061)
      ·
        refine ⟨1942152863651817503487773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5179074303071513342634061 1942152863651817503487773)
        ·
          refine ⟨728307323869431563807915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1942152863651817503487773 728307323869431563807915)
          ·
            refine ⟨1092460985804147345711873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728307323869431563807915 1092460985804147345711873)
            ·
              refine ⟨819345739353110509283905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1092460985804147345711873 819345739353110509283905)
              ·
                refine ⟨614509304514832881962929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 819345739353110509283905 614509304514832881962929)
                ·
                  refine ⟨460881978386124661472197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 614509304514832881962929 460881978386124661472197)
                  ·
                    refine ⟨86415370947398374026037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 460881978386124661472197 86415370947398374026037)
                    ·
                      rfl

theorem cell22_252440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 2, 2, 4].length) (baseStart_252440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_252440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_252440 prefixEnd_252440 := by exact prefixLift 252440
  have htrace : WordTrace (prefixWord ++ tailWord_252440) baseStart_252440 baseEnd_252440 := by
    simpa [prefixWord, tailWord_252440, baseEnd_252440] using wordTrace_append hprefix tailTrace_252440
  have hstable : (prefixWord ++ tailWord_252440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252440).length < 2 ^ (prefixWord ++ tailWord_252440).sum := by decide
  have hdescent : baseEnd_252440 < baseStart_252440 := by decide
  rcases family_descends (prefixWord ++ tailWord_252440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252444 : List Nat := [2, 2, 3, 1, 2, 4, 2, 2, 4]
def baseStart_252444 : Nat := 118140960795 + 252444 * 2 ^ 59
def prefixEnd_252444 : Nat := 4983230072969 + 3 ^ 40 * 252444 * 2
def baseEnd_252444 : Nat := 28805580076381232308675

theorem tailTrace_252444 : CollatzResearch.WordTrace tailWord_252444 prefixEnd_252444 28805580076381232308675 := by
  unfold tailWord_252444
  simp only [CollatzResearch.WordTrace]
  refine ⟨4603694548722988423914193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6138259398297317898552257 4603694548722988423914193)
  ·
    refine ⟨3452770911542241317935645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4603694548722988423914193 3452770911542241317935645)
    ·
      refine ⟨1294789091828340494225867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3452770911542241317935645 1294789091828340494225867)
      ·
        refine ⟨1942183637742510741338801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1294789091828340494225867 1942183637742510741338801)
        ·
          refine ⟨1456637728306883056004101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1942183637742510741338801 1456637728306883056004101)
          ·
            refine ⟨273119574057540573000769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1456637728306883056004101 273119574057540573000769)
            ·
              refine ⟨204839680543155429750577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273119574057540573000769 204839680543155429750577)
              ·
                refine ⟨153629760407366572312933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 204839680543155429750577 153629760407366572312933)
                ·
                  refine ⟨28805580076381232308675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 153629760407366572312933 28805580076381232308675)
                  ·
                    rfl

theorem cell22_252444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 4, 2, 2, 4].length) (baseStart_252444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_252444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_252444 prefixEnd_252444 := by exact prefixLift 252444
  have htrace : WordTrace (prefixWord ++ tailWord_252444) baseStart_252444 baseEnd_252444 := by
    simpa [prefixWord, tailWord_252444, baseEnd_252444] using wordTrace_append hprefix tailTrace_252444
  have hstable : (prefixWord ++ tailWord_252444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252444).length < 2 ^ (prefixWord ++ tailWord_252444).sum := by decide
  have hdescent : baseEnd_252444 < baseStart_252444 := by decide
  rcases family_descends (prefixWord ++ tailWord_252444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252500 : List Nat := [2, 4, 1, 1, 1, 4, 1, 1, 7]
def baseStart_252500 : Nat := 118140960795 + 252500 * 2 ^ 59
def prefixEnd_252500 : Nat := 4983230072969 + 3 ^ 40 * 252500 * 2
def baseEnd_252500 : Nat := 28811970057859405841951

theorem tailTrace_252500 : CollatzResearch.WordTrace tailWord_252500 prefixEnd_252500 28811970057859405841951 := by
  unfold tailWord_252500
  simp only [CollatzResearch.WordTrace]
  refine ⟨4604715792621549205933477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6139621056828732274577969 4604715792621549205933477)
  ·
    refine ⟨863384211116540476112527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4604715792621549205933477 863384211116540476112527)
    ·
      refine ⟨1295076316674810714168791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 863384211116540476112527 1295076316674810714168791)
      ·
        refine ⟨1942614475012216071253187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1295076316674810714168791 1942614475012216071253187)
        ·
          refine ⟨2913921712518324106879781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1942614475012216071253187 2913921712518324106879781)
          ·
            refine ⟨546360321097185770039959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2913921712518324106879781 546360321097185770039959)
            ·
              refine ⟨819540481645778655059939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 546360321097185770039959 819540481645778655059939)
              ·
                refine ⟨1229310722468667982589909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 819540481645778655059939 1229310722468667982589909)
                ·
                  refine ⟨28811970057859405841951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1229310722468667982589909 28811970057859405841951)
                  ·
                    rfl

theorem cell22_252500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 1, 1, 7].length) (baseStart_252500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_252500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_252500 prefixEnd_252500 := by exact prefixLift 252500
  have htrace : WordTrace (prefixWord ++ tailWord_252500) baseStart_252500 baseEnd_252500 := by
    simpa [prefixWord, tailWord_252500, baseEnd_252500] using wordTrace_append hprefix tailTrace_252500
  have hstable : (prefixWord ++ tailWord_252500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252500).length < 2 ^ (prefixWord ++ tailWord_252500).sum := by decide
  have hdescent : baseEnd_252500 < baseStart_252500 := by decide
  rcases family_descends (prefixWord ++ tailWord_252500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252510 : List Nat := [4, 4, 1, 2, 1, 1, 3, 1, 2, 3]
def baseStart_252510 : Nat := 118140960795 + 252510 * 2 ^ 59
def prefixEnd_252510 : Nat := 4983230072969 + 3 ^ 40 * 252510 * 2
def baseEnd_252510 : Nat := 86439333377941524775823

theorem tailTrace_252510 : CollatzResearch.WordTrace tailWord_252510 prefixEnd_252510 86439333377941524775823 := by
  unfold tailWord_252510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1151224539400858764966373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6139864210137913413153989 1151224539400858764966373)
  ·
    refine ⟨215854601137661018431195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1151224539400858764966373 215854601137661018431195)
    ·
      refine ⟨323781901706491527646793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 215854601137661018431195 323781901706491527646793)
      ·
        refine ⟨242836426279868645735095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 323781901706491527646793 242836426279868645735095)
        ·
          refine ⟨364254639419802968602643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 242836426279868645735095 364254639419802968602643)
          ·
            refine ⟨546381959129704452903965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364254639419802968602643 546381959129704452903965)
            ·
              refine ⟨204893234673639169838987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 546381959129704452903965 204893234673639169838987)
              ·
                refine ⟨307339852010458754758481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204893234673639169838987 307339852010458754758481)
                ·
                  refine ⟨230504889007844066068861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 307339852010458754758481 230504889007844066068861)
                  ·
                    refine ⟨86439333377941524775823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 230504889007844066068861 86439333377941524775823)
                    ·
                      rfl

theorem cell22_252510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 3, 1, 2, 3].length) (baseStart_252510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_252510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_252510 prefixEnd_252510 := by exact prefixLift 252510
  have htrace : WordTrace (prefixWord ++ tailWord_252510) baseStart_252510 baseEnd_252510 := by
    simpa [prefixWord, tailWord_252510, baseEnd_252510] using wordTrace_append hprefix tailTrace_252510
  have hstable : (prefixWord ++ tailWord_252510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252510).length < 2 ^ (prefixWord ++ tailWord_252510).sum := by decide
  have hdescent : baseEnd_252510 < baseStart_252510 := by decide
  rcases family_descends (prefixWord ++ tailWord_252510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252562 : List Nat := [3, 2, 3, 1, 2, 1, 3, 1, 6]
def baseStart_252562 : Nat := 118140960795 + 252562 * 2 ^ 59
def prefixEnd_252562 : Nat := 4983230072969 + 3 ^ 40 * 252562 * 2
def baseEnd_252562 : Nat := 28819044680210240825221

theorem tailTrace_252562 : CollatzResearch.WordTrace tailWord_252562 prefixEnd_252562 28819044680210240825221 := by
  unfold tailWord_252562
  simp only [CollatzResearch.WordTrace]
  refine ⟨2302923227754620750155985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6141128607345655333749293 2302923227754620750155985)
  ·
    refine ⟨1727192420815965562616989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2302923227754620750155985 1727192420815965562616989)
    ·
      refine ⟨647697157805987085981371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1727192420815965562616989 647697157805987085981371)
      ·
        refine ⟨971545736708980628972057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 647697157805987085981371 971545736708980628972057)
        ·
          refine ⟨728659302531735471729043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 971545736708980628972057 728659302531735471729043)
          ·
            refine ⟨1092988953797603207593565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 728659302531735471729043 1092988953797603207593565)
            ·
              refine ⟨409870857674101202847587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1092988953797603207593565 409870857674101202847587)
              ·
                refine ⟨614806286511151804271381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 409870857674101202847587 614806286511151804271381)
                ·
                  refine ⟨28819044680210240825221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 614806286511151804271381 28819044680210240825221)
                  ·
                    rfl

theorem cell22_252562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_252562 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_252562 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_252562 prefixEnd_252562 := by exact prefixLift 252562
  have htrace : WordTrace (prefixWord ++ tailWord_252562) baseStart_252562 baseEnd_252562 := by
    simpa [prefixWord, tailWord_252562, baseEnd_252562] using wordTrace_append hprefix tailTrace_252562
  have hstable : (prefixWord ++ tailWord_252562).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252562).length < 2 ^ (prefixWord ++ tailWord_252562).sum := by decide
  have hdescent : baseEnd_252562 < baseStart_252562 := by decide
  rcases family_descends (prefixWord ++ tailWord_252562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252598 : List Nat := [5, 1, 3, 1, 2, 1, 3, 1, 1, 4]
def baseStart_252598 : Nat := 118140960795 + 252598 * 2 ^ 59
def prefixEnd_252598 : Nat := 4983230072969 + 3 ^ 40 * 252598 * 2
def baseEnd_252598 : Nat := 86469457576338628575553

theorem tailTrace_252598 : CollatzResearch.WordTrace tailWord_252598 prefixEnd_252598 86469457576338628575553 := by
  unfold tailWord_252598
  simp only [CollatzResearch.WordTrace]
  refine ⟨575812871180503821808403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6142003959258707432622965 575812871180503821808403)
  ·
    refine ⟨863719306770755732712605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 575812871180503821808403 863719306770755732712605)
    ·
      refine ⟨323894740039033399767227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 863719306770755732712605 323894740039033399767227)
      ·
        refine ⟨485842110058550099650841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 323894740039033399767227 485842110058550099650841)
        ·
          refine ⟨364381582543912574738131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 485842110058550099650841 364381582543912574738131)
          ·
            refine ⟨546572373815868862107197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364381582543912574738131 546572373815868862107197)
            ·
              refine ⟨204964640180950823290199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 546572373815868862107197 204964640180950823290199)
              ·
                refine ⟨307446960271426234935299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 204964640180950823290199 307446960271426234935299)
                ·
                  refine ⟨461170440407139352402949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 307446960271426234935299 461170440407139352402949)
                  ·
                    refine ⟨86469457576338628575553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 461170440407139352402949 86469457576338628575553)
                    ·
                      rfl

theorem cell22_252598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_252598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_252598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_252598 prefixEnd_252598 := by exact prefixLift 252598
  have htrace : WordTrace (prefixWord ++ tailWord_252598) baseStart_252598 baseEnd_252598 := by
    simpa [prefixWord, tailWord_252598, baseEnd_252598] using wordTrace_append hprefix tailTrace_252598
  have hstable : (prefixWord ++ tailWord_252598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252598).length < 2 ^ (prefixWord ++ tailWord_252598).sum := by decide
  have hdescent : baseEnd_252598 < baseStart_252598 := by decide
  rcases family_descends (prefixWord ++ tailWord_252598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252650 : List Nat := [3, 1, 3, 1, 1, 1, 1, 1, 3, 7]
def baseStart_252650 : Nat := 118140960795 + 252650 * 2 ^ 59
def prefixEnd_252650 : Nat := 4983230072969 + 3 ^ 40 * 252650 * 2
def baseEnd_252650 : Nat := 86487258239027826275393

theorem tailTrace_252650 : CollatzResearch.WordTrace tailWord_252650 prefixEnd_252650 86487258239027826275393 := by
  unfold tailWord_252650
  simp only [CollatzResearch.WordTrace]
  refine ⟨2303725633674918507456851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6143268356466449353218269 2303725633674918507456851)
  ·
    refine ⟨3455588450512377761185277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2303725633674918507456851 3455588450512377761185277)
    ·
      refine ⟨1295845668942141660444479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3455588450512377761185277 1295845668942141660444479)
      ·
        refine ⟨1943768503413212490666719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1295845668942141660444479 1943768503413212490666719)
        ·
          refine ⟨2915652755119818736000079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1943768503413212490666719 2915652755119818736000079)
          ·
            refine ⟨4373479132679728104000119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2915652755119818736000079 4373479132679728104000119)
            ·
              refine ⟨6560218699019592156000179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4373479132679728104000119 6560218699019592156000179)
              ·
                refine ⟨9840328048529388234000269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6560218699019592156000179 9840328048529388234000269)
                ·
                  refine ⟨3690123018198520587750101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 9840328048529388234000269 3690123018198520587750101)
                  ·
                    refine ⟨86487258239027826275393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3690123018198520587750101 86487258239027826275393)
                    ·
                      rfl

theorem cell22_252650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_252650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_252650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_252650 prefixEnd_252650 := by exact prefixLift 252650
  have htrace : WordTrace (prefixWord ++ tailWord_252650) baseStart_252650 baseEnd_252650 := by
    simpa [prefixWord, tailWord_252650, baseEnd_252650] using wordTrace_append hprefix tailTrace_252650
  have hstable : (prefixWord ++ tailWord_252650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252650).length < 2 ^ (prefixWord ++ tailWord_252650).sum := by decide
  have hdescent : baseEnd_252650 < baseStart_252650 := by decide
  rcases family_descends (prefixWord ++ tailWord_252650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252712 : List Nat := [2, 1, 5, 1, 1, 1, 2, 1, 3, 5]
def baseStart_252712 : Nat := 118140960795 + 252712 * 2 ^ 59
def prefixEnd_252712 : Nat := 4983230072969 + 3 ^ 40 * 252712 * 2
def baseEnd_252712 : Nat := 86508482106080331225203

theorem tailTrace_252712 : CollatzResearch.WordTrace tailWord_252712 prefixEnd_252712 86508482106080331225203 := by
  unfold tailWord_252712
  simp only [CollatzResearch.WordTrace]
  refine ⟨4608581930237529309292195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6144775906983372412389593 4608581930237529309292195)
  ·
    refine ⟨6912872895356293963938293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4608581930237529309292195 6912872895356293963938293)
    ·
      refine ⟨648081833939652559119215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 6912872895356293963938293 648081833939652559119215)
      ·
        refine ⟨972122750909478838678823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 648081833939652559119215 972122750909478838678823)
        ·
          refine ⟨1458184126364218258018235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 972122750909478838678823 1458184126364218258018235)
          ·
            refine ⟨2187276189546327387027353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1458184126364218258018235 2187276189546327387027353)
            ·
              refine ⟨1640457142159745540270515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2187276189546327387027353 1640457142159745540270515)
              ·
                refine ⟨2460685713239618310405773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1640457142159745540270515 2460685713239618310405773)
                ·
                  refine ⟨922757142464856866402165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2460685713239618310405773 922757142464856866402165)
                  ·
                    refine ⟨86508482106080331225203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 922757142464856866402165 86508482106080331225203)
                    ·
                      rfl

theorem cell22_252712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 2, 1, 3, 5].length) (baseStart_252712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_252712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_252712 prefixEnd_252712 := by exact prefixLift 252712
  have htrace : WordTrace (prefixWord ++ tailWord_252712) baseStart_252712 baseEnd_252712 := by
    simpa [prefixWord, tailWord_252712, baseEnd_252712] using wordTrace_append hprefix tailTrace_252712
  have hstable : (prefixWord ++ tailWord_252712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252712).length < 2 ^ (prefixWord ++ tailWord_252712).sum := by decide
  have hdescent : baseEnd_252712 < baseStart_252712 := by decide
  rcases family_descends (prefixWord ++ tailWord_252712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252727 : List Nat := [1, 1, 3, 1, 2, 1, 5, 2, 2, 4]
def baseStart_252727 : Nat := 118140960795 + 252727 * 2 ^ 59
def prefixEnd_252727 : Nat := 4983230072969 + 3 ^ 40 * 252727 * 2
def baseEnd_252727 : Nat := 86513616912625292100157

theorem tailTrace_252727 : CollatzResearch.WordTrace tailWord_252727 prefixEnd_252727 86513616912625292100157 := by
  unfold tailWord_252727
  simp only [CollatzResearch.WordTrace]
  refine ⟨9217710955420716180380435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6145140636947144120253623 9217710955420716180380435)
  ·
    refine ⟨13826566433131074270570653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9217710955420716180380435 13826566433131074270570653)
    ·
      refine ⟨5184962412424152851463995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13826566433131074270570653 5184962412424152851463995)
      ·
        refine ⟨7777443618636229277195993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5184962412424152851463995 7777443618636229277195993)
        ·
          refine ⟨5833082713977171957896995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7777443618636229277195993 5833082713977171957896995)
          ·
            refine ⟨8749624070965757936845493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5833082713977171957896995 8749624070965757936845493)
            ·
              refine ⟨820277256653039806579265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8749624070965757936845493 820277256653039806579265)
              ·
                refine ⟨615207942489779854934449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 820277256653039806579265 615207942489779854934449)
                ·
                  refine ⟨461405956867334891200837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 615207942489779854934449 461405956867334891200837)
                  ·
                    refine ⟨86513616912625292100157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 461405956867334891200837 86513616912625292100157)
                    ·
                      rfl

theorem cell22_252727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_252727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_252727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_252727 prefixEnd_252727 := by exact prefixLift 252727
  have htrace : WordTrace (prefixWord ++ tailWord_252727) baseStart_252727 baseEnd_252727 := by
    simpa [prefixWord, tailWord_252727, baseEnd_252727] using wordTrace_append hprefix tailTrace_252727
  have hstable : (prefixWord ++ tailWord_252727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252727).length < 2 ^ (prefixWord ++ tailWord_252727).sum := by decide
  have hdescent : baseEnd_252727 < baseStart_252727 := by decide
  rcases family_descends (prefixWord ++ tailWord_252727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252787 : List Nat := [1, 1, 1, 2, 2, 1, 5, 4, 5]
def baseStart_252787 : Nat := 118140960795 + 252787 * 2 ^ 59
def prefixEnd_252787 : Nat := 4983230072969 + 3 ^ 40 * 252787 * 2
def baseEnd_252787 : Nat := 28844718712935045199991

theorem tailTrace_252787 : CollatzResearch.WordTrace tailWord_252787 prefixEnd_252787 28844718712935045199991 := by
  unfold tailWord_252787
  simp only [CollatzResearch.WordTrace]
  refine ⟨9219899335203346427564615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6146599556802230951709743 9219899335203346427564615)
  ·
    refine ⟨13829849002805019641346923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9219899335203346427564615 13829849002805019641346923)
    ·
      refine ⟨20744773504207529462020385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13829849002805019641346923 20744773504207529462020385)
      ·
        refine ⟨15558580128155647096515289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 20744773504207529462020385 15558580128155647096515289)
        ·
          refine ⟨11668935096116735322386467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15558580128155647096515289 11668935096116735322386467)
          ·
            refine ⟨17503402644175102983579701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11668935096116735322386467 17503402644175102983579701)
            ·
              refine ⟨1640943997891415904710597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17503402644175102983579701 1640943997891415904710597)
              ·
                refine ⟨307676999604640482133237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1640943997891415904710597 307676999604640482133237)
                ·
                  refine ⟨28844718712935045199991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 307676999604640482133237 28844718712935045199991)
                  ·
                    rfl

theorem cell22_252787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 5, 4, 5].length) (baseStart_252787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_252787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_252787 prefixEnd_252787 := by exact prefixLift 252787
  have htrace : WordTrace (prefixWord ++ tailWord_252787) baseStart_252787 baseEnd_252787 := by
    simpa [prefixWord, tailWord_252787, baseEnd_252787] using wordTrace_append hprefix tailTrace_252787
  have hstable : (prefixWord ++ tailWord_252787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252787).length < 2 ^ (prefixWord ++ tailWord_252787).sum := by decide
  have hdescent : baseEnd_252787 < baseStart_252787 := by decide
  rcases family_descends (prefixWord ++ tailWord_252787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252864 : List Nat := [2, 1, 1, 2, 3, 3, 3, 1, 1, 5]
def baseStart_252864 : Nat := 118140960795 + 252864 * 2 ^ 59
def prefixEnd_252864 : Nat := 4983230072969 + 3 ^ 40 * 252864 * 2
def baseEnd_252864 : Nat := 86560514812402601424737

theorem tailTrace_252864 : CollatzResearch.WordTrace tailWord_252864 prefixEnd_252864 86560514812402601424737 := by
  unfold tailWord_252864
  simp only [CollatzResearch.WordTrace]
  refine ⟨4611353877962194289058823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6148471837282925718745097 4611353877962194289058823)
  ·
    refine ⟨6917030816943291433588235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4611353877962194289058823 6917030816943291433588235)
    ·
      refine ⟨10375546225414937150382353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6917030816943291433588235 10375546225414937150382353)
      ·
        refine ⟨7781659669061202862786765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10375546225414937150382353 7781659669061202862786765)
        ·
          refine ⟨2918122375897951073545037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7781659669061202862786765 2918122375897951073545037)
          ·
            refine ⟨1094295890961731652579389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2918122375897951073545037 1094295890961731652579389)
            ·
              refine ⟨410360959110649369717271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1094295890961731652579389 410360959110649369717271)
              ·
                refine ⟨615541438665974054575907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410360959110649369717271 615541438665974054575907)
                ·
                  refine ⟨923312157998961081863861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 615541438665974054575907 923312157998961081863861)
                  ·
                    refine ⟨86560514812402601424737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 923312157998961081863861 86560514812402601424737)
                    ·
                      rfl

theorem cell22_252864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 3, 3, 1, 1, 5].length) (baseStart_252864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_252864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_252864 prefixEnd_252864 := by exact prefixLift 252864
  have htrace : WordTrace (prefixWord ++ tailWord_252864) baseStart_252864 baseEnd_252864 := by
    simpa [prefixWord, tailWord_252864, baseEnd_252864] using wordTrace_append hprefix tailTrace_252864
  have hstable : (prefixWord ++ tailWord_252864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252864).length < 2 ^ (prefixWord ++ tailWord_252864).sum := by decide
  have hdescent : baseEnd_252864 < baseStart_252864 := by decide
  rcases family_descends (prefixWord ++ tailWord_252864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252898 : List Nat := [3, 3, 3, 1, 1, 1, 2, 1, 4, 3]
def baseStart_252898 : Nat := 118140960795 + 252898 * 2 ^ 59
def prefixEnd_252898 : Nat := 4983230072969 + 3 ^ 40 * 252898 * 2
def baseEnd_252898 : Nat := 86572153707237846074633

theorem tailTrace_252898 : CollatzResearch.WordTrace tailWord_252898 prefixEnd_252898 86572153707237846074633 := by
  unfold tailWord_252898
  simp only [CollatzResearch.WordTrace]
  refine ⟨2305986959450303096213837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6149298558534141589903565 2305986959450303096213837)
  ·
    refine ⟨864745109793863661080189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2305986959450303096213837 864745109793863661080189)
    ·
      refine ⟨324279416172698872905071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 864745109793863661080189 324279416172698872905071)
      ·
        refine ⟨486419124259048309357607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324279416172698872905071 486419124259048309357607)
        ·
          refine ⟨729628686388572464036411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 486419124259048309357607 729628686388572464036411)
          ·
            refine ⟨1094443029582858696054617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729628686388572464036411 1094443029582858696054617)
            ·
              refine ⟨820832272187144022040963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1094443029582858696054617 820832272187144022040963)
              ·
                refine ⟨1231248408280716033061445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 820832272187144022040963 1231248408280716033061445)
                ·
                  refine ⟨230859076552634256199021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1231248408280716033061445 230859076552634256199021)
                  ·
                    refine ⟨86572153707237846074633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 230859076552634256199021 86572153707237846074633)
                    ·
                      rfl

theorem cell22_252898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 1, 1, 2, 1, 4, 3].length) (baseStart_252898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_252898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_252898 prefixEnd_252898 := by exact prefixLift 252898
  have htrace : WordTrace (prefixWord ++ tailWord_252898) baseStart_252898 baseEnd_252898 := by
    simpa [prefixWord, tailWord_252898, baseEnd_252898] using wordTrace_append hprefix tailTrace_252898
  have hstable : (prefixWord ++ tailWord_252898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252898).length < 2 ^ (prefixWord ++ tailWord_252898).sum := by decide
  have hdescent : baseEnd_252898 < baseStart_252898 := by decide
  rcases family_descends (prefixWord ++ tailWord_252898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252930 : List Nat := [3, 4, 1, 3, 1, 1, 2, 1, 2, 4]
def baseStart_252930 : Nat := 118140960795 + 252930 * 2 ^ 59
def prefixEnd_252930 : Nat := 4983230072969 + 3 ^ 40 * 252930 * 2
def baseEnd_252930 : Nat := 86583107961200429274535

theorem tailTrace_252930 : CollatzResearch.WordTrace tailWord_252930 prefixEnd_252930 86583107961200429274535 := by
  unfold tailWord_252930
  simp only [CollatzResearch.WordTrace]
  refine ⟨2306278743421320462505061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6150076649123521233346829 2306278743421320462505061)
  ·
    refine ⟨432427264391497586719699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2306278743421320462505061 432427264391497586719699)
    ·
      refine ⟨648640896587246380079549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 432427264391497586719699 648640896587246380079549)
      ·
        refine ⟨243240336220217392529831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 648640896587246380079549 243240336220217392529831)
        ·
          refine ⟨364860504330326088794747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243240336220217392529831 364860504330326088794747)
          ·
            refine ⟨547290756495489133192121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 364860504330326088794747 547290756495489133192121)
            ·
              refine ⟨410468067371616849894091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 547290756495489133192121 410468067371616849894091)
              ·
                refine ⟨615702101057425274841137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 410468067371616849894091 615702101057425274841137)
                ·
                  refine ⟨461776575793068956130853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 615702101057425274841137 461776575793068956130853)
                  ·
                    refine ⟨86583107961200429274535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 461776575793068956130853 86583107961200429274535)
                    ·
                      rfl

theorem cell22_252930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 1, 2, 4].length) (baseStart_252930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_252930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_252930 prefixEnd_252930 := by exact prefixLift 252930
  have htrace : WordTrace (prefixWord ++ tailWord_252930) baseStart_252930 baseEnd_252930 := by
    simpa [prefixWord, tailWord_252930, baseEnd_252930] using wordTrace_append hprefix tailTrace_252930
  have hstable : (prefixWord ++ tailWord_252930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252930).length < 2 ^ (prefixWord ++ tailWord_252930).sum := by decide
  have hdescent : baseEnd_252930 < baseStart_252930 := by decide
  rcases family_descends (prefixWord ++ tailWord_252930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252954 : List Nat := [3, 1, 1, 3, 1, 2, 2, 2, 2, 5]
def baseStart_252954 : Nat := 118140960795 + 252954 * 2 ^ 59
def prefixEnd_252954 : Nat := 4983230072969 + 3 ^ 40 * 252954 * 2
def baseEnd_252954 : Nat := 86591323651672366674461

theorem tailTrace_252954 : CollatzResearch.WordTrace tailWord_252954 prefixEnd_252954 86591323651672366674461 := by
  unfold tailWord_252954
  simp only [CollatzResearch.WordTrace]
  refine ⟨2306497581399583487223479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6150660217065555965929277 2306497581399583487223479)
  ·
    refine ⟨3459746372099375230835219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2306497581399583487223479 3459746372099375230835219)
    ·
      refine ⟨5189619558149062846252829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3459746372099375230835219 5189619558149062846252829)
      ·
        refine ⟨1946107334305898567344811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5189619558149062846252829 1946107334305898567344811)
        ·
          refine ⟨2919161001458847851017217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1946107334305898567344811 2919161001458847851017217)
          ·
            refine ⟨2189370751094135888262913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2919161001458847851017217 2189370751094135888262913)
            ·
              refine ⟨1642028063320601916197185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2189370751094135888262913 1642028063320601916197185)
              ·
                refine ⟨1231521047490451437147889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1642028063320601916197185 1231521047490451437147889)
                ·
                  refine ⟨923640785617838577860917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1231521047490451437147889 923640785617838577860917)
                  ·
                    refine ⟨86591323651672366674461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 923640785617838577860917 86591323651672366674461)
                    ·
                      rfl

theorem cell22_252954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 2, 2, 5].length) (baseStart_252954 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_252954 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_252954 prefixEnd_252954 := by exact prefixLift 252954
  have htrace : WordTrace (prefixWord ++ tailWord_252954) baseStart_252954 baseEnd_252954 := by
    simpa [prefixWord, tailWord_252954, baseEnd_252954] using wordTrace_append hprefix tailTrace_252954
  have hstable : (prefixWord ++ tailWord_252954).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252954).length < 2 ^ (prefixWord ++ tailWord_252954).sum := by decide
  have hdescent : baseEnd_252954 < baseStart_252954 := by decide
  rcases family_descends (prefixWord ++ tailWord_252954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_252984 : List Nat := [2, 1, 2, 1, 5, 1, 1, 1, 8]
def baseStart_252984 : Nat := 118140960795 + 252984 * 2 ^ 59
def prefixEnd_252984 : Nat := 4983230072969 + 3 ^ 40 * 252984 * 2
def baseEnd_252984 : Nat := 28867197754920762808123

theorem tailTrace_252984 : CollatzResearch.WordTrace tailWord_252984 prefixEnd_252984 28867197754920762808123 := by
  unfold tailWord_252984
  simp only [CollatzResearch.WordTrace]
  refine ⟨4613542257744824536243003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6151389676993099381657337 4613542257744824536243003)
  ·
    refine ⟨6920313386617236804364505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4613542257744824536243003 6920313386617236804364505)
    ·
      refine ⟨5190235039962927603273379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6920313386617236804364505 5190235039962927603273379)
      ·
        refine ⟨7785352559944391404910069, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5190235039962927603273379 7785352559944391404910069)
        ·
          refine ⟨729876802494786694210319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7785352559944391404910069 729876802494786694210319)
          ·
            refine ⟨1094815203742180041315479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 729876802494786694210319 1094815203742180041315479)
            ·
              refine ⟨1642222805613270061973219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1094815203742180041315479 1642222805613270061973219)
              ·
                refine ⟨2463334208419905092959829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1642222805613270061973219 2463334208419905092959829)
                ·
                  refine ⟨28867197754920762808123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2463334208419905092959829 28867197754920762808123)
                  ·
                    rfl

theorem cell22_252984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 1, 8].length) (baseStart_252984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_252984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_252984 prefixEnd_252984 := by exact prefixLift 252984
  have htrace : WordTrace (prefixWord ++ tailWord_252984) baseStart_252984 baseEnd_252984 := by
    simpa [prefixWord, tailWord_252984, baseEnd_252984] using wordTrace_append hprefix tailTrace_252984
  have hstable : (prefixWord ++ tailWord_252984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_252984).length < 2 ^ (prefixWord ++ tailWord_252984).sum := by decide
  have hdescent : baseEnd_252984 < baseStart_252984 := by decide
  rcases family_descends (prefixWord ++ tailWord_252984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253016 : List Nat := [2, 1, 2, 2, 1, 3, 3, 1, 4, 3]
def baseStart_253016 : Nat := 118140960795 + 253016 * 2 ^ 59
def prefixEnd_253016 : Nat := 4983230072969 + 3 ^ 40 * 253016 * 2
def baseEnd_253016 : Nat := 86612547518724871624271

theorem tailTrace_253016 : CollatzResearch.WordTrace tailWord_253016 prefixEnd_253016 86612547518724871624271 := by
  unfold tailWord_253016
  simp only [CollatzResearch.WordTrace]
  refine ⟨4614125825686859268825451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6152167767582479025100601 4614125825686859268825451)
  ·
    refine ⟨6921188738530288903238177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4614125825686859268825451 6921188738530288903238177)
    ·
      refine ⟨5190891553897716677428633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6921188738530288903238177 5190891553897716677428633)
      ·
        refine ⟨3893168665423287508071475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5190891553897716677428633 3893168665423287508071475)
        ·
          refine ⟨5839752998134931262107213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3893168665423287508071475 5839752998134931262107213)
          ·
            refine ⟨2189907374300599223290205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5839752998134931262107213 2189907374300599223290205)
            ·
              refine ⟨821215265362724708733827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2189907374300599223290205 821215265362724708733827)
              ·
                refine ⟨1231822898044087063100741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 821215265362724708733827 1231822898044087063100741)
                ·
                  refine ⟨230966793383266324331389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1231822898044087063100741 230966793383266324331389)
                  ·
                    refine ⟨86612547518724871624271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 230966793383266324331389 86612547518724871624271)
                    ·
                      rfl

theorem cell22_253016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 1, 4, 3].length) (baseStart_253016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253016 prefixEnd_253016 := by exact prefixLift 253016
  have htrace : WordTrace (prefixWord ++ tailWord_253016) baseStart_253016 baseEnd_253016 := by
    simpa [prefixWord, tailWord_253016, baseEnd_253016] using wordTrace_append hprefix tailTrace_253016
  have hstable : (prefixWord ++ tailWord_253016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253016).length < 2 ^ (prefixWord ++ tailWord_253016).sum := by decide
  have hdescent : baseEnd_253016 < baseStart_253016 := by decide
  rcases family_descends (prefixWord ++ tailWord_253016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253029 : List Nat := [1, 3, 1, 3, 2, 1, 2, 9]
def baseStart_253029 : Nat := 118140960795 + 253029 * 2 ^ 59
def prefixEnd_253029 : Nat := 4983230072969 + 3 ^ 40 * 253029 * 2
def baseEnd_253029 : Nat := 9624110853821907894359

theorem tailTrace_253029 : CollatzResearch.WordTrace tailWord_253029 prefixEnd_253029 9624110853821907894359 := by
  unfold tailWord_253029
  simp only [CollatzResearch.WordTrace]
  refine ⟨9228725800326621757874141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6152483866884414505249427 9228725800326621757874141)
  ·
    refine ⟨3460772175122483159202803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9228725800326621757874141 3460772175122483159202803)
    ·
      refine ⟨5191158262683724738804205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3460772175122483159202803 5191158262683724738804205)
      ·
        refine ⟨1946684348506396777051577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5191158262683724738804205 1946684348506396777051577)
        ·
          refine ⟨1460013261379797582788683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1946684348506396777051577 1460013261379797582788683)
          ·
            refine ⟨2190019892069696374183025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1460013261379797582788683 2190019892069696374183025)
            ·
              refine ⟨1642514919052272280637269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2190019892069696374183025 1642514919052272280637269)
              ·
                refine ⟨9624110853821907894359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 1642514919052272280637269 9624110853821907894359)
                ·
                  rfl

theorem cell22_253029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 9].length) (baseStart_253029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253029 prefixEnd_253029 := by exact prefixLift 253029
  have htrace : WordTrace (prefixWord ++ tailWord_253029) baseStart_253029 baseEnd_253029 := by
    simpa [prefixWord, tailWord_253029, baseEnd_253029] using wordTrace_append hprefix tailTrace_253029
  have hstable : (prefixWord ++ tailWord_253029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253029).length < 2 ^ (prefixWord ++ tailWord_253029).sum := by decide
  have hdescent : baseEnd_253029 < baseStart_253029 := by decide
  rcases family_descends (prefixWord ++ tailWord_253029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253046 : List Nat := [5, 1, 1, 2, 1, 1, 3, 8]
def baseStart_253046 : Nat := 118140960795 + 253046 * 2 ^ 59
def prefixEnd_253046 : Nat := 4983230072969 + 3 ^ 40 * 253046 * 2
def baseEnd_253046 : Nat := 9624757459090532597131

theorem tailTrace_253046 : CollatzResearch.WordTrace tailWord_253046 prefixEnd_253046 9624757459090532597131 := by
  unfold tailWord_253046
  simp only [CollatzResearch.WordTrace]
  refine ⟨576834115079064603827687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6152897227510022440828661 576834115079064603827687)
  ·
    refine ⟨865251172618596905741531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 576834115079064603827687 865251172618596905741531)
    ·
      refine ⟨1297876758927895358612297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 865251172618596905741531 1297876758927895358612297)
      ·
        refine ⟨973407569195921518959223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1297876758927895358612297 973407569195921518959223)
        ·
          refine ⟨1460111353793882278438835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 973407569195921518959223 1460111353793882278438835)
          ·
            refine ⟨2190167030690823417658253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1460111353793882278438835 2190167030690823417658253)
            ·
              refine ⟨821312636509058781621845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2190167030690823417658253 821312636509058781621845)
              ·
                refine ⟨9624757459090532597131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 821312636509058781621845 9624757459090532597131)
                ·
                  rfl

theorem cell22_253046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 8].length) (baseStart_253046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253046 prefixEnd_253046 := by exact prefixLift 253046
  have htrace : WordTrace (prefixWord ++ tailWord_253046) baseStart_253046 baseEnd_253046 := by
    simpa [prefixWord, tailWord_253046, baseEnd_253046] using wordTrace_append hprefix tailTrace_253046
  have hstable : (prefixWord ++ tailWord_253046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253046).length < 2 ^ (prefixWord ++ tailWord_253046).sum := by decide
  have hdescent : baseEnd_253046 < baseStart_253046 := by decide
  rcases family_descends (prefixWord ++ tailWord_253046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253104 : List Nat := [2, 1, 1, 1, 2, 1, 2, 2, 2, 8]
def baseStart_253104 : Nat := 118140960795 + 253104 * 2 ^ 59
def prefixEnd_253104 : Nat := 4983230072969 + 3 ^ 40 * 253104 * 2
def baseEnd_253104 : Nat := 86642671717121975424001

theorem tailTrace_253104 : CollatzResearch.WordTrace tailWord_253104 prefixEnd_253104 86642671717121975424001 := by
  unfold tailWord_253104
  simp only [CollatzResearch.WordTrace]
  refine ⟨4615730637527454783427183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6154307516703273044569577 4615730637527454783427183)
  ·
    refine ⟨6923595956291182175140775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4615730637527454783427183 6923595956291182175140775)
    ·
      refine ⟨10385393934436773262711163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6923595956291182175140775 10385393934436773262711163)
      ·
        refine ⟨15578090901655159894066745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10385393934436773262711163 15578090901655159894066745)
        ·
          refine ⟨11683568176241369920550059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15578090901655159894066745 11683568176241369920550059)
          ·
            refine ⟨17525352264362054880825089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11683568176241369920550059 17525352264362054880825089)
            ·
              refine ⟨13144014198271541160618817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17525352264362054880825089 13144014198271541160618817)
              ·
                refine ⟨9858010648703655870464113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13144014198271541160618817 9858010648703655870464113)
                ·
                  refine ⟨7393507986527741902848085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9858010648703655870464113 7393507986527741902848085)
                  ·
                    refine ⟨86642671717121975424001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7393507986527741902848085 86642671717121975424001)
                    ·
                      rfl

theorem cell22_253104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 2, 2, 8].length) (baseStart_253104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253104 prefixEnd_253104 := by exact prefixLift 253104
  have htrace : WordTrace (prefixWord ++ tailWord_253104) baseStart_253104 baseEnd_253104 := by
    simpa [prefixWord, tailWord_253104, baseEnd_253104] using wordTrace_append hprefix tailTrace_253104
  have hstable : (prefixWord ++ tailWord_253104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253104).length < 2 ^ (prefixWord ++ tailWord_253104).sum := by decide
  have hdescent : baseEnd_253104 < baseStart_253104 := by decide
  rcases family_descends (prefixWord ++ tailWord_253104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253140 : List Nat := [2, 4, 1, 4, 1, 1, 1, 1, 2, 5]
def baseStart_253140 : Nat := 118140960795 + 253140 * 2 ^ 59
def prefixEnd_253140 : Nat := 4983230072969 + 3 ^ 40 * 253140 * 2
def baseEnd_253140 : Nat := 86654995252829881523891

theorem tailTrace_253140 : CollatzResearch.WordTrace tailWord_253140 prefixEnd_253140 86654995252829881523891 := by
  unfold tailWord_253140
  simp only [CollatzResearch.WordTrace]
  refine ⟨4616387151462243857582437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6155182868616325143443249 4616387151462243857582437)
  ·
    refine ⟨865572590899170723296707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4616387151462243857582437 865572590899170723296707)
    ·
      refine ⟨1298358886348756084945061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 865572590899170723296707 1298358886348756084945061)
      ·
        refine ⟨243442291190391765927199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1298358886348756084945061 243442291190391765927199)
        ·
          refine ⟨365163436785587648890799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243442291190391765927199 365163436785587648890799)
          ·
            refine ⟨547745155178381473336199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365163436785587648890799 547745155178381473336199)
            ·
              refine ⟨821617732767572210004299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 547745155178381473336199 821617732767572210004299)
              ·
                refine ⟨1232426599151358315006449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 821617732767572210004299 1232426599151358315006449)
                ·
                  refine ⟨924319949363518736254837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1232426599151358315006449 924319949363518736254837)
                  ·
                    refine ⟨86654995252829881523891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 924319949363518736254837 86654995252829881523891)
                    ·
                      rfl

theorem cell22_253140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_253140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253140 prefixEnd_253140 := by exact prefixLift 253140
  have htrace : WordTrace (prefixWord ++ tailWord_253140) baseStart_253140 baseEnd_253140 := by
    simpa [prefixWord, tailWord_253140, baseEnd_253140] using wordTrace_append hprefix tailTrace_253140
  have hstable : (prefixWord ++ tailWord_253140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253140).length < 2 ^ (prefixWord ++ tailWord_253140).sum := by decide
  have hdescent : baseEnd_253140 < baseStart_253140 := by decide
  rcases family_descends (prefixWord ++ tailWord_253140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253151 : List Nat := [1, 1, 2, 3, 2, 1, 3, 3, 1, 5]
def baseStart_253151 : Nat := 118140960795 + 253151 * 2 ^ 59
def prefixEnd_253151 : Nat := 4983230072969 + 3 ^ 40 * 253151 * 2
def baseEnd_253151 : Nat := 86658760777629519498857

theorem tailTrace_253151 : CollatzResearch.WordTrace tailWord_253151 prefixEnd_253151 86658760777629519498857 := by
  unfold tailWord_253151
  simp only [CollatzResearch.WordTrace]
  refine ⟨9233175505884636593815307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6155450337256424395876871 9233175505884636593815307)
  ·
    refine ⟨13849763258826954890722961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9233175505884636593815307 13849763258826954890722961)
    ·
      refine ⟨10387322444120216168042221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13849763258826954890722961 10387322444120216168042221)
      ·
        refine ⟨3895245916545081063015833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10387322444120216168042221 3895245916545081063015833)
        ·
          refine ⟨2921434437408810797261875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3895245916545081063015833 2921434437408810797261875)
          ·
            refine ⟨4382151656113216195892813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2921434437408810797261875 4382151656113216195892813)
            ·
              refine ⟨1643306871042456073459805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4382151656113216195892813 1643306871042456073459805)
              ·
                refine ⟨616240076640921027547427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1643306871042456073459805 616240076640921027547427)
                ·
                  refine ⟨924360114961381541321141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 616240076640921027547427 924360114961381541321141)
                  ·
                    refine ⟨86658760777629519498857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 924360114961381541321141 86658760777629519498857)
                    ·
                      rfl

theorem cell22_253151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 1, 3, 3, 1, 5].length) (baseStart_253151 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253151 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253151 prefixEnd_253151 := by exact prefixLift 253151
  have htrace : WordTrace (prefixWord ++ tailWord_253151) baseStart_253151 baseEnd_253151 := by
    simpa [prefixWord, tailWord_253151, baseEnd_253151] using wordTrace_append hprefix tailTrace_253151
  have hstable : (prefixWord ++ tailWord_253151).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253151).length < 2 ^ (prefixWord ++ tailWord_253151).sum := by decide
  have hdescent : baseEnd_253151 < baseStart_253151 := by decide
  rcases family_descends (prefixWord ++ tailWord_253151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253185 : List Nat := [1, 2, 4, 1, 1, 3, 3, 2, 2, 3]
def baseStart_253185 : Nat := 118140960795 + 253185 * 2 ^ 59
def prefixEnd_253185 : Nat := 4983230072969 + 3 ^ 40 * 253185 * 2
def baseEnd_253185 : Nat := 86670399672464764148753

theorem tailTrace_253185 : CollatzResearch.WordTrace tailWord_253185 prefixEnd_253185 86670399672464764148753 := by
  unfold tailWord_253185
  simp only [CollatzResearch.WordTrace]
  refine ⟨9234415587761460400553009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6156277058507640267035339 9234415587761460400553009)
  ·
    refine ⟨6925811690821095300414757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9234415587761460400553009 6925811690821095300414757)
    ·
      refine ⟨1298589692028955368827767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6925811690821095300414757 1298589692028955368827767)
      ·
        refine ⟨1947884538043433053241651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1298589692028955368827767 1947884538043433053241651)
        ·
          refine ⟨2921826807065149579862477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1947884538043433053241651 2921826807065149579862477)
          ·
            refine ⟨1095685052649431092448429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2921826807065149579862477 1095685052649431092448429)
            ·
              refine ⟨410881894743536659668161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1095685052649431092448429 410881894743536659668161)
              ·
                refine ⟨308161421057652494751121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 410881894743536659668161 308161421057652494751121)
                ·
                  refine ⟨231121065793239371063341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308161421057652494751121 231121065793239371063341)
                  ·
                    refine ⟨86670399672464764148753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 231121065793239371063341 86670399672464764148753)
                    ·
                      rfl

theorem cell22_253185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 3, 3, 2, 2, 3].length) (baseStart_253185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253185 prefixEnd_253185 := by exact prefixLift 253185
  have htrace : WordTrace (prefixWord ++ tailWord_253185) baseStart_253185 baseEnd_253185 := by
    simpa [prefixWord, tailWord_253185, baseEnd_253185] using wordTrace_append hprefix tailTrace_253185
  have hstable : (prefixWord ++ tailWord_253185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253185).length < 2 ^ (prefixWord ++ tailWord_253185).sum := by decide
  have hdescent : baseEnd_253185 < baseStart_253185 := by decide
  rcases family_descends (prefixWord ++ tailWord_253185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253215 : List Nat := [1, 1, 2, 4, 4, 2, 2, 6]
def baseStart_253215 : Nat := 118140960795 + 253215 * 2 ^ 59
def prefixEnd_253215 : Nat := 4983230072969 + 3 ^ 40 * 253215 * 2
def baseEnd_253215 : Nat := 9631185476172742877629

theorem tailTrace_253215 : CollatzResearch.WordTrace tailWord_253215 prefixEnd_253215 9631185476172742877629 := by
  unfold tailWord_253215
  simp only [CollatzResearch.WordTrace]
  refine ⟨9235509777652775524145099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6157006518435183682763399 9235509777652775524145099)
  ·
    refine ⟨13853264666479163286217649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9235509777652775524145099 13853264666479163286217649)
    ·
      refine ⟨10389948499859372464663237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13853264666479163286217649 10389948499859372464663237)
      ·
        refine ⟨1948115343723632337124357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10389948499859372464663237 1948115343723632337124357)
        ·
          refine ⟨365271626948181063210817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1948115343723632337124357 365271626948181063210817)
          ·
            refine ⟨273953720211135797408113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 365271626948181063210817 273953720211135797408113)
            ·
              refine ⟨205465290158351848056085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 273953720211135797408113 205465290158351848056085)
              ·
                refine ⟨9631185476172742877629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 205465290158351848056085 9631185476172742877629)
                ·
                  rfl

theorem cell22_253215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 2, 2, 6].length) (baseStart_253215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253215 prefixEnd_253215 := by exact prefixLift 253215
  have htrace : WordTrace (prefixWord ++ tailWord_253215) baseStart_253215 baseEnd_253215 := by
    simpa [prefixWord, tailWord_253215, baseEnd_253215] using wordTrace_append hprefix tailTrace_253215
  have hstable : (prefixWord ++ tailWord_253215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253215).length < 2 ^ (prefixWord ++ tailWord_253215).sum := by decide
  have hdescent : baseEnd_253215 < baseStart_253215 := by decide
  rcases family_descends (prefixWord ++ tailWord_253215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253256 : List Nat := [2, 1, 3, 1, 1, 2, 1, 1, 2, 8]
def baseStart_253256 : Nat := 118140960795 + 253256 * 2 ^ 59
def prefixEnd_253256 : Nat := 4983230072969 + 3 ^ 40 * 253256 * 2
def baseEnd_253256 : Nat := 86694704423444245623535

theorem tailTrace_253256 : CollatzResearch.WordTrace tailWord_253256 prefixEnd_253256 86694704423444245623535 := by
  unfold tailWord_253256
  simp only [CollatzResearch.WordTrace]
  refine ⟨4618502585252119763193811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6158003447002826350925081 4618502585252119763193811)
  ·
    refine ⟨6927753877878179644790717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4618502585252119763193811 6927753877878179644790717)
    ·
      refine ⟨2597907704204317366796519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6927753877878179644790717 2597907704204317366796519)
      ·
        refine ⟨3896861556306476050194779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2597907704204317366796519 3896861556306476050194779)
        ·
          refine ⟨5845292334459714075292169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3896861556306476050194779 5845292334459714075292169)
          ·
            refine ⟨4383969250844785556469127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5845292334459714075292169 4383969250844785556469127)
            ·
              refine ⟨6575953876267178334703691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4383969250844785556469127 6575953876267178334703691)
              ·
                refine ⟨9863930814400767502055537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6575953876267178334703691 9863930814400767502055537)
                ·
                  refine ⟨7397948110800575626541653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 9863930814400767502055537 7397948110800575626541653)
                  ·
                    refine ⟨86694704423444245623535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7397948110800575626541653 86694704423444245623535)
                    ·
                      rfl

theorem cell22_253256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 1, 1, 2, 8].length) (baseStart_253256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253256 prefixEnd_253256 := by exact prefixLift 253256
  have htrace : WordTrace (prefixWord ++ tailWord_253256) baseStart_253256 baseEnd_253256 := by
    simpa [prefixWord, tailWord_253256, baseEnd_253256] using wordTrace_append hprefix tailTrace_253256
  have hstable : (prefixWord ++ tailWord_253256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253256).length < 2 ^ (prefixWord ++ tailWord_253256).sum := by decide
  have hdescent : baseEnd_253256 < baseStart_253256 := by decide
  rcases family_descends (prefixWord ++ tailWord_253256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253260 : List Nat := [2, 2, 1, 3, 2, 2, 4, 1, 5]
def baseStart_253260 : Nat := 118140960795 + 253260 * 2 ^ 59
def prefixEnd_253260 : Nat := 4983230072969 + 3 ^ 40 * 253260 * 2
def baseEnd_253260 : Nat := 28898691235063189507841

theorem tailTrace_253260 : CollatzResearch.WordTrace tailWord_253260 prefixEnd_253260 28898691235063189507841 := by
  unfold tailWord_253260
  simp only [CollatzResearch.WordTrace]
  refine ⟨4618575531244874104766617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6158100708326498806355489 4618575531244874104766617)
  ·
    refine ⟨3463931648433655578574963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4618575531244874104766617 3463931648433655578574963)
    ·
      refine ⟨5195897472650483367862445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3463931648433655578574963 5195897472650483367862445)
      ·
        refine ⟨1948461552243931262948417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5195897472650483367862445 1948461552243931262948417)
        ·
          refine ⟨1461346164182948447211313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1948461552243931262948417 1461346164182948447211313)
          ·
            refine ⟨1096009623137211335408485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1461346164182948447211313 1096009623137211335408485)
            ·
              refine ⟨205501804338227125389091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1096009623137211335408485 205501804338227125389091)
              ·
                refine ⟨308252706507340688083637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205501804338227125389091 308252706507340688083637)
                ·
                  refine ⟨28898691235063189507841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 308252706507340688083637 28898691235063189507841)
                  ·
                    rfl

theorem cell22_253260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 4, 1, 5].length) (baseStart_253260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253260 prefixEnd_253260 := by exact prefixLift 253260
  have htrace : WordTrace (prefixWord ++ tailWord_253260) baseStart_253260 baseEnd_253260 := by
    simpa [prefixWord, tailWord_253260, baseEnd_253260] using wordTrace_append hprefix tailTrace_253260
  have hstable : (prefixWord ++ tailWord_253260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253260).length < 2 ^ (prefixWord ++ tailWord_253260).sum := by decide
  have hdescent : baseEnd_253260 < baseStart_253260 := by decide
  rcases family_descends (prefixWord ++ tailWord_253260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253320 : List Nat := [2, 1, 3, 3, 1, 3, 2, 1, 1, 5]
def baseStart_253320 : Nat := 118140960795 + 253320 * 2 ^ 59
def prefixEnd_253320 : Nat := 4983230072969 + 3 ^ 40 * 253320 * 2
def baseEnd_253320 : Nat := 86716612931369412023339

theorem tailTrace_253320 : CollatzResearch.WordTrace tailWord_253320 prefixEnd_253320 86716612931369412023339 := by
  unfold tailWord_253320
  simp only [CollatzResearch.WordTrace]
  refine ⟨4619669721136189228358707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6159559628181585637811609 4619669721136189228358707)
  ·
    refine ⟨6929504581704283842538061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4619669721136189228358707 6929504581704283842538061)
    ·
      refine ⟨2598564218139106440951773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6929504581704283842538061 2598564218139106440951773)
      ·
        refine ⟨974461581802164915356915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2598564218139106440951773 974461581802164915356915)
        ·
          refine ⟨1461692372703247373035373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 974461581802164915356915 1461692372703247373035373)
          ·
            refine ⟨548134639763717764888265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1461692372703247373035373 548134639763717764888265)
            ·
              refine ⟨411100979822788323666199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 548134639763717764888265 411100979822788323666199)
              ·
                refine ⟨616651469734182485499299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411100979822788323666199 616651469734182485499299)
                ·
                  refine ⟨924977204601273728248949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 616651469734182485499299 924977204601273728248949)
                  ·
                    refine ⟨86716612931369412023339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 924977204601273728248949 86716612931369412023339)
                    ·
                      rfl

theorem cell22_253320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 1, 1, 5].length) (baseStart_253320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253320 prefixEnd_253320 := by exact prefixLift 253320
  have htrace : WordTrace (prefixWord ++ tailWord_253320) baseStart_253320 baseEnd_253320 := by
    simpa [prefixWord, tailWord_253320, baseEnd_253320] using wordTrace_append hprefix tailTrace_253320
  have hstable : (prefixWord ++ tailWord_253320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253320).length < 2 ^ (prefixWord ++ tailWord_253320).sum := by decide
  have hdescent : baseEnd_253320 < baseStart_253320 := by decide
  rcases family_descends (prefixWord ++ tailWord_253320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253429 : List Nat := [1, 3, 5, 1, 1, 1, 4, 1, 5]
def baseStart_253429 : Nat := 118140960795 + 253429 * 2 ^ 59
def prefixEnd_253429 : Nat := 4983230072969 + 3 ^ 40 * 253429 * 2
def baseEnd_253429 : Nat := 28917975286309820349335

theorem tailTrace_253429 : CollatzResearch.WordTrace tailWord_253429 prefixEnd_253429 28917975286309820349335 := by
  unfold tailWord_253429
  simp only [CollatzResearch.WordTrace]
  refine ⟨9243314998877490072435341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6162209999251660048290227 9243314998877490072435341)
  ·
    refine ⟨3466243124579058777163253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9243314998877490072435341 3466243124579058777163253)
    ·
      refine ⟨324960292929286760359055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3466243124579058777163253 324960292929286760359055)
      ·
        refine ⟨487440439393930140538583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 324960292929286760359055 487440439393930140538583)
        ·
          refine ⟨731160659090895210807875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 487440439393930140538583 731160659090895210807875)
          ·
            refine ⟨1096740988636342816211813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 731160659090895210807875 1096740988636342816211813)
            ·
              refine ⟨205638935369314278039715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1096740988636342816211813 205638935369314278039715)
              ·
                refine ⟨308458403053971417059573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205638935369314278039715 308458403053971417059573)
                ·
                  refine ⟨28917975286309820349335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 308458403053971417059573 28917975286309820349335)
                  ·
                    rfl

theorem cell22_253429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 4, 1, 5].length) (baseStart_253429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253429 prefixEnd_253429 := by exact prefixLift 253429
  have htrace : WordTrace (prefixWord ++ tailWord_253429) baseStart_253429 baseEnd_253429 := by
    simpa [prefixWord, tailWord_253429, baseEnd_253429] using wordTrace_append hprefix tailTrace_253429
  have hstable : (prefixWord ++ tailWord_253429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253429).length < 2 ^ (prefixWord ++ tailWord_253429).sum := by decide
  have hdescent : baseEnd_253429 < baseStart_253429 := by decide
  rcases family_descends (prefixWord ++ tailWord_253429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253474 : List Nat := [3, 3, 1, 1, 1, 1, 6, 2, 4]
def baseStart_253474 : Nat := 118140960795 + 253474 * 2 ^ 59
def prefixEnd_253474 : Nat := 4983230072969 + 3 ^ 40 * 253474 * 2
def baseEnd_253474 : Nat := 28923110092854781224289

theorem tailTrace_253474 : CollatzResearch.WordTrace tailWord_253474 prefixEnd_253474 28923110092854781224289 := by
  unfold tailWord_253474
  simp only [CollatzResearch.WordTrace]
  refine ⟨2311239070928615689455869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6163304189142975171882317 2311239070928615689455869)
  ·
    refine ⟨866714651598230883545951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2311239070928615689455869 866714651598230883545951)
    ·
      refine ⟨1300071977397346325318927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 866714651598230883545951 1300071977397346325318927)
      ·
        refine ⟨1950107966096019487978391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1300071977397346325318927 1950107966096019487978391)
        ·
          refine ⟨2925161949144029231967587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1950107966096019487978391 2925161949144029231967587)
          ·
            refine ⟨4387742923716043847951381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2925161949144029231967587 4387742923716043847951381)
            ·
              refine ⟨205675449549189555372721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 4387742923716043847951381 205675449549189555372721)
              ·
                refine ⟨154256587161892166529541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 205675449549189555372721 154256587161892166529541)
                ·
                  refine ⟨28923110092854781224289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154256587161892166529541 28923110092854781224289)
                  ·
                    rfl

theorem cell22_253474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 6, 2, 4].length) (baseStart_253474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253474 prefixEnd_253474 := by exact prefixLift 253474
  have htrace : WordTrace (prefixWord ++ tailWord_253474) baseStart_253474 baseEnd_253474 := by
    simpa [prefixWord, tailWord_253474, baseEnd_253474] using wordTrace_append hprefix tailTrace_253474
  have hstable : (prefixWord ++ tailWord_253474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253474).length < 2 ^ (prefixWord ++ tailWord_253474).sum := by decide
  have hdescent : baseEnd_253474 < baseStart_253474 := by decide
  rcases family_descends (prefixWord ++ tailWord_253474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253483 : List Nat := [1, 1, 1, 1, 2, 1, 3, 1, 4, 7]
def baseStart_253483 : Nat := 118140960795 + 253483 * 2 ^ 59
def prefixEnd_253483 : Nat := 4983230072969 + 3 ^ 40 * 253483 * 2
def baseEnd_253483 : Nat := 86772411162491320197839

theorem tailTrace_253483 : CollatzResearch.WordTrace tailWord_253483 prefixEnd_253483 86772411162491320197839 := by
  unfold tailWord_253483
  simp only [CollatzResearch.WordTrace]
  refine ⟨9245284540681857294901103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6163523027121238196600735 9245284540681857294901103)
  ·
    refine ⟨13867926811022785942351655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9245284540681857294901103 13867926811022785942351655)
    ·
      refine ⟨20801890216534178913527483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13867926811022785942351655 20801890216534178913527483)
      ·
        refine ⟨31202835324801268370291225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 20801890216534178913527483 31202835324801268370291225)
        ·
          refine ⟨23402126493600951277718419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31202835324801268370291225 23402126493600951277718419)
          ·
            refine ⟨35103189740401426916577629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23402126493600951277718419 35103189740401426916577629)
            ·
              refine ⟨13163696152650535093716611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 35103189740401426916577629 13163696152650535093716611)
              ·
                refine ⟨19745544228975802640574917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13163696152650535093716611 19745544228975802640574917)
                ·
                  refine ⟨3702289542932962995107797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19745544228975802640574917 3702289542932962995107797)
                  ·
                    refine ⟨86772411162491320197839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3702289542932962995107797 86772411162491320197839)
                    ·
                      rfl

theorem cell22_253483_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 4, 7].length) (baseStart_253483 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253483 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253483 prefixEnd_253483 := by exact prefixLift 253483
  have htrace : WordTrace (prefixWord ++ tailWord_253483) baseStart_253483 baseEnd_253483 := by
    simpa [prefixWord, tailWord_253483, baseEnd_253483] using wordTrace_append hprefix tailTrace_253483
  have hstable : (prefixWord ++ tailWord_253483).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253483).length < 2 ^ (prefixWord ++ tailWord_253483).sum := by decide
  have hdescent : baseEnd_253483 < baseStart_253483 := by decide
  rcases family_descends (prefixWord ++ tailWord_253483) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253510 : List Nat := [6, 1, 1, 1, 4, 1, 2, 1, 1, 4]
def baseStart_253510 : Nat := 118140960795 + 253510 * 2 ^ 59
def prefixEnd_253510 : Nat := 4983230072969 + 3 ^ 40 * 253510 * 2
def baseEnd_253510 : Nat := 86781653814272249772757

theorem tailTrace_253510 : CollatzResearch.WordTrace tailWord_253510 prefixEnd_253510 86781653814272249772757 := by
  unfold tailWord_253510
  simp only [CollatzResearch.WordTrace]
  refine ⟨288945915987001278316687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6164179541056027270755989 288945915987001278316687)
  ·
    refine ⟨433418873980501917475031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 288945915987001278316687 433418873980501917475031)
    ·
      refine ⟨650128310970752876212547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 433418873980501917475031 650128310970752876212547)
      ·
        refine ⟨975192466456129314318821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 650128310970752876212547 975192466456129314318821)
        ·
          refine ⟨182848587460524246434779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 975192466456129314318821 182848587460524246434779)
          ·
            refine ⟨274272881190786369652169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 182848587460524246434779 274272881190786369652169)
            ·
              refine ⟨205704660893089777239127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274272881190786369652169 205704660893089777239127)
              ·
                refine ⟨308556991339634665858691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205704660893089777239127 308556991339634665858691)
                ·
                  refine ⟨462835487009451998788037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308556991339634665858691 462835487009451998788037)
                  ·
                    refine ⟨86781653814272249772757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 462835487009451998788037 86781653814272249772757)
                    ·
                      rfl

theorem cell22_253510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 4, 1, 2, 1, 1, 4].length) (baseStart_253510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253510 prefixEnd_253510 := by exact prefixLift 253510
  have htrace : WordTrace (prefixWord ++ tailWord_253510) baseStart_253510 baseEnd_253510 := by
    simpa [prefixWord, tailWord_253510, baseEnd_253510] using wordTrace_append hprefix tailTrace_253510
  have hstable : (prefixWord ++ tailWord_253510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253510).length < 2 ^ (prefixWord ++ tailWord_253510).sum := by decide
  have hdescent : baseEnd_253510 < baseStart_253510 := by decide
  rcases family_descends (prefixWord ++ tailWord_253510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253545 : List Nat := [1, 2, 1, 1, 1, 4, 4, 1, 2, 5]
def baseStart_253545 : Nat := 118140960795 + 253545 * 2 ^ 59
def prefixEnd_253545 : Nat := 4983230072969 + 3 ^ 40 * 253545 * 2
def baseEnd_253545 : Nat := 86793635029543825147649

theorem tailTrace_253545 : CollatzResearch.WordTrace tailWord_253545 prefixEnd_253545 86793635029543825147649 := by
  unfold tailWord_253545
  simp only [CollatzResearch.WordTrace]
  refine ⟨9247545866457241883658089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6165030577638161255772059 9247545866457241883658089)
  ·
    refine ⟨6935659399842931412743567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9247545866457241883658089 6935659399842931412743567)
    ·
      refine ⟨10403489099764397119115351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6935659399842931412743567 10403489099764397119115351)
      ·
        refine ⟨15605233649646595678673027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10403489099764397119115351 15605233649646595678673027)
        ·
          refine ⟨23407850474469893518009541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15605233649646595678673027 23407850474469893518009541)
          ·
            refine ⟨4388971963963105034626789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 23407850474469893518009541 4388971963963105034626789)
            ·
              refine ⟨822932243243082193992523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4388971963963105034626789 822932243243082193992523)
              ·
                refine ⟨1234398364864623290988785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 822932243243082193992523 1234398364864623290988785)
                ·
                  refine ⟨925798773648467468241589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1234398364864623290988785 925798773648467468241589)
                  ·
                    refine ⟨86793635029543825147649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 925798773648467468241589 86793635029543825147649)
                    ·
                      rfl

theorem cell22_253545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 4, 1, 2, 5].length) (baseStart_253545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253545 prefixEnd_253545 := by exact prefixLift 253545
  have htrace : WordTrace (prefixWord ++ tailWord_253545) baseStart_253545 baseEnd_253545 := by
    simpa [prefixWord, tailWord_253545, baseEnd_253545] using wordTrace_append hprefix tailTrace_253545
  have hstable : (prefixWord ++ tailWord_253545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253545).length < 2 ^ (prefixWord ++ tailWord_253545).sum := by decide
  have hdescent : baseEnd_253545 < baseStart_253545 := by decide
  rcases family_descends (prefixWord ++ tailWord_253545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253577 : List Nat := [1, 2, 1, 1, 4, 1, 4, 3, 1, 4]
def baseStart_253577 : Nat := 118140960795 + 253577 * 2 ^ 59
def prefixEnd_253577 : Nat := 4983230072969 + 3 ^ 40 * 253577 * 2
def baseEnd_253577 : Nat := 86804589283506408347551

theorem tailTrace_253577 : CollatzResearch.WordTrace tailWord_253577 prefixEnd_253577 86804589283506408347551 := by
  unfold tailWord_253577
  simp only [CollatzResearch.WordTrace]
  refine ⟨9248713002341311348822985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6165808668227540899215323 9248713002341311348822985)
  ·
    refine ⟨6936534751755983511617239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9248713002341311348822985 6936534751755983511617239)
    ·
      refine ⟨10404802127633975267425859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6936534751755983511617239 10404802127633975267425859)
      ·
        refine ⟨15607203191450962901138789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10404802127633975267425859 15607203191450962901138789)
        ·
          refine ⟨2926350598397055543963523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15607203191450962901138789 2926350598397055543963523)
          ·
            refine ⟨4389525897595583315945285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2926350598397055543963523 4389525897595583315945285)
            ·
              refine ⟨823036105799171871739741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4389525897595583315945285 823036105799171871739741)
              ·
                refine ⟨308638539674689451902403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 823036105799171871739741 308638539674689451902403)
                ·
                  refine ⟨462957809512034177853605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308638539674689451902403 462957809512034177853605)
                  ·
                    refine ⟨86804589283506408347551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 462957809512034177853605 86804589283506408347551)
                    ·
                      rfl

theorem cell22_253577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 4, 3, 1, 4].length) (baseStart_253577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253577 prefixEnd_253577 := by exact prefixLift 253577
  have htrace : WordTrace (prefixWord ++ tailWord_253577) baseStart_253577 baseEnd_253577 := by
    simpa [prefixWord, tailWord_253577, baseEnd_253577] using wordTrace_append hprefix tailTrace_253577
  have hstable : (prefixWord ++ tailWord_253577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253577).length < 2 ^ (prefixWord ++ tailWord_253577).sum := by decide
  have hdescent : baseEnd_253577 < baseStart_253577 := by decide
  rcases family_descends (prefixWord ++ tailWord_253577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253592 : List Nat := [2, 1, 2, 4, 1, 2, 3, 1, 6]
def baseStart_253592 : Nat := 118140960795 + 253592 * 2 ^ 59
def prefixEnd_253592 : Nat := 4983230072969 + 3 ^ 40 * 253592 * 2
def baseEnd_253592 : Nat := 28936574696683789740835

theorem tailTrace_253592 : CollatzResearch.WordTrace tailWord_253592 prefixEnd_253592 28936574696683789740835 := by
  unfold tailWord_253592
  simp only [CollatzResearch.WordTrace]
  refine ⟨4624630048643484455309515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6166173398191312607079353 4624630048643484455309515)
  ·
    refine ⟨6936945072965226682964273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4624630048643484455309515 6936945072965226682964273)
    ·
      refine ⟨5202708804723920012223205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6936945072965226682964273 5202708804723920012223205)
      ·
        refine ⟨975507900885735002291851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5202708804723920012223205 975507900885735002291851)
        ·
          refine ⟨1463261851328602503437777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 975507900885735002291851 1463261851328602503437777)
          ·
            refine ⟨1097446388496451877578333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1463261851328602503437777 1097446388496451877578333)
            ·
              refine ⟨411542395686169454091875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1097446388496451877578333 411542395686169454091875)
              ·
                refine ⟨617313593529254181137813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 411542395686169454091875 617313593529254181137813)
                ·
                  refine ⟨28936574696683789740835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 617313593529254181137813 28936574696683789740835)
                  ·
                    rfl

theorem cell22_253592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 2, 3, 1, 6].length) (baseStart_253592 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253592 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253592 prefixEnd_253592 := by exact prefixLift 253592
  have htrace : WordTrace (prefixWord ++ tailWord_253592) baseStart_253592 baseEnd_253592 := by
    simpa [prefixWord, tailWord_253592, baseEnd_253592] using wordTrace_append hprefix tailTrace_253592
  have hstable : (prefixWord ++ tailWord_253592).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253592).length < 2 ^ (prefixWord ++ tailWord_253592).sum := by decide
  have hdescent : baseEnd_253592 < baseStart_253592 := by decide
  rcases family_descends (prefixWord ++ tailWord_253592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253605 : List Nat := [1, 3, 1, 2, 1, 2, 2, 1, 3, 6]
def baseStart_253605 : Nat := 118140960795 + 253605 * 2 ^ 59
def prefixEnd_253605 : Nat := 4983230072969 + 3 ^ 40 * 253605 * 2
def baseEnd_253605 : Nat := 86814174255723668647465

theorem tailTrace_253605 : CollatzResearch.WordTrace tailWord_253605 prefixEnd_253605 86814174255723668647465 := by
  unfold tailWord_253605
  simp only [CollatzResearch.WordTrace]
  refine ⟨9249734246239872130842269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6166489497493248087228179 9249734246239872130842269)
  ·
    refine ⟨3468650342339952049065851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9249734246239872130842269 3468650342339952049065851)
    ·
      refine ⟨5202975513509928073598777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3468650342339952049065851 5202975513509928073598777)
      ·
        refine ⟨3902231635132446055199083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5202975513509928073598777 3902231635132446055199083)
        ·
          refine ⟨5853347452698669082798625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3902231635132446055199083 5853347452698669082798625)
          ·
            refine ⟨4390010589524001812098969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5853347452698669082798625 4390010589524001812098969)
            ·
              refine ⟨3292507942143001359074227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4390010589524001812098969 3292507942143001359074227)
              ·
                refine ⟨4938761913214502038611341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3292507942143001359074227 4938761913214502038611341)
                ·
                  refine ⟨1852035717455438264479253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4938761913214502038611341 1852035717455438264479253)
                  ·
                    refine ⟨86814174255723668647465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1852035717455438264479253 86814174255723668647465)
                    ·
                      rfl

theorem cell22_253605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 1, 3, 6].length) (baseStart_253605 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253605 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253605 prefixEnd_253605 := by exact prefixLift 253605
  have htrace : WordTrace (prefixWord ++ tailWord_253605) baseStart_253605 baseEnd_253605 := by
    simpa [prefixWord, tailWord_253605, baseEnd_253605] using wordTrace_append hprefix tailTrace_253605
  have hstable : (prefixWord ++ tailWord_253605).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253605).length < 2 ^ (prefixWord ++ tailWord_253605).sum := by decide
  have hdescent : baseEnd_253605 < baseStart_253605 := by decide
  rcases family_descends (prefixWord ++ tailWord_253605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253669 : List Nat := [1, 3, 1, 4, 1, 1, 3, 2, 3, 3]
def baseStart_253669 : Nat := 118140960795 + 253669 * 2 ^ 59
def prefixEnd_253669 : Nat := 4983230072969 + 3 ^ 40 * 253669 * 2
def baseEnd_253669 : Nat := 86836082763648835047269

theorem tailTrace_253669 : CollatzResearch.WordTrace tailWord_253669 prefixEnd_253669 86836082763648835047269 := by
  unfold tailWord_253669
  simp only [CollatzResearch.WordTrace]
  refine ⟨9252068518008011061172061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6168045678672007374114707 9252068518008011061172061)
  ·
    refine ⟨3469525694253004147939523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9252068518008011061172061 3469525694253004147939523)
    ·
      refine ⟨5204288541379506221909285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3469525694253004147939523 5204288541379506221909285)
      ·
        refine ⟨975804101508657416607991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5204288541379506221909285 975804101508657416607991)
        ·
          refine ⟨1463706152262986124911987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 975804101508657416607991 1463706152262986124911987)
          ·
            refine ⟨2195559228394479187367981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1463706152262986124911987 2195559228394479187367981)
            ·
              refine ⟨823334710647929695262993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2195559228394479187367981 823334710647929695262993)
              ·
                refine ⟨617501032985947271447245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 823334710647929695262993 617501032985947271447245)
                ·
                  refine ⟨231562887369730226792717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 617501032985947271447245 231562887369730226792717)
                  ·
                    refine ⟨86836082763648835047269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 231562887369730226792717 86836082763648835047269)
                    ·
                      rfl

theorem cell22_253669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 3, 2, 3, 3].length) (baseStart_253669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253669 prefixEnd_253669 := by exact prefixLift 253669
  have htrace : WordTrace (prefixWord ++ tailWord_253669) baseStart_253669 baseEnd_253669 := by
    simpa [prefixWord, tailWord_253669, baseEnd_253669] using wordTrace_append hprefix tailTrace_253669
  have hstable : (prefixWord ++ tailWord_253669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253669).length < 2 ^ (prefixWord ++ tailWord_253669).sum := by decide
  have hdescent : baseEnd_253669 < baseStart_253669 := by decide
  rcases family_descends (prefixWord ++ tailWord_253669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253671 : List Nat := [1, 1, 5, 4, 1, 1, 3, 6]
def baseStart_253671 : Nat := 118140960795 + 253671 * 2 ^ 59
def prefixEnd_253671 : Nat := 4983230072969 + 3 ^ 40 * 253671 * 2
def baseEnd_253671 : Nat := 9648529711613499610807

theorem tailTrace_253671 : CollatzResearch.WordTrace tailWord_253671 prefixEnd_253671 9648529711613499610807 := by
  unfold tailWord_253671
  simp only [CollatzResearch.WordTrace]
  refine ⟨9252141464000765402744867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6168094309333843601829911 9252141464000765402744867)
  ·
    refine ⟨13878212196001148104117301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9252141464000765402744867 13878212196001148104117301)
    ·
      refine ⟨1301082393375107634760997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13878212196001148104117301 1301082393375107634760997)
      ·
        refine ⟨243952948757832681517687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1301082393375107634760997 243952948757832681517687)
        ·
          refine ⟨365929423136749022276531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243952948757832681517687 365929423136749022276531)
          ·
            refine ⟨548894134705123533414797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365929423136749022276531 548894134705123533414797)
            ·
              refine ⟨205835300514421325030549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 548894134705123533414797 205835300514421325030549)
              ·
                refine ⟨9648529711613499610807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 205835300514421325030549 9648529711613499610807)
                ·
                  rfl

theorem cell22_253671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 3, 6].length) (baseStart_253671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253671 prefixEnd_253671 := by exact prefixLift 253671
  have htrace : WordTrace (prefixWord ++ tailWord_253671) baseStart_253671 baseEnd_253671 := by
    simpa [prefixWord, tailWord_253671, baseEnd_253671] using wordTrace_append hprefix tailTrace_253671
  have hstable : (prefixWord ++ tailWord_253671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253671).length < 2 ^ (prefixWord ++ tailWord_253671).sum := by decide
  have hdescent : baseEnd_253671 < baseStart_253671 := by decide
  rcases family_descends (prefixWord ++ tailWord_253671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253682 : List Nat := [3, 2, 1, 3, 1, 1, 2, 2, 7]
def baseStart_253682 : Nat := 118140960795 + 253682 * 2 ^ 59
def prefixEnd_253682 : Nat := 4983230072969 + 3 ^ 40 * 253682 * 2
def baseEnd_253682 : Nat := 28946844309773711490743

theorem tailTrace_253682 : CollatzResearch.WordTrace tailWord_253682 prefixEnd_253682 28946844309773711490743 := by
  unfold tailWord_253682
  simp only [CollatzResearch.WordTrace]
  refine ⟨2313135666740228570348825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6168361777973942854263533 2313135666740228570348825)
  ·
    refine ⟨1734851750055171427761619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2313135666740228570348825 1734851750055171427761619)
    ·
      refine ⟨2602277625082757141642429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1734851750055171427761619 2602277625082757141642429)
      ·
        refine ⟨975854109406033928115911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2602277625082757141642429 975854109406033928115911)
        ·
          refine ⟨1463781164109050892173867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 975854109406033928115911 1463781164109050892173867)
          ·
            refine ⟨2195671746163576338260801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1463781164109050892173867 2195671746163576338260801)
            ·
              refine ⟨1646753809622682253695601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2195671746163576338260801 1646753809622682253695601)
              ·
                refine ⟨1235065357217011690271701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1646753809622682253695601 1235065357217011690271701)
                ·
                  refine ⟨28946844309773711490743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1235065357217011690271701 28946844309773711490743)
                  ·
                    rfl

theorem cell22_253682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 2, 7].length) (baseStart_253682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253682 prefixEnd_253682 := by exact prefixLift 253682
  have htrace : WordTrace (prefixWord ++ tailWord_253682) baseStart_253682 baseEnd_253682 := by
    simpa [prefixWord, tailWord_253682, baseEnd_253682] using wordTrace_append hprefix tailTrace_253682
  have hstable : (prefixWord ++ tailWord_253682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253682).length < 2 ^ (prefixWord ++ tailWord_253682).sum := by decide
  have hdescent : baseEnd_253682 < baseStart_253682 := by decide
  rcases family_descends (prefixWord ++ tailWord_253682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253697 : List Nat := [1, 2, 4, 1, 1, 1, 3, 2, 2, 5]
def baseStart_253697 : Nat := 118140960795 + 253697 * 2 ^ 59
def prefixEnd_253697 : Nat := 4983230072969 + 3 ^ 40 * 253697 * 2
def baseEnd_253697 : Nat := 86845667735866095347183

theorem tailTrace_253697 : CollatzResearch.WordTrace tailWord_253697 prefixEnd_253697 86845667735866095347183 := by
  unfold tailWord_253697
  simp only [CollatzResearch.WordTrace]
  refine ⟨9253089761906571843191345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6168726507937714562127563 9253089761906571843191345)
  ·
    refine ⟨6939817321429928882393509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9253089761906571843191345 6939817321429928882393509)
    ·
      refine ⟨1301215747768111665448783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6939817321429928882393509 1301215747768111665448783)
      ·
        refine ⟨1951823621652167498173175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1301215747768111665448783 1951823621652167498173175)
        ·
          refine ⟨2927735432478251247259763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1951823621652167498173175 2927735432478251247259763)
          ·
            refine ⟨4391603148717376870889645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2927735432478251247259763 4391603148717376870889645)
            ·
              refine ⟨1646851180769016326583617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4391603148717376870889645 1646851180769016326583617)
              ·
                refine ⟨1235138385576762244937713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1646851180769016326583617 1235138385576762244937713)
                ·
                  refine ⟨926353789182571683703285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1235138385576762244937713 926353789182571683703285)
                  ·
                    refine ⟨86845667735866095347183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 926353789182571683703285 86845667735866095347183)
                    ·
                      rfl

theorem cell22_253697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_253697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253697 prefixEnd_253697 := by exact prefixLift 253697
  have htrace : WordTrace (prefixWord ++ tailWord_253697) baseStart_253697 baseEnd_253697 := by
    simpa [prefixWord, tailWord_253697, baseEnd_253697] using wordTrace_append hprefix tailTrace_253697
  have hstable : (prefixWord ++ tailWord_253697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253697).length < 2 ^ (prefixWord ++ tailWord_253697).sum := by decide
  have hdescent : baseEnd_253697 < baseStart_253697 := by decide
  rcases family_descends (prefixWord ++ tailWord_253697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253709 : List Nat := [1, 7, 2, 1, 1, 1, 3, 1, 2, 3]
def baseStart_253709 : Nat := 118140960795 + 253709 * 2 ^ 59
def prefixEnd_253709 : Nat := 4983230072969 + 3 ^ 40 * 253709 * 2
def baseEnd_253709 : Nat := 86849775581102064047147

theorem tailTrace_253709 : CollatzResearch.WordTrace tailWord_253709 prefixEnd_253709 86849775581102064047147 := by
  unfold tailWord_253709
  simp only [CollatzResearch.WordTrace]
  refine ⟨9253527437863097892628181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6169018291908731928418787 9253527437863097892628181)
  ·
    refine ⟨216879549324916356858473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 9253527437863097892628181 216879549324916356858473)
    ·
      refine ⟨162659661993687267643855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 216879549324916356858473 162659661993687267643855)
      ·
        refine ⟨243989492990530901465783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 162659661993687267643855 243989492990530901465783)
        ·
          refine ⟨365984239485796352198675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 243989492990530901465783 365984239485796352198675)
          ·
            refine ⟨548976359228694528298013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 365984239485796352198675 548976359228694528298013)
            ·
              refine ⟨205866134710760448111755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 548976359228694528298013 205866134710760448111755)
              ·
                refine ⟨308799202066140672167633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 205866134710760448111755 308799202066140672167633)
                ·
                  refine ⟨231599401549605504125725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 308799202066140672167633 231599401549605504125725)
                  ·
                    refine ⟨86849775581102064047147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 231599401549605504125725 86849775581102064047147)
                    ·
                      rfl

theorem cell22_253709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_253709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253709 prefixEnd_253709 := by exact prefixLift 253709
  have htrace : WordTrace (prefixWord ++ tailWord_253709) baseStart_253709 baseEnd_253709 := by
    simpa [prefixWord, tailWord_253709, baseEnd_253709] using wordTrace_append hprefix tailTrace_253709
  have hstable : (prefixWord ++ tailWord_253709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253709).length < 2 ^ (prefixWord ++ tailWord_253709).sum := by decide
  have hdescent : baseEnd_253709 < baseStart_253709 := by decide
  rcases family_descends (prefixWord ++ tailWord_253709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253727 : List Nat := [1, 1, 2, 4, 2, 1, 1, 4, 6]
def baseStart_253727 : Nat := 118140960795 + 253727 * 2 ^ 59
def prefixEnd_253727 : Nat := 4983230072969 + 3 ^ 40 * 253727 * 2
def baseEnd_253727 : Nat := 28951979116318672365697

theorem tailTrace_253727 : CollatzResearch.WordTrace tailWord_253727 prefixEnd_253727 28951979116318672365697 := by
  unfold tailWord_253727
  simp only [CollatzResearch.WordTrace]
  refine ⟨9254183951797886966783435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6169455967865257977855623 9254183951797886966783435)
  ·
    refine ⟨13881275927696830450175153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9254183951797886966783435 13881275927696830450175153)
    ·
      refine ⟨10410956945772622837631365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13881275927696830450175153 10410956945772622837631365)
      ·
        refine ⟨1952054427332366782055881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10410956945772622837631365 1952054427332366782055881)
        ·
          refine ⟨1464040820499275086541911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1952054427332366782055881 1464040820499275086541911)
          ·
            refine ⟨2196061230748912629812867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1464040820499275086541911 2196061230748912629812867)
            ·
              refine ⟨3294091846123368944719301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2196061230748912629812867 3294091846123368944719301)
              ·
                refine ⟨617642221148131677134869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3294091846123368944719301 617642221148131677134869)
                ·
                  refine ⟨28951979116318672365697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 617642221148131677134869 28951979116318672365697)
                  ·
                    rfl

theorem cell22_253727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 4, 6].length) (baseStart_253727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253727 prefixEnd_253727 := by exact prefixLift 253727
  have htrace : WordTrace (prefixWord ++ tailWord_253727) baseStart_253727 baseEnd_253727 := by
    simpa [prefixWord, tailWord_253727, baseEnd_253727] using wordTrace_append hprefix tailTrace_253727
  have hstable : (prefixWord ++ tailWord_253727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253727).length < 2 ^ (prefixWord ++ tailWord_253727).sum := by decide
  have hdescent : baseEnd_253727 < baseStart_253727 := by decide
  rcases family_descends (prefixWord ++ tailWord_253727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253729 : List Nat := [1, 2, 3, 2, 1, 3, 1, 4, 1, 4]
def baseStart_253729 : Nat := 118140960795 + 253729 * 2 ^ 59
def prefixEnd_253729 : Nat := 4983230072969 + 3 ^ 40 * 253729 * 2
def baseEnd_253729 : Nat := 86856621989828678547085

theorem tailTrace_253729 : CollatzResearch.WordTrace tailWord_253729 prefixEnd_253729 86856621989828678547085 := by
  unfold tailWord_253729
  simp only [CollatzResearch.WordTrace]
  refine ⟨9254256897790641308356241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6169504598527094205570827 9254256897790641308356241)
  ·
    refine ⟨6940692673342980981267181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9254256897790641308356241 6940692673342980981267181)
    ·
      refine ⟨2602759752503617867975193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 6940692673342980981267181 2602759752503617867975193)
      ·
        refine ⟨1952069814377713400981395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2602759752503617867975193 1952069814377713400981395)
        ·
          refine ⟨2928104721566570101472093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1952069814377713400981395 2928104721566570101472093)
          ·
            refine ⟨1098039270587463788052035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2928104721566570101472093 1098039270587463788052035)
            ·
              refine ⟨1647058905881195682078053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1098039270587463788052035 1647058905881195682078053)
              ·
                refine ⟨308823544852724190389635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1647058905881195682078053 308823544852724190389635)
                ·
                  refine ⟨463235317279086285584453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 308823544852724190389635 463235317279086285584453)
                  ·
                    refine ⟨86856621989828678547085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 463235317279086285584453 86856621989828678547085)
                    ·
                      rfl

theorem cell22_253729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 1, 4, 1, 4].length) (baseStart_253729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253729 prefixEnd_253729 := by exact prefixLift 253729
  have htrace : WordTrace (prefixWord ++ tailWord_253729) baseStart_253729 baseEnd_253729 := by
    simpa [prefixWord, tailWord_253729, baseEnd_253729] using wordTrace_append hprefix tailTrace_253729
  have hstable : (prefixWord ++ tailWord_253729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253729).length < 2 ^ (prefixWord ++ tailWord_253729).sum := by decide
  have hdescent : baseEnd_253729 < baseStart_253729 := by decide
  rcases family_descends (prefixWord ++ tailWord_253729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253855 : List Nat := [1, 1, 2, 5, 3, 1, 2, 3, 1, 3]
def baseStart_253855 : Nat := 118140960795 + 253855 * 2 ^ 59
def prefixEnd_253855 : Nat := 4983230072969 + 3 ^ 40 * 253855 * 2
def baseEnd_253855 : Nat := 86899754364806349896699

theorem tailTrace_253855 : CollatzResearch.WordTrace tailWord_253855 prefixEnd_253855 86899754364806349896699 := by
  unfold tailWord_253855
  simp only [CollatzResearch.WordTrace]
  refine ⟨9258852495334164827443019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6172568330222776551628679 9258852495334164827443019)
  ·
    refine ⟨13888278743001247241164529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9258852495334164827443019 13888278743001247241164529)
    ·
      refine ⟨10416209057250935430873397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13888278743001247241164529 10416209057250935430873397)
      ·
        refine ⟨976519599117275196644381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10416209057250935430873397 976519599117275196644381)
        ·
          refine ⟨366194849668978198741643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 976519599117275196644381 366194849668978198741643)
          ·
            refine ⟨549292274503467298112465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366194849668978198741643 549292274503467298112465)
            ·
              refine ⟨411969205877600473584349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 549292274503467298112465 411969205877600473584349)
              ·
                refine ⟨154488452204100177594131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 411969205877600473584349 154488452204100177594131)
                ·
                  refine ⟨231732678306150266391197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 154488452204100177594131 231732678306150266391197)
                  ·
                    refine ⟨86899754364806349896699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 231732678306150266391197 86899754364806349896699)
                    ·
                      rfl

theorem cell22_253855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 3, 1, 2, 3, 1, 3].length) (baseStart_253855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253855 prefixEnd_253855 := by exact prefixLift 253855
  have htrace : WordTrace (prefixWord ++ tailWord_253855) baseStart_253855 baseEnd_253855 := by
    simpa [prefixWord, tailWord_253855, baseEnd_253855] using wordTrace_append hprefix tailTrace_253855
  have hstable : (prefixWord ++ tailWord_253855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253855).length < 2 ^ (prefixWord ++ tailWord_253855).sum := by decide
  have hdescent : baseEnd_253855 < baseStart_253855 := by decide
  rcases family_descends (prefixWord ++ tailWord_253855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_253945 : List Nat := [1, 2, 1, 3, 1, 6, 2, 1, 2, 3]
def baseStart_253945 : Nat := 118140960795 + 253945 * 2 ^ 59
def prefixEnd_253945 : Nat := 4983230072969 + 3 ^ 40 * 253945 * 2
def baseEnd_253945 : Nat := 86930563204076115146423

theorem tailTrace_253945 : CollatzResearch.WordTrace tailWord_253945 prefixEnd_253945 86930563204076115146423 := by
  unfold tailWord_253945
  simp only [CollatzResearch.WordTrace]
  refine ⟨9262135065008110198219289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6174756710005406798812859 9262135065008110198219289)
  ·
    refine ⟨6946601298756082648664467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9262135065008110198219289 6946601298756082648664467)
    ·
      refine ⟨10419901948134123972996701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6946601298756082648664467 10419901948134123972996701)
      ·
        refine ⟨3907463230550296489873763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10419901948134123972996701 3907463230550296489873763)
        ·
          refine ⟨5861194845825444734810645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3907463230550296489873763 5861194845825444734810645)
          ·
            refine ⟨274743508398067721944249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5861194845825444734810645 274743508398067721944249)
            ·
              refine ⟨206057631298550791458187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274743508398067721944249 206057631298550791458187)
              ·
                refine ⟨309086446947826187187281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206057631298550791458187 309086446947826187187281)
                ·
                  refine ⟨231814835210869640390461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309086446947826187187281 231814835210869640390461)
                  ·
                    refine ⟨86930563204076115146423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 231814835210869640390461 86930563204076115146423)
                    ·
                      rfl

theorem cell22_253945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 6, 2, 1, 2, 3].length) (baseStart_253945 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_253945 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_253945 prefixEnd_253945 := by exact prefixLift 253945
  have htrace : WordTrace (prefixWord ++ tailWord_253945) baseStart_253945 baseEnd_253945 := by
    simpa [prefixWord, tailWord_253945, baseEnd_253945] using wordTrace_append hprefix tailTrace_253945
  have hstable : (prefixWord ++ tailWord_253945).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_253945).length < 2 ^ (prefixWord ++ tailWord_253945).sum := by decide
  have hdescent : baseEnd_253945 < baseStart_253945 := by decide
  rcases family_descends (prefixWord ++ tailWord_253945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254001 : List Nat := [1, 2, 2, 3, 1, 4, 1, 1, 2, 5]
def baseStart_254001 : Nat := 118140960795 + 254001 * 2 ^ 59
def prefixEnd_254001 : Nat := 4983230072969 + 3 ^ 40 * 254001 * 2
def baseEnd_254001 : Nat := 86949733148510635746251

theorem tailTrace_254001 : CollatzResearch.WordTrace tailWord_254001 prefixEnd_254001 86949733148510635746251 := by
  unfold tailWord_254001
  simp only [CollatzResearch.WordTrace]
  refine ⟨9264177552805231762257857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6176118368536821174838571 9264177552805231762257857)
  ·
    refine ⟨6948133164603923821693393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9264177552805231762257857 6948133164603923821693393)
    ·
      refine ⟨5211099873452942866270045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6948133164603923821693393 5211099873452942866270045)
      ·
        refine ⟨1954162452544853574851267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5211099873452942866270045 1954162452544853574851267)
        ·
          refine ⟨2931243678817280362276901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1954162452544853574851267 2931243678817280362276901)
          ·
            refine ⟨549608189778240067926919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2931243678817280362276901 549608189778240067926919)
            ·
              refine ⟨824412284667360101890379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549608189778240067926919 824412284667360101890379)
              ·
                refine ⟨1236618427001040152835569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 824412284667360101890379 1236618427001040152835569)
                ·
                  refine ⟨927463820250780114626677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1236618427001040152835569 927463820250780114626677)
                  ·
                    refine ⟨86949733148510635746251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 927463820250780114626677 86949733148510635746251)
                    ·
                      rfl

theorem cell22_254001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 1, 2, 5].length) (baseStart_254001 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_254001 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_254001 prefixEnd_254001 := by exact prefixLift 254001
  have htrace : WordTrace (prefixWord ++ tailWord_254001) baseStart_254001 baseEnd_254001 := by
    simpa [prefixWord, tailWord_254001, baseEnd_254001] using wordTrace_append hprefix tailTrace_254001
  have hstable : (prefixWord ++ tailWord_254001).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254001).length < 2 ^ (prefixWord ++ tailWord_254001).sum := by decide
  have hdescent : baseEnd_254001 < baseStart_254001 := by decide
  rcases family_descends (prefixWord ++ tailWord_254001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254016 : List Nat := [2, 1, 1, 2, 2, 4, 2, 1, 3, 4]
def baseStart_254016 : Nat := 118140960795 + 254016 * 2 ^ 59
def prefixEnd_254016 : Nat := 4983230072969 + 3 ^ 40 * 254016 * 2
def baseEnd_254016 : Nat := 86954867955055596621205

theorem tailTrace_254016 : CollatzResearch.WordTrace tailWord_254016 prefixEnd_254016 86954867955055596621205 := by
  unfold tailWord_254016
  simp only [CollatzResearch.WordTrace]
  refine ⟨4632362323875444662026951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6176483098500592882702601 4632362323875444662026951)
  ·
    refine ⟨6948543485813166993040427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4632362323875444662026951 6948543485813166993040427)
    ·
      refine ⟨10422815228719750489560641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6948543485813166993040427 10422815228719750489560641)
      ·
        refine ⟨7817111421539812867170481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10422815228719750489560641 7817111421539812867170481)
        ·
          refine ⟨5862833566154859650377861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7817111421539812867170481 5862833566154859650377861)
          ·
            refine ⟨1099281293654036184445849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5862833566154859650377861 1099281293654036184445849)
            ·
              refine ⟨824460970240527138334387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1099281293654036184445849 824460970240527138334387)
              ·
                refine ⟨1236691455360790707501581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 824460970240527138334387 1236691455360790707501581)
                ·
                  refine ⟨463759295760296515313093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1236691455360790707501581 463759295760296515313093)
                  ·
                    refine ⟨86954867955055596621205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 463759295760296515313093 86954867955055596621205)
                    ·
                      rfl

theorem cell22_254016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 2, 1, 3, 4].length) (baseStart_254016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_254016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_254016 prefixEnd_254016 := by exact prefixLift 254016
  have htrace : WordTrace (prefixWord ++ tailWord_254016) baseStart_254016 baseEnd_254016 := by
    simpa [prefixWord, tailWord_254016, baseEnd_254016] using wordTrace_append hprefix tailTrace_254016
  have hstable : (prefixWord ++ tailWord_254016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254016).length < 2 ^ (prefixWord ++ tailWord_254016).sum := by decide
  have hdescent : baseEnd_254016 < baseStart_254016 := by decide
  rcases family_descends (prefixWord ++ tailWord_254016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254048 : List Nat := [2, 1, 1, 3, 2, 3, 2, 4, 4]
def baseStart_254048 : Nat := 118140960795 + 254048 * 2 ^ 59
def prefixEnd_254048 : Nat := 4983230072969 + 3 ^ 40 * 254048 * 2
def baseEnd_254048 : Nat := 28988607403006059940369

theorem tailTrace_254048 : CollatzResearch.WordTrace tailWord_254048 prefixEnd_254048 28988607403006059940369 := by
  unfold tailWord_254048
  simp only [CollatzResearch.WordTrace]
  refine ⟨4632945891817479394609399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6177261189089972526145865 4632945891817479394609399)
  ·
    refine ⟨6949418837726219091914099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4632945891817479394609399 6949418837726219091914099)
    ·
      refine ⟨10424128256589328637871149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6949418837726219091914099 10424128256589328637871149)
      ·
        refine ⟨3909048096220998239201681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10424128256589328637871149 3909048096220998239201681)
        ·
          refine ⟨2931786072165748679401261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3909048096220998239201681 2931786072165748679401261)
          ·
            refine ⟨1099419777062155754775473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2931786072165748679401261 1099419777062155754775473)
            ·
              refine ⟨824564832796616816081605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1099419777062155754775473 824564832796616816081605)
              ·
                refine ⟨154605906149365653015301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 824564832796616816081605 154605906149365653015301)
                ·
                  refine ⟨28988607403006059940369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154605906149365653015301 28988607403006059940369)
                  ·
                    rfl

theorem cell22_254048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 2, 4, 4].length) (baseStart_254048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_254048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_254048 prefixEnd_254048 := by exact prefixLift 254048
  have htrace : WordTrace (prefixWord ++ tailWord_254048) baseStart_254048 baseEnd_254048 := by
    simpa [prefixWord, tailWord_254048, baseEnd_254048] using wordTrace_append hprefix tailTrace_254048
  have hstable : (prefixWord ++ tailWord_254048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254048).length < 2 ^ (prefixWord ++ tailWord_254048).sum := by decide
  have hdescent : baseEnd_254048 < baseStart_254048 := by decide
  rcases family_descends (prefixWord ++ tailWord_254048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254061 : List Nat := [1, 5, 1, 1, 2, 1, 1, 1, 3, 6]
def baseStart_254061 : Nat := 118140960795 + 254061 * 2 ^ 59
def prefixEnd_254061 : Nat := 4983230072969 + 3 ^ 40 * 254061 * 2
def baseEnd_254061 : Nat := 86970272374690479246067

theorem tailTrace_254061 : CollatzResearch.WordTrace tailWord_254061 prefixEnd_254061 86970272374690479246067 := by
  unfold tailWord_254061
  simp only [CollatzResearch.WordTrace]
  refine ⟨9266365932587862009442037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6177577288391908006294691 9266365932587862009442037)
  ·
    refine ⟨868721806180112063385191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9266365932587862009442037 868721806180112063385191)
    ·
      refine ⟨1303082709270168095077787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 868721806180112063385191 1303082709270168095077787)
      ·
        refine ⟨1954624063905252142616681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1303082709270168095077787 1954624063905252142616681)
        ·
          refine ⟨1465968047928939106962511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1954624063905252142616681 1465968047928939106962511)
          ·
            refine ⟨2198952071893408660443767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1465968047928939106962511 2198952071893408660443767)
            ·
              refine ⟨3298428107840112990665651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2198952071893408660443767 3298428107840112990665651)
              ·
                refine ⟨4947642161760169485998477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3298428107840112990665651 4947642161760169485998477)
                ·
                  refine ⟨1855365810660063557249429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4947642161760169485998477 1855365810660063557249429)
                  ·
                    refine ⟨86970272374690479246067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1855365810660063557249429 86970272374690479246067)
                    ·
                      rfl

theorem cell22_254061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 1, 1, 3, 6].length) (baseStart_254061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_254061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_254061 prefixEnd_254061 := by exact prefixLift 254061
  have htrace : WordTrace (prefixWord ++ tailWord_254061) baseStart_254061 baseEnd_254061 := by
    simpa [prefixWord, tailWord_254061, baseEnd_254061] using wordTrace_append hprefix tailTrace_254061
  have hstable : (prefixWord ++ tailWord_254061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254061).length < 2 ^ (prefixWord ++ tailWord_254061).sum := by decide
  have hdescent : baseEnd_254061 < baseStart_254061 := by decide
  rcases family_descends (prefixWord ++ tailWord_254061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254063 : List Nat := [1, 1, 2, 1, 3, 6, 1, 1, 1, 5]
def baseStart_254063 : Nat := 118140960795 + 254063 * 2 ^ 59
def prefixEnd_254063 : Nat := 4983230072969 + 3 ^ 40 * 254063 * 2
def baseEnd_254063 : Nat := 86970957015563140696061

theorem tailTrace_254063 : CollatzResearch.WordTrace tailWord_254063 prefixEnd_254063 86970957015563140696061 := by
  unfold tailWord_254063
  simp only [CollatzResearch.WordTrace]
  refine ⟨9266438878580616351014843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6177625919053744234009895 9266438878580616351014843)
  ·
    refine ⟨13899658317870924526522265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9266438878580616351014843 13899658317870924526522265)
    ·
      refine ⟨10424743738403193394891699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13899658317870924526522265 10424743738403193394891699)
      ·
        refine ⟨15637115607604790092337549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10424743738403193394891699 15637115607604790092337549)
        ·
          refine ⟨5863918352851796284626581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15637115607604790092337549 5863918352851796284626581)
          ·
            refine ⟨274871172789927950841871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5863918352851796284626581 274871172789927950841871)
            ·
              refine ⟨412306759184891926262807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 274871172789927950841871 412306759184891926262807)
              ·
                refine ⟨618460138777337889394211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 412306759184891926262807 618460138777337889394211)
                ·
                  refine ⟨927690208166006834091317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 618460138777337889394211 927690208166006834091317)
                  ·
                    refine ⟨86970957015563140696061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 927690208166006834091317 86970957015563140696061)
                    ·
                      rfl

theorem cell22_254063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 6, 1, 1, 1, 5].length) (baseStart_254063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_254063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_254063 prefixEnd_254063 := by exact prefixLift 254063
  have htrace : WordTrace (prefixWord ++ tailWord_254063) baseStart_254063 baseEnd_254063 := by
    simpa [prefixWord, tailWord_254063, baseEnd_254063] using wordTrace_append hprefix tailTrace_254063
  have hstable : (prefixWord ++ tailWord_254063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254063).length < 2 ^ (prefixWord ++ tailWord_254063).sum := by decide
  have hdescent : baseEnd_254063 < baseStart_254063 := by decide
  rcases family_descends (prefixWord ++ tailWord_254063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254076 : List Nat := [2, 2, 2, 1, 1, 5, 1, 8]
def baseStart_254076 : Nat := 118140960795 + 254076 * 2 ^ 59
def prefixEnd_254076 : Nat := 4983230072969 + 3 ^ 40 * 254076 * 2
def baseEnd_254076 : Nat := 9663934131248382235669

theorem tailTrace_254076 : CollatzResearch.WordTrace tailWord_254076 prefixEnd_254076 9663934131248382235669 := by
  unfold tailWord_254076
  simp only [CollatzResearch.WordTrace]
  refine ⟨4633456513766759785619041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6177942018355679714158721 4633456513766759785619041)
  ·
    refine ⟨3475092385325069839214281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4633456513766759785619041 3475092385325069839214281)
    ·
      refine ⟨2606319288993802379410711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3475092385325069839214281 2606319288993802379410711)
      ·
        refine ⟨3909478933490703569116067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2606319288993802379410711 3909478933490703569116067)
        ·
          refine ⟨5864218400236055353674101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3909478933490703569116067 5864218400236055353674101)
          ·
            refine ⟨549770475022130189406947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5864218400236055353674101 549770475022130189406947)
            ·
              refine ⟨824655712533195284110421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 549770475022130189406947 824655712533195284110421)
              ·
                refine ⟨9663934131248382235669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 824655712533195284110421 9663934131248382235669)
                ·
                  rfl

theorem cell22_254076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 1, 8].length) (baseStart_254076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_254076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_254076 prefixEnd_254076 := by exact prefixLift 254076
  have htrace : WordTrace (prefixWord ++ tailWord_254076) baseStart_254076 baseEnd_254076 := by
    simpa [prefixWord, tailWord_254076, baseEnd_254076] using wordTrace_append hprefix tailTrace_254076
  have hstable : (prefixWord ++ tailWord_254076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254076).length < 2 ^ (prefixWord ++ tailWord_254076).sum := by decide
  have hdescent : baseEnd_254076 < baseStart_254076 := by decide
  rcases family_descends (prefixWord ++ tailWord_254076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254110 : List Nat := [4, 3, 1, 1, 3, 1, 2, 7]
def baseStart_254110 : Nat := 118140960795 + 254110 * 2 ^ 59
def prefixEnd_254110 : Nat := 4983230072969 + 3 ^ 40 * 254110 * 2
def baseEnd_254110 : Nat := 9665227341785631641213

theorem tailTrace_254110 : CollatzResearch.WordTrace tailWord_254110 prefixEnd_254110 9665227341785631641213 := by
  unfold tailWord_254110
  simp only [CollatzResearch.WordTrace]
  refine ⟨1158519138676292922246973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6178768739606895585317189 1158519138676292922246973)
  ·
    refine ⟨434444677003609845842615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1158519138676292922246973 434444677003609845842615)
    ·
      refine ⟨651667015505414768763923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 434444677003609845842615 651667015505414768763923)
      ·
        refine ⟨977500523258122153145885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 651667015505414768763923 977500523258122153145885)
        ·
          refine ⟨366562696221795807429707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 977500523258122153145885 366562696221795807429707)
          ·
            refine ⟨549844044332693711144561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 366562696221795807429707 549844044332693711144561)
            ·
              refine ⟨412383033249520283358421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 549844044332693711144561 412383033249520283358421)
              ·
                refine ⟨9665227341785631641213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 412383033249520283358421 9665227341785631641213)
                ·
                  rfl

theorem cell22_254110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 2, 7].length) (baseStart_254110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_254110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_254110 prefixEnd_254110 := by exact prefixLift 254110
  have htrace : WordTrace (prefixWord ++ tailWord_254110) baseStart_254110 baseEnd_254110 := by
    simpa [prefixWord, tailWord_254110, baseEnd_254110] using wordTrace_append hprefix tailTrace_254110
  have hstable : (prefixWord ++ tailWord_254110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254110).length < 2 ^ (prefixWord ++ tailWord_254110).sum := by decide
  have hdescent : baseEnd_254110 < baseStart_254110 := by decide
  rcases family_descends (prefixWord ++ tailWord_254110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254114 : List Nat := [3, 3, 1, 3, 1, 3, 2, 1, 2, 3]
def baseStart_254114 : Nat := 118140960795 + 254114 * 2 ^ 59
def prefixEnd_254114 : Nat := 4983230072969 + 3 ^ 40 * 254114 * 2
def baseEnd_254114 : Nat := 86988415357816007670905

theorem tailTrace_254114 : CollatzResearch.WordTrace tailWord_254114 prefixEnd_254114 86988415357816007670905 := by
  unfold tailWord_254114
  simp only [CollatzResearch.WordTrace]
  refine ⟨2317074750348963015280349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6178866000930568040747597 2317074750348963015280349)
  ·
    refine ⟨868903031380861130730131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2317074750348963015280349 868903031380861130730131)
    ·
      refine ⟨1303354547071291696095197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 868903031380861130730131 1303354547071291696095197)
      ·
        refine ⟨488757955151734386035699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1303354547071291696095197 488757955151734386035699)
        ·
          refine ⟨733136932727601579053549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488757955151734386035699 733136932727601579053549)
          ·
            refine ⟨274926349772850592145081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 733136932727601579053549 274926349772850592145081)
            ·
              refine ⟨206194762329637944108811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 274926349772850592145081 206194762329637944108811)
              ·
                refine ⟨309292143494456916163217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206194762329637944108811 309292143494456916163217)
                ·
                  refine ⟨231969107620842687122413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309292143494456916163217 231969107620842687122413)
                  ·
                    refine ⟨86988415357816007670905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 231969107620842687122413 86988415357816007670905)
                    ·
                      rfl

theorem cell22_254114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 3, 2, 1, 2, 3].length) (baseStart_254114 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_254114 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_254114 prefixEnd_254114 := by exact prefixLift 254114
  have htrace : WordTrace (prefixWord ++ tailWord_254114) baseStart_254114 baseEnd_254114 := by
    simpa [prefixWord, tailWord_254114, baseEnd_254114] using wordTrace_append hprefix tailTrace_254114
  have hstable : (prefixWord ++ tailWord_254114).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254114).length < 2 ^ (prefixWord ++ tailWord_254114).sum := by decide
  have hdescent : baseEnd_254114 < baseStart_254114 := by decide
  rcases family_descends (prefixWord ++ tailWord_254114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254168 : List Nat := [2, 1, 2, 2, 4, 1, 1, 2, 3, 4]
def baseStart_254168 : Nat := 118140960795 + 254168 * 2 ^ 59
def prefixEnd_254168 : Nat := 4983230072969 + 3 ^ 40 * 254168 * 2
def baseEnd_254168 : Nat := 87006900661377866820739

theorem tailTrace_254168 : CollatzResearch.WordTrace tailWord_254168 prefixEnd_254168 87006900661377866820739 := by
  unfold tailWord_254168
  simp only [CollatzResearch.WordTrace]
  refine ⟨4635134271600109641793579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6180179028800146189058105 4635134271600109641793579)
  ·
    refine ⟨6952701407400164462690369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4635134271600109641793579 6952701407400164462690369)
    ·
      refine ⟨5214526055550123347017777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6952701407400164462690369 5214526055550123347017777)
      ·
        refine ⟨3910894541662592510263333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5214526055550123347017777 3910894541662592510263333)
        ·
          refine ⟨733292726561736095674375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3910894541662592510263333 733292726561736095674375)
          ·
            refine ⟨1099939089842604143511563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733292726561736095674375 1099939089842604143511563)
            ·
              refine ⟨1649908634763906215267345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1099939089842604143511563 1649908634763906215267345)
              ·
                refine ⟨1237431476072929661450509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1649908634763906215267345 1237431476072929661450509)
                ·
                  refine ⟨464036803527348623043941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1237431476072929661450509 464036803527348623043941)
                  ·
                    refine ⟨87006900661377866820739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 464036803527348623043941 87006900661377866820739)
                    ·
                      rfl

theorem cell22_254168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 1, 2, 3, 4].length) (baseStart_254168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_254168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_254168 prefixEnd_254168 := by exact prefixLift 254168
  have htrace : WordTrace (prefixWord ++ tailWord_254168) baseStart_254168 baseEnd_254168 := by
    simpa [prefixWord, tailWord_254168, baseEnd_254168] using wordTrace_append hprefix tailTrace_254168
  have hstable : (prefixWord ++ tailWord_254168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254168).length < 2 ^ (prefixWord ++ tailWord_254168).sum := by decide
  have hdescent : baseEnd_254168 < baseStart_254168 := by decide
  rcases family_descends (prefixWord ++ tailWord_254168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254183 : List Nat := [1, 1, 5, 3, 1, 1, 1, 1, 8]
def baseStart_254183 : Nat := 118140960795 + 254183 * 2 ^ 59
def prefixEnd_254183 : Nat := 4983230072969 + 3 ^ 40 * 254183 * 2
def baseEnd_254183 : Nat := 29004011822640942565231

theorem tailTrace_254183 : CollatzResearch.WordTrace tailWord_254183 prefixEnd_254183 29004011822640942565231 := by
  unfold tailWord_254183
  simp only [CollatzResearch.WordTrace]
  refine ⟨9270815638145876845383203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6180543758763917896922135 9270815638145876845383203)
  ·
    refine ⟨13906223457218815268074805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9270815638145876845383203 13906223457218815268074805)
    ·
      refine ⟨1303708449114263931382013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 13906223457218815268074805 1303708449114263931382013)
      ·
        refine ⟨488890668417848974268255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1303708449114263931382013 488890668417848974268255)
        ·
          refine ⟨733336002626773461402383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 488890668417848974268255 733336002626773461402383)
          ·
            refine ⟨1100004003940160192103575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 733336002626773461402383 1100004003940160192103575)
            ·
              refine ⟨1650006005910240288155363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1100004003940160192103575 1650006005910240288155363)
              ·
                refine ⟨2475009008865360432233045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1650006005910240288155363 2475009008865360432233045)
                ·
                  refine ⟨29004011822640942565231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2475009008865360432233045 29004011822640942565231)
                  ·
                    rfl

theorem cell22_254183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 1, 8].length) (baseStart_254183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_254183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_254183 prefixEnd_254183 := by exact prefixLift 254183
  have htrace : WordTrace (prefixWord ++ tailWord_254183) baseStart_254183 baseEnd_254183 := by
    simpa [prefixWord, tailWord_254183, baseEnd_254183] using wordTrace_append hprefix tailTrace_254183
  have hstable : (prefixWord ++ tailWord_254183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254183).length < 2 ^ (prefixWord ++ tailWord_254183).sum := by decide
  have hdescent : baseEnd_254183 < baseStart_254183 := by decide
  rcases family_descends (prefixWord ++ tailWord_254183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254202 : List Nat := [3, 1, 1, 1, 1, 7, 2, 1, 1, 4]
def baseStart_254202 : Nat := 118140960795 + 254202 * 2 ^ 59
def prefixEnd_254202 : Nat := 4983230072969 + 3 ^ 40 * 254202 * 2
def baseEnd_254202 : Nat := 87018539556213111470635

theorem tailTrace_254202 : CollatzResearch.WordTrace tailWord_254202 prefixEnd_254202 87018539556213111470635 := by
  unfold tailWord_254202
  simp only [CollatzResearch.WordTrace]
  refine ⟨2317877156269260772581215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6181005750051362060216573 2317877156269260772581215)
  ·
    refine ⟨3476815734403891158871823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2317877156269260772581215 3476815734403891158871823)
    ·
      refine ⟨5215223601605836738307735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3476815734403891158871823 5215223601605836738307735)
      ·
        refine ⟨7822835402408755107461603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5215223601605836738307735 7822835402408755107461603)
        ·
          refine ⟨11734253103613132661192405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7822835402408755107461603 11734253103613132661192405)
          ·
            refine ⟨275021557115932796746697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 11734253103613132661192405 275021557115932796746697)
            ·
              refine ⟨206266167836949597560023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275021557115932796746697 206266167836949597560023)
              ·
                refine ⟨309399251755424396340035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206266167836949597560023 309399251755424396340035)
                ·
                  refine ⟨464098877633136594510053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 309399251755424396340035 464098877633136594510053)
                  ·
                    refine ⟨87018539556213111470635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 464098877633136594510053 87018539556213111470635)
                    ·
                      rfl

theorem cell22_254202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 7, 2, 1, 1, 4].length) (baseStart_254202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_254202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_254202 prefixEnd_254202 := by exact prefixLift 254202
  have htrace : WordTrace (prefixWord ++ tailWord_254202) baseStart_254202 baseEnd_254202 := by
    simpa [prefixWord, tailWord_254202, baseEnd_254202] using wordTrace_append hprefix tailTrace_254202
  have hstable : (prefixWord ++ tailWord_254202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254202).length < 2 ^ (prefixWord ++ tailWord_254202).sum := by decide
  have hdescent : baseEnd_254202 < baseStart_254202 := by decide
  rcases family_descends (prefixWord ++ tailWord_254202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254211 : List Nat := [1, 1, 1, 3, 2, 3, 11]
def baseStart_254211 : Nat := 118140960795 + 254211 * 2 ^ 59
def prefixEnd_254211 : Nat := 4983230072969 + 3 ^ 40 * 254211 * 2
def baseEnd_254211 : Nat := 3223022979264447703541

theorem tailTrace_254211 : CollatzResearch.WordTrace tailWord_254211 prefixEnd_254211 3223022979264447703541 := by
  unfold tailWord_254211
  simp only [CollatzResearch.WordTrace]
  refine ⟨9271836882044437627402487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6181224588029625084934991 9271836882044437627402487)
  ·
    refine ⟨13907755323066656441103731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9271836882044437627402487 13907755323066656441103731)
    ·
      refine ⟨20861632984599984661655597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13907755323066656441103731 20861632984599984661655597)
      ·
        refine ⟨7823112369224994248120849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20861632984599984661655597 7823112369224994248120849)
        ·
          refine ⟨5867334276918745686090637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7823112369224994248120849 5867334276918745686090637)
          ·
            refine ⟨2200250353844529632283989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5867334276918745686090637 2200250353844529632283989)
            ·
              refine ⟨3223022979264447703541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 2200250353844529632283989 3223022979264447703541)
              ·
                rfl

theorem cell22_254211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 11].length) (baseStart_254211 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_254211 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_254211 prefixEnd_254211 := by exact prefixLift 254211
  have htrace : WordTrace (prefixWord ++ tailWord_254211) baseStart_254211 baseEnd_254211 := by
    simpa [prefixWord, tailWord_254211, baseEnd_254211] using wordTrace_append hprefix tailTrace_254211
  have hstable : (prefixWord ++ tailWord_254211).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254211).length < 2 ^ (prefixWord ++ tailWord_254211).sum := by decide
  have hdescent : baseEnd_254211 < baseStart_254211 := by decide
  rcases family_descends (prefixWord ++ tailWord_254211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254232 : List Nat := [2, 1, 2, 3, 1, 2, 5, 1, 2, 3]
def baseStart_254232 : Nat := 118140960795 + 254232 * 2 ^ 59
def prefixEnd_254232 : Nat := 4983230072969 + 3 ^ 40 * 254232 * 2
def baseEnd_254232 : Nat := 87028809169303033220543

theorem tailTrace_254232 : CollatzResearch.WordTrace tailWord_254232 prefixEnd_254232 87028809169303033220543 := by
  unfold tailWord_254232
  simp only [CollatzResearch.WordTrace]
  refine ⟨4636301407484179106958475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6181735209978905475944633 4636301407484179106958475)
  ·
    refine ⟨6954452111226268660437713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4636301407484179106958475 6954452111226268660437713)
    ·
      refine ⟨5215839083419701495328285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6954452111226268660437713 5215839083419701495328285)
      ·
        refine ⟨1955939656282388060748107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5215839083419701495328285 1955939656282388060748107)
        ·
          refine ⟨2933909484423582091122161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1955939656282388060748107 2933909484423582091122161)
          ·
            refine ⟨2200432113317686568341621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2933909484423582091122161 2200432113317686568341621)
            ·
              refine ⟨206290510623533115782027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2200432113317686568341621 206290510623533115782027)
              ·
                refine ⟨309435765935299673673041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206290510623533115782027 309435765935299673673041)
                ·
                  refine ⟨232076824451474755254781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 309435765935299673673041 232076824451474755254781)
                  ·
                    refine ⟨87028809169303033220543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 232076824451474755254781 87028809169303033220543)
                    ·
                      rfl

theorem cell22_254232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 5, 1, 2, 3].length) (baseStart_254232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_254232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_254232 prefixEnd_254232 := by exact prefixLift 254232
  have htrace : WordTrace (prefixWord ++ tailWord_254232) baseStart_254232 baseEnd_254232 := by
    simpa [prefixWord, tailWord_254232, baseEnd_254232] using wordTrace_append hprefix tailTrace_254232
  have hstable : (prefixWord ++ tailWord_254232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254232).length < 2 ^ (prefixWord ++ tailWord_254232).sum := by decide
  have hdescent : baseEnd_254232 < baseStart_254232 := by decide
  rcases family_descends (prefixWord ++ tailWord_254232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254335 : List Nat := [1, 1, 2, 2, 1, 1, 2, 8, 4]
def baseStart_254335 : Nat := 118140960795 + 254335 * 2 ^ 59
def prefixEnd_254335 : Nat := 4983230072969 + 3 ^ 40 * 254335 * 2
def baseEnd_254335 : Nat := 29021356058081699298409

theorem tailTrace_254335 : CollatzResearch.WordTrace tailWord_254335 prefixEnd_254335 29021356058081699298409 := by
  unfold tailWord_254335
  simp only [CollatzResearch.WordTrace]
  refine ⟨9276359533595206804916459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6184239689063471203277639 9276359533595206804916459)
  ·
    refine ⟨13914539300392810207374689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9276359533595206804916459 13914539300392810207374689)
    ·
      refine ⟨10435904475294607655531017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13914539300392810207374689 10435904475294607655531017)
      ·
        refine ⟨7826928356470955741648263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10435904475294607655531017 7826928356470955741648263)
        ·
          refine ⟨11740392534706433612472395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7826928356470955741648263 11740392534706433612472395)
          ·
            refine ⟨17610588802059650418708593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11740392534706433612472395 17610588802059650418708593)
            ·
              refine ⟨13207941601544737814031445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17610588802059650418708593 13207941601544737814031445)
              ·
                refine ⟨154780565643102396258181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 13207941601544737814031445 154780565643102396258181)
                ·
                  refine ⟨29021356058081699298409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 154780565643102396258181 29021356058081699298409)
                  ·
                    rfl

theorem cell22_254335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 8, 4].length) (baseStart_254335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_254335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_254335 prefixEnd_254335 := by exact prefixLift 254335
  have htrace : WordTrace (prefixWord ++ tailWord_254335) baseStart_254335 baseEnd_254335 := by
    simpa [prefixWord, tailWord_254335, baseEnd_254335] using wordTrace_append hprefix tailTrace_254335
  have hstable : (prefixWord ++ tailWord_254335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254335).length < 2 ^ (prefixWord ++ tailWord_254335).sum := by decide
  have hdescent : baseEnd_254335 < baseStart_254335 := by decide
  rcases family_descends (prefixWord ++ tailWord_254335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254564 : List Nat := [2, 3, 1, 1, 2, 2, 4, 1, 3, 3]
def baseStart_254564 : Nat := 118140960795 + 254564 * 2 ^ 59
def prefixEnd_254564 : Nat := 4983230072969 + 3 ^ 40 * 254564 * 2
def baseEnd_254564 : Nat := 87142459554164833919525

theorem tailTrace_254564 : CollatzResearch.WordTrace tailWord_254564 prefixEnd_254564 87142459554164833919525 := by
  unfold tailWord_254564
  simp only [CollatzResearch.WordTrace]
  refine ⟨4642355924882789457501373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6189807899843719276668497 4642355924882789457501373)
  ·
    refine ⟨1740883471831046046563015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4642355924882789457501373 1740883471831046046563015)
    ·
      refine ⟨2611325207746569069844523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1740883471831046046563015 2611325207746569069844523)
      ·
        refine ⟨3916987811619853604766785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2611325207746569069844523 3916987811619853604766785)
        ·
          refine ⟨2937740858714890203575089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3916987811619853604766785 2937740858714890203575089)
          ·
            refine ⟨2203305644036167652681317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2937740858714890203575089 2203305644036167652681317)
            ·
              refine ⟨413119808256781434877747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2203305644036167652681317 413119808256781434877747)
              ·
                refine ⟨619679712385172152316621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 413119808256781434877747 619679712385172152316621)
                ·
                  refine ⟨232379892144439557118733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 619679712385172152316621 232379892144439557118733)
                  ·
                    refine ⟨87142459554164833919525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 232379892144439557118733 87142459554164833919525)
                    ·
                      rfl

theorem cell22_254564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 4, 1, 3, 3].length) (baseStart_254564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_254564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_254564 prefixEnd_254564 := by exact prefixLift 254564
  have htrace : WordTrace (prefixWord ++ tailWord_254564) baseStart_254564 baseEnd_254564 := by
    simpa [prefixWord, tailWord_254564, baseEnd_254564] using wordTrace_append hprefix tailTrace_254564
  have hstable : (prefixWord ++ tailWord_254564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254564).length < 2 ^ (prefixWord ++ tailWord_254564).sum := by decide
  have hdescent : baseEnd_254564 < baseStart_254564 := by decide
  rcases family_descends (prefixWord ++ tailWord_254564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254641 : List Nat := [1, 2, 2, 6, 1, 1, 1, 1, 3, 4]
def baseStart_254641 : Nat := 118140960795 + 254641 * 2 ^ 59
def prefixEnd_254641 : Nat := 4983230072969 + 3 ^ 40 * 254641 * 2
def baseEnd_254641 : Nat := 87168818227762299744289

theorem tailTrace_254641 : CollatzResearch.WordTrace tailWord_254641 prefixEnd_254641 87168818227762299744289 := by
  unfold tailWord_254641
  simp only [CollatzResearch.WordTrace]
  refine ⟨9287520270486621065555777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6191680180324414043703851 9287520270486621065555777)
  ·
    refine ⟨6965640202864965799166833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9287520270486621065555777 6965640202864965799166833)
    ·
      refine ⟨5224230152148724349375125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6965640202864965799166833 5224230152148724349375125)
      ·
        refine ⟨244885788381971453876959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 5224230152148724349375125 244885788381971453876959)
        ·
          refine ⟨367328682572957180815439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 244885788381971453876959 367328682572957180815439)
          ·
            refine ⟨550993023859435771223159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 367328682572957180815439 550993023859435771223159)
            ·
              refine ⟨826489535789153656834739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 550993023859435771223159 826489535789153656834739)
              ·
                refine ⟨1239734303683730485252109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 826489535789153656834739 1239734303683730485252109)
                ·
                  refine ⟨464900363881398931969541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1239734303683730485252109 464900363881398931969541)
                  ·
                    refine ⟨87168818227762299744289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 464900363881398931969541 87168818227762299744289)
                    ·
                      rfl

theorem cell22_254641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 1, 1, 3, 4].length) (baseStart_254641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_254641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_254641 prefixEnd_254641 := by exact prefixLift 254641
  have htrace : WordTrace (prefixWord ++ tailWord_254641) baseStart_254641 baseEnd_254641 := by
    simpa [prefixWord, tailWord_254641, baseEnd_254641] using wordTrace_append hprefix tailTrace_254641
  have hstable : (prefixWord ++ tailWord_254641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254641).length < 2 ^ (prefixWord ++ tailWord_254641).sum := by decide
  have hdescent : baseEnd_254641 < baseStart_254641 := by decide
  rcases family_descends (prefixWord ++ tailWord_254641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254654 : List Nat := [4, 2, 1, 1, 2, 1, 3, 2, 1, 5]
def baseStart_254654 : Nat := 118140960795 + 254654 * 2 ^ 59
def prefixEnd_254654 : Nat := 4983230072969 + 3 ^ 40 * 254654 * 2
def baseEnd_254654 : Nat := 87173268393434599169249

theorem tailTrace_254654 : CollatzResearch.WordTrace tailWord_254654 prefixEnd_254654 87173268393434599169249 := by
  unfold tailWord_254654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1160999302429940535722377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6191996279626349523852677 1160999302429940535722377)
  ·
    refine ⟨870749476822455401791783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1160999302429940535722377 870749476822455401791783)
    ·
      refine ⟨1306124215233683102687675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 870749476822455401791783 1306124215233683102687675)
      ·
        refine ⟨1959186322850524654031513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1306124215233683102687675 1959186322850524654031513)
        ·
          refine ⟨1469389742137893490523635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1959186322850524654031513 1469389742137893490523635)
          ·
            refine ⟨2204084613206840235785453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1469389742137893490523635 2204084613206840235785453)
            ·
              refine ⟨826531729952565088419545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2204084613206840235785453 826531729952565088419545)
              ·
                refine ⟨619898797464423816314659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 826531729952565088419545 619898797464423816314659)
                ·
                  refine ⟨929848196196635724471989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 619898797464423816314659 929848196196635724471989)
                  ·
                    refine ⟨87173268393434599169249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 929848196196635724471989 87173268393434599169249)
                    ·
                      rfl

theorem cell22_254654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 3, 2, 1, 5].length) (baseStart_254654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_254654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_254654 prefixEnd_254654 := by exact prefixLift 254654
  have htrace : WordTrace (prefixWord ++ tailWord_254654) baseStart_254654 baseEnd_254654 := by
    simpa [prefixWord, tailWord_254654, baseEnd_254654] using wordTrace_append hprefix tailTrace_254654
  have hstable : (prefixWord ++ tailWord_254654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254654).length < 2 ^ (prefixWord ++ tailWord_254654).sum := by decide
  have hdescent : baseEnd_254654 < baseStart_254654 := by decide
  rcases family_descends (prefixWord ++ tailWord_254654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254709 : List Nat := [1, 3, 6, 1, 2, 1, 2, 1, 1, 4]
def baseStart_254709 : Nat := 118140960795 + 254709 * 2 ^ 59
def prefixEnd_254709 : Nat := 4983230072969 + 3 ^ 40 * 254709 * 2
def baseEnd_254709 : Nat := 87192096017432789044081

theorem tailTrace_254709 : CollatzResearch.WordTrace tailWord_254709 prefixEnd_254709 87192096017432789044081 := by
  unfold tailWord_254709
  simp only [CollatzResearch.WordTrace]
  refine ⟨9290000434240268679031181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6193333622826845786020787 9290000434240268679031181)
  ·
    refine ⟨3483750162840100754636693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9290000434240268679031181 3483750162840100754636693)
    ·
      refine ⟨163300788883129722873595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 3483750162840100754636693 163300788883129722873595)
      ·
        refine ⟨244951183324694584310393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 163300788883129722873595 244951183324694584310393)
        ·
          refine ⟨183713387493520938232795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 244951183324694584310393 183713387493520938232795)
          ·
            refine ⟨275570081240281407349193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183713387493520938232795 275570081240281407349193)
            ·
              refine ⟨206677560930211055511895, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275570081240281407349193 206677560930211055511895)
              ·
                refine ⟨310016341395316583267843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206677560930211055511895 310016341395316583267843)
                ·
                  refine ⟨465024512092974874901765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 310016341395316583267843 465024512092974874901765)
                  ·
                    refine ⟨87192096017432789044081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 465024512092974874901765 87192096017432789044081)
                    ·
                      rfl

theorem cell22_254709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_254709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_254709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_254709 prefixEnd_254709 := by exact prefixLift 254709
  have htrace : WordTrace (prefixWord ++ tailWord_254709) baseStart_254709 baseEnd_254709 := by
    simpa [prefixWord, tailWord_254709, baseEnd_254709] using wordTrace_append hprefix tailTrace_254709
  have hstable : (prefixWord ++ tailWord_254709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254709).length < 2 ^ (prefixWord ++ tailWord_254709).sum := by decide
  have hdescent : baseEnd_254709 < baseStart_254709 := by decide
  rcases family_descends (prefixWord ++ tailWord_254709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254712 : List Nat := [2, 1, 2, 1, 1, 2, 4, 2, 7]
def baseStart_254712 : Nat := 118140960795 + 254712 * 2 ^ 59
def prefixEnd_254712 : Nat := 4983230072969 + 3 ^ 40 * 254712 * 2
def baseEnd_254712 : Nat := 29064374326247260406357

theorem tailTrace_254712 : CollatzResearch.WordTrace tailWord_254712 prefixEnd_254712 29064374326247260406357 := by
  unfold tailWord_254712
  simp only [CollatzResearch.WordTrace]
  refine ⟨4645054926614700095695195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6193406568819600127593593 4645054926614700095695195)
  ·
    refine ⟨6967582389922050143542793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4645054926614700095695195 6967582389922050143542793)
    ·
      refine ⟨5225686792441537607657095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6967582389922050143542793 5225686792441537607657095)
      ·
        refine ⟨7838530188662306411485643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5225686792441537607657095 7838530188662306411485643)
        ·
          refine ⟨11757795282993459617228465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7838530188662306411485643 11757795282993459617228465)
          ·
            refine ⟨8818346462245094712921349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11757795282993459617228465 8818346462245094712921349)
            ·
              refine ⟨1653439961670955258672753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8818346462245094712921349 1653439961670955258672753)
              ·
                refine ⟨1240079971253216444004565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1653439961670955258672753 1240079971253216444004565)
                ·
                  refine ⟨29064374326247260406357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1240079971253216444004565 29064374326247260406357)
                  ·
                    rfl

theorem cell22_254712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 4, 2, 7].length) (baseStart_254712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_254712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_254712 prefixEnd_254712 := by exact prefixLift 254712
  have htrace : WordTrace (prefixWord ++ tailWord_254712) baseStart_254712 baseEnd_254712 := by
    simpa [prefixWord, tailWord_254712, baseEnd_254712] using wordTrace_append hprefix tailTrace_254712
  have hstable : (prefixWord ++ tailWord_254712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254712).length < 2 ^ (prefixWord ++ tailWord_254712).sum := by decide
  have hdescent : baseEnd_254712 < baseStart_254712 := by decide
  rcases family_descends (prefixWord ++ tailWord_254712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254729 : List Nat := [1, 2, 1, 1, 3, 2, 5, 2, 5]
def baseStart_254729 : Nat := 118140960795 + 254729 * 2 ^ 59
def prefixEnd_254729 : Nat := 4983230072969 + 3 ^ 40 * 254729 * 2
def baseEnd_254729 : Nat := 29066314142053134514673

theorem tailTrace_254729 : CollatzResearch.WordTrace tailWord_254729 prefixEnd_254729 29066314142053134514673 := by
  unfold tailWord_254729
  simp only [CollatzResearch.WordTrace]
  refine ⟨9290729894167812094759241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6193819929445208063172827 9290729894167812094759241)
  ·
    refine ⟨6968047420625859071069431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9290729894167812094759241 6968047420625859071069431)
    ·
      refine ⟨10452071130938788606604147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6968047420625859071069431 10452071130938788606604147)
      ·
        refine ⟨15678106696408182909906221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10452071130938788606604147 15678106696408182909906221)
        ·
          refine ⟨5879290011153068591214833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15678106696408182909906221 5879290011153068591214833)
          ·
            refine ⟨4409467508364801443411125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5879290011153068591214833 4409467508364801443411125)
            ·
              refine ⟨413387578909200135319793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4409467508364801443411125 413387578909200135319793)
              ·
                refine ⟨310040684181900101489845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 413387578909200135319793 310040684181900101489845)
                ·
                  refine ⟨29066314142053134514673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 310040684181900101489845 29066314142053134514673)
                  ·
                    rfl

theorem cell22_254729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 5, 2, 5].length) (baseStart_254729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_254729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_254729 prefixEnd_254729 := by exact prefixLift 254729
  have htrace : WordTrace (prefixWord ++ tailWord_254729) baseStart_254729 baseEnd_254729 := by
    simpa [prefixWord, tailWord_254729, baseEnd_254729] using wordTrace_append hprefix tailTrace_254729
  have hstable : (prefixWord ++ tailWord_254729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254729).length < 2 ^ (prefixWord ++ tailWord_254729).sum := by decide
  have hdescent : baseEnd_254729 < baseStart_254729 := by decide
  rcases family_descends (prefixWord ++ tailWord_254729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254746 : List Nat := [3, 1, 1, 3, 2, 1, 5, 1, 5]
def baseStart_254746 : Nat := 118140960795 + 254746 * 2 ^ 59
def prefixEnd_254746 : Nat := 4983230072969 + 3 ^ 40 * 254746 * 2
def baseEnd_254746 : Nat := 29068253957859008622989

theorem tailTrace_254746 : CollatzResearch.WordTrace tailWord_254746 prefixEnd_254746 29068253957859008622989 := by
  unfold tailWord_254746
  simp only [CollatzResearch.WordTrace]
  refine ⟨2322837483776555999532023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6194233290070815998752061 2322837483776555999532023)
  ·
    refine ⟨3484256225664833999298035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2322837483776555999532023 3484256225664833999298035)
    ·
      refine ⟨5226384338497250998947053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3484256225664833999298035 5226384338497250998947053)
      ·
        refine ⟨1959894126936469124605145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5226384338497250998947053 1959894126936469124605145)
        ·
          refine ⟨1469920595202351843453859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1959894126936469124605145 1469920595202351843453859)
          ·
            refine ⟨2204880892803527765180789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1469920595202351843453859 2204880892803527765180789)
            ·
              refine ⟨206707583700330727985699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2204880892803527765180789 206707583700330727985699)
              ·
                refine ⟨310061375550496091978549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206707583700330727985699 310061375550496091978549)
                ·
                  refine ⟨29068253957859008622989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 310061375550496091978549 29068253957859008622989)
                  ·
                    rfl

theorem cell22_254746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 5, 1, 5].length) (baseStart_254746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_254746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_254746 prefixEnd_254746 := by exact prefixLift 254746
  have htrace : WordTrace (prefixWord ++ tailWord_254746) baseStart_254746 baseEnd_254746 := by
    simpa [prefixWord, tailWord_254746, baseEnd_254746] using wordTrace_append hprefix tailTrace_254746
  have hstable : (prefixWord ++ tailWord_254746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254746).length < 2 ^ (prefixWord ++ tailWord_254746).sum := by decide
  have hdescent : baseEnd_254746 < baseStart_254746 := by decide
  rcases family_descends (prefixWord ++ tailWord_254746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254797 : List Nat := [1, 6, 1, 2, 3, 1, 2, 1, 5]
def baseStart_254797 : Nat := 118140960795 + 254797 * 2 ^ 59
def prefixEnd_254797 : Nat := 4983230072969 + 3 ^ 40 * 254797 * 2
def baseEnd_254797 : Nat := 29074073405276630947937

theorem tailTrace_254797 : CollatzResearch.WordTrace tailWord_254797 prefixEnd_254797 29074073405276630947937 := by
  unfold tailWord_254797
  simp only [CollatzResearch.WordTrace]
  refine ⟨9293210057921459708234645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6195473371947639805489763 9293210057921459708234645)
  ·
    refine ⟨435619221465068423823499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9293210057921459708234645 435619221465068423823499)
    ·
      refine ⟨653428832197602635735249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 435619221465068423823499 653428832197602635735249)
      ·
        refine ⟨490071624148201976801437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 653428832197602635735249 490071624148201976801437)
        ·
          refine ⟨183776859055575741300539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 490071624148201976801437 183776859055575741300539)
          ·
            refine ⟨275665288583363611950809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 183776859055575741300539 275665288583363611950809)
            ·
              refine ⟨206748966437522708963107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 275665288583363611950809 206748966437522708963107)
              ·
                refine ⟨310123449656284063444661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 206748966437522708963107 310123449656284063444661)
                ·
                  refine ⟨29074073405276630947937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 310123449656284063444661 29074073405276630947937)
                  ·
                    rfl

theorem cell22_254797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_254797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_254797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_254797 prefixEnd_254797 := by exact prefixLift 254797
  have htrace : WordTrace (prefixWord ++ tailWord_254797) baseStart_254797 baseEnd_254797 := by
    simpa [prefixWord, tailWord_254797, baseEnd_254797] using wordTrace_append hprefix tailTrace_254797
  have hstable : (prefixWord ++ tailWord_254797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254797).length < 2 ^ (prefixWord ++ tailWord_254797).sum := by decide
  have hdescent : baseEnd_254797 < baseStart_254797 := by decide
  rcases family_descends (prefixWord ++ tailWord_254797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254819 : List Nat := [1, 1, 1, 5, 3, 1, 2, 8]
def baseStart_254819 : Nat := 118140960795 + 254819 * 2 ^ 59
def prefixEnd_254819 : Nat := 4983230072969 + 3 ^ 40 * 254819 * 2
def baseEnd_254819 : Nat := 9692194585047685421527

theorem tailTrace_254819 : CollatzResearch.WordTrace tailWord_254819 prefixEnd_254819 9692194585047685421527 := by
  unfold tailWord_254819
  simp only [CollatzResearch.WordTrace]
  refine ⟨9294012463841757465535511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6196008309227838310357007 9294012463841757465535511)
  ·
    refine ⟨13941018695762636198303267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9294012463841757465535511 13941018695762636198303267)
    ·
      refine ⟨20911528043643954297454901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13941018695762636198303267 20911528043643954297454901)
      ·
        refine ⟨1960455754091620715386397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 20911528043643954297454901 1960455754091620715386397)
        ·
          refine ⟨735170907784357768269899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1960455754091620715386397 735170907784357768269899)
          ·
            refine ⟨1102756361676536652404849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735170907784357768269899 1102756361676536652404849)
            ·
              refine ⟨827067271257402489303637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1102756361676536652404849 827067271257402489303637)
              ·
                refine ⟨9692194585047685421527, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 827067271257402489303637 9692194585047685421527)
                ·
                  rfl

theorem cell22_254819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 8].length) (baseStart_254819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_254819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_254819 prefixEnd_254819 := by exact prefixLift 254819
  have htrace : WordTrace (prefixWord ++ tailWord_254819) baseStart_254819 baseEnd_254819 := by
    simpa [prefixWord, tailWord_254819, baseEnd_254819] using wordTrace_append hprefix tailTrace_254819
  have hstable : (prefixWord ++ tailWord_254819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254819).length < 2 ^ (prefixWord ++ tailWord_254819).sum := by decide
  have hdescent : baseEnd_254819 < baseStart_254819 := by decide
  rcases family_descends (prefixWord ++ tailWord_254819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254838 : List Nat := [5, 1, 1, 3, 1, 1, 2, 2, 2, 4]
def baseStart_254838 : Nat := 118140960795 + 254838 * 2 ^ 59
def prefixEnd_254838 : Nat := 4983230072969 + 3 ^ 40 * 254838 * 2
def baseEnd_254838 : Nat := 87236255353719452568685

theorem tailTrace_254838 : CollatzResearch.WordTrace tailWord_254838 prefixEnd_254838 87236255353719452568685 := by
  unfold tailWord_254838
  simp only [CollatzResearch.WordTrace]
  refine ⟨580919090673307731904823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6196470300515282473651445 580919090673307731904823)
  ·
    refine ⟨871378636009961597857235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 580919090673307731904823 871378636009961597857235)
    ·
      refine ⟨1307067954014942396785853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 871378636009961597857235 1307067954014942396785853)
      ·
        refine ⟨490150482755603398794695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1307067954014942396785853 490150482755603398794695)
        ·
          refine ⟨735225724133405098192043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490150482755603398794695 735225724133405098192043)
          ·
            refine ⟨1102838586200107647288065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735225724133405098192043 1102838586200107647288065)
            ·
              refine ⟨827128939650080735466049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1102838586200107647288065 827128939650080735466049)
              ·
                refine ⟨620346704737560551599537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 827128939650080735466049 620346704737560551599537)
                ·
                  refine ⟨465260028553170413699653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 620346704737560551599537 465260028553170413699653)
                  ·
                    refine ⟨87236255353719452568685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 465260028553170413699653 87236255353719452568685)
                    ·
                      rfl

theorem cell22_254838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 1, 2, 2, 2, 4].length) (baseStart_254838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_254838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_254838 prefixEnd_254838 := by exact prefixLift 254838
  have htrace : WordTrace (prefixWord ++ tailWord_254838) baseStart_254838 baseEnd_254838 := by
    simpa [prefixWord, tailWord_254838, baseEnd_254838] using wordTrace_append hprefix tailTrace_254838
  have hstable : (prefixWord ++ tailWord_254838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254838).length < 2 ^ (prefixWord ++ tailWord_254838).sum := by decide
  have hdescent : baseEnd_254838 < baseStart_254838 := by decide
  rcases family_descends (prefixWord ++ tailWord_254838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254851 : List Nat := [1, 1, 1, 3, 4, 1, 2, 3, 3, 3]
def baseStart_254851 : Nat := 118140960795 + 254851 * 2 ^ 59
def prefixEnd_254851 : Nat := 4983230072969 + 3 ^ 40 * 254851 * 2
def baseEnd_254851 : Nat := 87240705519391751993645

theorem tailTrace_254851 : CollatzResearch.WordTrace tailWord_254851 prefixEnd_254851 87240705519391751993645 := by
  unfold tailWord_254851
  simp only [CollatzResearch.WordTrace]
  refine ⟨9295179599725826930700407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6196786399817217953800271 9295179599725826930700407)
  ·
    refine ⟨13942769399588740396050611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9295179599725826930700407 13942769399588740396050611)
    ·
      refine ⟨20914154099383110594075917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13942769399588740396050611 20914154099383110594075917)
      ·
        refine ⟨7842807787268666472778469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 20914154099383110594075917 7842807787268666472778469)
        ·
          refine ⟨1470526460112874963645963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7842807787268666472778469 1470526460112874963645963)
          ·
            refine ⟨2205789690169312445468945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470526460112874963645963 2205789690169312445468945)
            ·
              refine ⟨1654342267626984334101709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2205789690169312445468945 1654342267626984334101709)
              ·
                refine ⟨620378350360119125288141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1654342267626984334101709 620378350360119125288141)
                ·
                  refine ⟨232641881385044671983053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 620378350360119125288141 232641881385044671983053)
                  ·
                    refine ⟨87240705519391751993645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 232641881385044671983053 87240705519391751993645)
                    ·
                      rfl

theorem cell22_254851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 2, 3, 3, 3].length) (baseStart_254851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_254851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_254851 prefixEnd_254851 := by exact prefixLift 254851
  have htrace : WordTrace (prefixWord ++ tailWord_254851) baseStart_254851 baseEnd_254851 := by
    simpa [prefixWord, tailWord_254851, baseEnd_254851] using wordTrace_append hprefix tailTrace_254851
  have hstable : (prefixWord ++ tailWord_254851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254851).length < 2 ^ (prefixWord ++ tailWord_254851).sum := by decide
  have hdescent : baseEnd_254851 < baseStart_254851 := by decide
  rcases family_descends (prefixWord ++ tailWord_254851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254868 : List Nat := [2, 4, 2, 1, 1, 1, 3, 2, 3, 3]
def baseStart_254868 : Nat := 118140960795 + 254868 * 2 ^ 59
def prefixEnd_254868 : Nat := 4983230072969 + 3 ^ 40 * 254868 * 2
def baseEnd_254868 : Nat := 87246524966809374318593

theorem tailTrace_254868 : CollatzResearch.WordTrace tailWord_254868 prefixEnd_254868 87246524966809374318593 := by
  unfold tailWord_254868
  simp only [CollatzResearch.WordTrace]
  refine ⟨4647899820332119417034629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6197199760442825889379505 4647899820332119417034629)
  ·
    refine ⟨871481216312272390693993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4647899820332119417034629 871481216312272390693993)
    ·
      refine ⟨653610912234204293020495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 871481216312272390693993 653610912234204293020495)
      ·
        refine ⟨980416368351306439530743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 653610912234204293020495 980416368351306439530743)
        ·
          refine ⟨1470624552526959659296115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 980416368351306439530743 1470624552526959659296115)
          ·
            refine ⟨2205936828790439488944173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1470624552526959659296115 2205936828790439488944173)
            ·
              refine ⟨827226310796414808354065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2205936828790439488944173 827226310796414808354065)
              ·
                refine ⟨620419733097311106265549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 827226310796414808354065 620419733097311106265549)
                ·
                  refine ⟨232657399911491664849581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 620419733097311106265549 232657399911491664849581)
                  ·
                    refine ⟨87246524966809374318593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 232657399911491664849581 87246524966809374318593)
                    ·
                      rfl

theorem cell22_254868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_254868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_254868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_254868 prefixEnd_254868 := by exact prefixLift 254868
  have htrace : WordTrace (prefixWord ++ tailWord_254868) baseStart_254868 baseEnd_254868 := by
    simpa [prefixWord, tailWord_254868, baseEnd_254868] using wordTrace_append hprefix tailTrace_254868
  have hstable : (prefixWord ++ tailWord_254868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254868).length < 2 ^ (prefixWord ++ tailWord_254868).sum := by decide
  have hdescent : baseEnd_254868 < baseStart_254868 := by decide
  rcases family_descends (prefixWord ++ tailWord_254868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_254926 : List Nat := [4, 1, 1, 1, 2, 3, 2, 2, 6]
def baseStart_254926 : Nat := 118140960795 + 254926 * 2 ^ 59
def prefixEnd_254926 : Nat := 4983230072969 + 3 ^ 40 * 254926 * 2
def baseEnd_254926 : Nat := 29088793184038852122805

theorem tailTrace_254926 : CollatzResearch.WordTrace tailWord_254926 prefixEnd_254926 29088793184038852122805 := by
  unfold tailWord_254926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1162239384306764342460079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6198610049636076493120421 1162239384306764342460079)
  ·
    refine ⟨1743359076460146513690119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1162239384306764342460079 1743359076460146513690119)
    ·
      refine ⟨2615038614690219770535179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1743359076460146513690119 2615038614690219770535179)
      ·
        refine ⟨3922557922035329655802769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2615038614690219770535179 3922557922035329655802769)
        ·
          refine ⟨2941918441526497241852077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3922557922035329655802769 2941918441526497241852077)
          ·
            refine ⟨1103219415572436465694529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2941918441526497241852077 1103219415572436465694529)
            ·
              refine ⟨827414561679327349270897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1103219415572436465694529 827414561679327349270897)
              ·
                refine ⟨620560921259495511953173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 827414561679327349270897 620560921259495511953173)
                ·
                  refine ⟨29088793184038852122805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 620560921259495511953173 29088793184038852122805)
                  ·
                    rfl

theorem cell22_254926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 2, 6].length) (baseStart_254926 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_254926 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_254926 prefixEnd_254926 := by exact prefixLift 254926
  have htrace : WordTrace (prefixWord ++ tailWord_254926) baseStart_254926 baseEnd_254926 := by
    simpa [prefixWord, tailWord_254926, baseEnd_254926] using wordTrace_append hprefix tailTrace_254926
  have hstable : (prefixWord ++ tailWord_254926).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_254926).length < 2 ^ (prefixWord ++ tailWord_254926).sum := by decide
  have hdescent : baseEnd_254926 < baseStart_254926 := by decide
  rcases family_descends (prefixWord ++ tailWord_254926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255020 : List Nat := [2, 2, 1, 1, 1, 2, 5, 4, 1, 3]
def baseStart_255020 : Nat := 118140960795 + 255020 * 2 ^ 59
def prefixEnd_255020 : Nat := 4983230072969 + 3 ^ 40 * 255020 * 2
def baseEnd_255020 : Nat := 87298557673131644518127

theorem tailTrace_255020 : CollatzResearch.WordTrace tailWord_255020 prefixEnd_255020 87298557673131644518127 := by
  unfold tailWord_255020
  simp only [CollatzResearch.WordTrace]
  refine ⟨4650671768056784396801257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6200895690742379195735009 4650671768056784396801257)
  ·
    refine ⟨3488003826042588297600943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4650671768056784396801257 3488003826042588297600943)
    ·
      refine ⟨5232005739063882446401415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3488003826042588297600943 5232005739063882446401415)
      ·
        refine ⟨7848008608595823669602123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5232005739063882446401415 7848008608595823669602123)
        ·
          refine ⟨11772012912893735504403185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7848008608595823669602123 11772012912893735504403185)
          ·
            refine ⟨8829009684670301628302389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11772012912893735504403185 8829009684670301628302389)
            ·
              refine ⟨827719657937840777653349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8829009684670301628302389 827719657937840777653349)
              ·
                refine ⟨155197435863345145810003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 827719657937840777653349 155197435863345145810003)
                ·
                  refine ⟨232796153795017718715005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155197435863345145810003 232796153795017718715005)
                  ·
                    refine ⟨87298557673131644518127, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 232796153795017718715005 87298557673131644518127)
                    ·
                      rfl

theorem cell22_255020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 5, 4, 1, 3].length) (baseStart_255020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_255020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_255020 prefixEnd_255020 := by exact prefixLift 255020
  have htrace : WordTrace (prefixWord ++ tailWord_255020) baseStart_255020 baseEnd_255020 := by
    simpa [prefixWord, tailWord_255020, baseEnd_255020] using wordTrace_append hprefix tailTrace_255020
  have hstable : (prefixWord ++ tailWord_255020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255020).length < 2 ^ (prefixWord ++ tailWord_255020).sum := by decide
  have hdescent : baseEnd_255020 < baseStart_255020 := by decide
  rcases family_descends (prefixWord ++ tailWord_255020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255033 : List Nat := [1, 2, 1, 5, 2, 1, 2, 3, 5]
def baseStart_255033 : Nat := 118140960795 + 255033 * 2 ^ 59
def prefixEnd_255033 : Nat := 4983230072969 + 3 ^ 40 * 255033 * 2
def baseEnd_255033 : Nat := 29101002612934647981029

theorem tailTrace_255033 : CollatzResearch.WordTrace tailWord_255033 prefixEnd_255033 29101002612934647981029 := by
  unfold tailWord_255033
  simp only [CollatzResearch.WordTrace]
  refine ⟨9301817685066472013825753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6201211790044314675883835 9301817685066472013825753)
  ·
    refine ⟨6976363263799854010369315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9301817685066472013825753 6976363263799854010369315)
    ·
      refine ⟨10464544895699781015553973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 6976363263799854010369315 10464544895699781015553973)
      ·
        refine ⟨981051083971854470208185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10464544895699781015553973 981051083971854470208185)
        ·
          refine ⟨735788312978890852656139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 981051083971854470208185 735788312978890852656139)
          ·
            refine ⟨1103682469468336278984209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 735788312978890852656139 1103682469468336278984209)
            ·
              refine ⟨827761852101252209238157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1103682469468336278984209 827761852101252209238157)
              ·
                refine ⟨310410694537969578464309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 827761852101252209238157 310410694537969578464309)
                ·
                  refine ⟨29101002612934647981029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 310410694537969578464309 29101002612934647981029)
                  ·
                    rfl

theorem cell22_255033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 2, 3, 5].length) (baseStart_255033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_255033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_255033 prefixEnd_255033 := by exact prefixLift 255033
  have htrace : WordTrace (prefixWord ++ tailWord_255033) baseStart_255033 baseEnd_255033 := by
    simpa [prefixWord, tailWord_255033, baseEnd_255033] using wordTrace_append hprefix tailTrace_255033
  have hstable : (prefixWord ++ tailWord_255033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255033).length < 2 ^ (prefixWord ++ tailWord_255033).sum := by decide
  have hdescent : baseEnd_255033 < baseStart_255033 := by decide
  rcases family_descends (prefixWord ++ tailWord_255033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255061 : List Nat := [1, 3, 2, 2, 1, 2, 1, 2, 8]
def baseStart_255061 : Nat := 118140960795 + 255061 * 2 ^ 59
def prefixEnd_255061 : Nat := 4983230072969 + 3 ^ 40 * 255061 * 2
def baseEnd_255061 : Nat := 29104197603673734747667

theorem tailTrace_255061 : CollatzResearch.WordTrace tailWord_255061 prefixEnd_255061 29104197603673734747667 := by
  unfold tailWord_255061
  simp only [CollatzResearch.WordTrace]
  refine ⟨9302838928965032795845037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6201892619310021863896691 9302838928965032795845037)
  ·
    refine ⟨3488564598361887298441889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9302838928965032795845037 3488564598361887298441889)
    ·
      refine ⟨2616423448771415473831417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3488564598361887298441889 2616423448771415473831417)
      ·
        refine ⟨1962317586578561605373563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2616423448771415473831417 1962317586578561605373563)
        ·
          refine ⟨2943476379867842408060345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1962317586578561605373563 2943476379867842408060345)
          ·
            refine ⟨2207607284900881806045259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2943476379867842408060345 2207607284900881806045259)
            ·
              refine ⟨3311410927351322709067889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2207607284900881806045259 3311410927351322709067889)
              ·
                refine ⟨2483558195513492031800917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3311410927351322709067889 2483558195513492031800917)
                ·
                  refine ⟨29104197603673734747667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2483558195513492031800917 29104197603673734747667)
                  ·
                    rfl

theorem cell22_255061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 2, 8].length) (baseStart_255061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_255061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_255061 prefixEnd_255061 := by exact prefixLift 255061
  have htrace : WordTrace (prefixWord ++ tailWord_255061) baseStart_255061 baseEnd_255061 := by
    simpa [prefixWord, tailWord_255061, baseEnd_255061] using wordTrace_append hprefix tailTrace_255061
  have hstable : (prefixWord ++ tailWord_255061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255061).length < 2 ^ (prefixWord ++ tailWord_255061).sum := by decide
  have hdescent : baseEnd_255061 < baseStart_255061 := by decide
  rcases family_descends (prefixWord ++ tailWord_255061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255108 : List Nat := [2, 3, 2, 1, 2, 2, 2, 1, 1, 6]
def baseStart_255108 : Nat := 118140960795 + 255108 * 2 ^ 59
def prefixEnd_255108 : Nat := 4983230072969 + 3 ^ 40 * 255108 * 2
def baseEnd_255108 : Nat := 87328681871528748317857

theorem tailTrace_255108 : CollatzResearch.WordTrace tailWord_255108 prefixEnd_255108 87328681871528748317857 := by
  unfold tailWord_255108
  simp only [CollatzResearch.WordTrace]
  refine ⟨4652276579897379911402989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6203035439863173215203985 4652276579897379911402989)
  ·
    refine ⟨1744603717461517466776121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4652276579897379911402989 1744603717461517466776121)
    ·
      refine ⟨1308452788096138100082091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1744603717461517466776121 1308452788096138100082091)
      ·
        refine ⟨1962679182144207150123137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1308452788096138100082091 1962679182144207150123137)
        ·
          refine ⟨1472009386608155362592353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1962679182144207150123137 1472009386608155362592353)
          ·
            refine ⟨1104007039956116521944265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1472009386608155362592353 1104007039956116521944265)
            ·
              refine ⟨828005279967087391458199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1104007039956116521944265 828005279967087391458199)
              ·
                refine ⟨1242007919950631087187299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 828005279967087391458199 1242007919950631087187299)
                ·
                  refine ⟨1863011879925946630780949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1242007919950631087187299 1863011879925946630780949)
                  ·
                    refine ⟨87328681871528748317857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1863011879925946630780949 87328681871528748317857)
                    ·
                      rfl

theorem cell22_255108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 2, 1, 1, 6].length) (baseStart_255108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_255108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_255108 prefixEnd_255108 := by exact prefixLift 255108
  have htrace : WordTrace (prefixWord ++ tailWord_255108) baseStart_255108 baseEnd_255108 := by
    simpa [prefixWord, tailWord_255108, baseEnd_255108] using wordTrace_append hprefix tailTrace_255108
  have hstable : (prefixWord ++ tailWord_255108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255108).length < 2 ^ (prefixWord ++ tailWord_255108).sum := by decide
  have hdescent : baseEnd_255108 < baseStart_255108 := by decide
  rcases family_descends (prefixWord ++ tailWord_255108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255174 : List Nat := [6, 1, 2, 2, 2, 9]
def baseStart_255174 : Nat := 118140960795 + 255174 * 2 ^ 59
def prefixEnd_255174 : Nat := 4983230072969 + 3 ^ 40 * 255174 * 2
def baseEnd_255174 : Nat := 1078410802720081187255

theorem tailTrace_255174 : CollatzResearch.WordTrace tailWord_255174 prefixEnd_255174 1078410802720081187255 := by
  unfold tailWord_255174
  simp only [CollatzResearch.WordTrace]
  refine ⟨290842511798614159209643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6204640251703768729805717 290842511798614159209643)
  ·
    refine ⟨436263767697921238814465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 290842511798614159209643 436263767697921238814465)
    ·
      refine ⟨327197825773440929110849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 436263767697921238814465 327197825773440929110849)
      ·
        refine ⟨245398369330080696833137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 327197825773440929110849 245398369330080696833137)
        ·
          refine ⟨184048776997560522624853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 245398369330080696833137 184048776997560522624853)
          ·
            refine ⟨1078410802720081187255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 184048776997560522624853 1078410802720081187255)
            ·
              rfl

theorem cell22_255174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 2, 9].length) (baseStart_255174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_255174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_255174 prefixEnd_255174 := by exact prefixLift 255174
  have htrace : WordTrace (prefixWord ++ tailWord_255174) baseStart_255174 baseEnd_255174 := by
    simpa [prefixWord, tailWord_255174, baseEnd_255174] using wordTrace_append hprefix tailTrace_255174
  have hstable : (prefixWord ++ tailWord_255174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255174).length < 2 ^ (prefixWord ++ tailWord_255174).sum := by decide
  have hdescent : baseEnd_255174 < baseStart_255174 := by decide
  rcases family_descends (prefixWord ++ tailWord_255174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255189 : List Nat := [1, 3, 2, 4, 1, 2, 1, 4, 1, 3]
def baseStart_255189 : Nat := 118140960795 + 255189 * 2 ^ 59
def prefixEnd_255189 : Nat := 4983230072969 + 3 ^ 40 * 255189 * 2
def baseEnd_255189 : Nat := 87356409826871537042609

theorem tailTrace_255189 : CollatzResearch.WordTrace tailWord_255189 prefixEnd_255189 87356409826871537042609 := by
  unfold tailWord_255189
  simp only [CollatzResearch.WordTrace]
  refine ⟨9307507472501310656504621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6205004981667540437669747 9307507472501310656504621)
  ·
    refine ⟨3490315302187991496189233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9307507472501310656504621 3490315302187991496189233)
    ·
      refine ⟨2617736476640993622141925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3490315302187991496189233 2617736476640993622141925)
      ·
        refine ⟨490825589370186304151611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2617736476640993622141925 490825589370186304151611)
        ·
          refine ⟨736238384055279456227417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490825589370186304151611 736238384055279456227417)
          ·
            refine ⟨552178788041459592170563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 736238384055279456227417 552178788041459592170563)
            ·
              refine ⟨828268182062189388255845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552178788041459592170563 828268182062189388255845)
              ·
                refine ⟨155300284136660510297971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 828268182062189388255845 155300284136660510297971)
                ·
                  refine ⟨232950426204990765446957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155300284136660510297971 232950426204990765446957)
                  ·
                    refine ⟨87356409826871537042609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 232950426204990765446957 87356409826871537042609)
                    ·
                      rfl

theorem cell22_255189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_255189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_255189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_255189 prefixEnd_255189 := by exact prefixLift 255189
  have htrace : WordTrace (prefixWord ++ tailWord_255189) baseStart_255189 baseEnd_255189 := by
    simpa [prefixWord, tailWord_255189, baseEnd_255189] using wordTrace_append hprefix tailTrace_255189
  have hstable : (prefixWord ++ tailWord_255189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255189).length < 2 ^ (prefixWord ++ tailWord_255189).sum := by decide
  have hdescent : baseEnd_255189 < baseStart_255189 := by decide
  rcases family_descends (prefixWord ++ tailWord_255189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255277 : List Nat := [1, 5, 3, 1, 1, 1, 2, 1, 1, 6]
def baseStart_255277 : Nat := 118140960795 + 255277 * 2 ^ 59
def prefixEnd_255277 : Nat := 4983230072969 + 3 ^ 40 * 255277 * 2
def baseEnd_255277 : Nat := 87386534025268640842339

theorem tailTrace_255277 : CollatzResearch.WordTrace tailWord_255277 prefixEnd_255277 87386534025268640842339 := by
  unfold tailWord_255277
  simp only [CollatzResearch.WordTrace]
  refine ⟨9310717096182501685708085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6207144730788334457138723 9310717096182501685708085)
  ·
    refine ⟨872879727767109533035133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 9310717096182501685708085 872879727767109533035133)
    ·
      refine ⟨327329897912666074888175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 872879727767109533035133 327329897912666074888175)
      ·
        refine ⟨490994846868999112332263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 327329897912666074888175 490994846868999112332263)
        ·
          refine ⟨736492270303498668498395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 490994846868999112332263 736492270303498668498395)
          ·
            refine ⟨1104738405455248002747593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 736492270303498668498395 1104738405455248002747593)
            ·
              refine ⟨828553804091436002060695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1104738405455248002747593 828553804091436002060695)
              ·
                refine ⟨1242830706137154003091043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 828553804091436002060695 1242830706137154003091043)
                ·
                  refine ⟨1864246059205731004636565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1242830706137154003091043 1864246059205731004636565)
                  ·
                    refine ⟨87386534025268640842339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1864246059205731004636565 87386534025268640842339)
                    ·
                      rfl

theorem cell22_255277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 1, 1, 6].length) (baseStart_255277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_255277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_255277 prefixEnd_255277 := by exact prefixLift 255277
  have htrace : WordTrace (prefixWord ++ tailWord_255277) baseStart_255277 baseEnd_255277 := by
    simpa [prefixWord, tailWord_255277, baseEnd_255277] using wordTrace_append hprefix tailTrace_255277
  have hstable : (prefixWord ++ tailWord_255277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255277).length < 2 ^ (prefixWord ++ tailWord_255277).sum := by decide
  have hdescent : baseEnd_255277 < baseStart_255277 := by decide
  rcases family_descends (prefixWord ++ tailWord_255277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255288 : List Nat := [2, 1, 2, 1, 3, 1, 1, 2, 1, 8]
def baseStart_255288 : Nat := 118140960795 + 255288 * 2 ^ 59
def prefixEnd_255288 : Nat := 4983230072969 + 3 ^ 40 * 255288 * 2
def baseEnd_255288 : Nat := 87390299550068278817305

theorem tailTrace_255288 : CollatzResearch.WordTrace tailWord_255288 prefixEnd_255288 87390299550068278817305 := by
  unfold tailWord_255288
  simp only [CollatzResearch.WordTrace]
  refine ⟨4655559149571325282179259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6207412199428433709572345 4655559149571325282179259)
  ·
    refine ⟨6983338724356987923268889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4655559149571325282179259 6983338724356987923268889)
    ·
      refine ⟨5237504043267740942451667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6983338724356987923268889 5237504043267740942451667)
      ·
        refine ⟨7856256064901611413677501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5237504043267740942451667 7856256064901611413677501)
        ·
          refine ⟨2946096024338104280129063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7856256064901611413677501 2946096024338104280129063)
          ·
            refine ⟨4419144036507156420193595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2946096024338104280129063 4419144036507156420193595)
            ·
              refine ⟨6628716054760734630290393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4419144036507156420193595 6628716054760734630290393)
              ·
                refine ⟨4971537041070550972717795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6628716054760734630290393 4971537041070550972717795)
                ·
                  refine ⟨7457305561605826459076693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4971537041070550972717795 7457305561605826459076693)
                  ·
                    refine ⟨87390299550068278817305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 7457305561605826459076693 87390299550068278817305)
                    ·
                      rfl

theorem cell22_255288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 2, 1, 8].length) (baseStart_255288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_255288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_255288 prefixEnd_255288 := by exact prefixLift 255288
  have htrace : WordTrace (prefixWord ++ tailWord_255288) baseStart_255288 baseEnd_255288 := by
    simpa [prefixWord, tailWord_255288, baseEnd_255288] using wordTrace_append hprefix tailTrace_255288
  have hstable : (prefixWord ++ tailWord_255288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255288).length < 2 ^ (prefixWord ++ tailWord_255288).sum := by decide
  have hdescent : baseEnd_255288 < baseStart_255288 := by decide
  rcases family_descends (prefixWord ++ tailWord_255288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255309 : List Nat := [1, 6, 1, 3, 1, 1, 2, 7]
def baseStart_255309 : Nat := 118140960795 + 255309 * 2 ^ 59
def prefixEnd_255309 : Nat := 4983230072969 + 3 ^ 40 * 255309 * 2
def baseEnd_255309 : Nat := 9710832031025691560249

theorem tailTrace_255309 : CollatzResearch.WordTrace tailWord_255309 prefixEnd_255309 9710832031025691560249 := by
  unfold tailWord_255309
  simp only [CollatzResearch.WordTrace]
  refine ⟨9311884232066571150872981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6207922821377714100581987 9311884232066571150872981)
  ·
    refine ⟨436494573378120522697171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 9311884232066571150872981 436494573378120522697171)
    ·
      refine ⟨654741860067180784045757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 436494573378120522697171 654741860067180784045757)
      ·
        refine ⟨245528197525192794017159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 654741860067180784045757 245528197525192794017159)
        ·
          refine ⟨368292296287789191025739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 245528197525192794017159 368292296287789191025739)
          ·
            refine ⟨552438444431683786538609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368292296287789191025739 552438444431683786538609)
            ·
              refine ⟨414328833323762839903957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 552438444431683786538609 414328833323762839903957)
              ·
                refine ⟨9710832031025691560249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 414328833323762839903957 9710832031025691560249)
                ·
                  rfl

theorem cell22_255309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 7].length) (baseStart_255309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_255309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_255309 prefixEnd_255309 := by exact prefixLift 255309
  have htrace : WordTrace (prefixWord ++ tailWord_255309) baseStart_255309 baseEnd_255309 := by
    simpa [prefixWord, tailWord_255309, baseEnd_255309] using wordTrace_append hprefix tailTrace_255309
  have hstable : (prefixWord ++ tailWord_255309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255309).length < 2 ^ (prefixWord ++ tailWord_255309).sum := by decide
  have hdescent : baseEnd_255309 < baseStart_255309 := by decide
  rcases family_descends (prefixWord ++ tailWord_255309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255320 : List Nat := [2, 1, 2, 2, 1, 1, 5, 3, 5]
def baseStart_255320 : Nat := 118140960795 + 255320 * 2 ^ 59
def prefixEnd_255320 : Nat := 4983230072969 + 3 ^ 40 * 255320 * 2
def baseEnd_255320 : Nat := 29133751268010287339069

theorem tailTrace_255320 : CollatzResearch.WordTrace tailWord_255320 prefixEnd_255320 29133751268010287339069 := by
  unfold tailWord_255320
  simp only [CollatzResearch.WordTrace]
  refine ⟨4656142717513360014761707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6208190290017813353015609 4656142717513360014761707)
  ·
    refine ⟨6984214076270040022142561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4656142717513360014761707 6984214076270040022142561)
    ·
      refine ⟨5238160557202530016606921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6984214076270040022142561 5238160557202530016606921)
      ·
        refine ⟨3928620417901897512455191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5238160557202530016606921 3928620417901897512455191)
        ·
          refine ⟨5892930626852846268682787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3928620417901897512455191 5892930626852846268682787)
          ·
            refine ⟨8839395940279269403024181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5892930626852846268682787 8839395940279269403024181)
            ·
              refine ⟨828693369401181506533517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 8839395940279269403024181 828693369401181506533517)
              ·
                refine ⟨310760013525443064950069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 828693369401181506533517 310760013525443064950069)
                ·
                  refine ⟨29133751268010287339069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 310760013525443064950069 29133751268010287339069)
                  ·
                    rfl

theorem cell22_255320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 5, 3, 5].length) (baseStart_255320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_255320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_255320 prefixEnd_255320 := by exact prefixLift 255320
  have htrace : WordTrace (prefixWord ++ tailWord_255320) baseStart_255320 baseEnd_255320 := by
    simpa [prefixWord, tailWord_255320, baseEnd_255320] using wordTrace_append hprefix tailTrace_255320
  have hstable : (prefixWord ++ tailWord_255320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255320).length < 2 ^ (prefixWord ++ tailWord_255320).sum := by decide
  have hdescent : baseEnd_255320 < baseStart_255320 := by decide
  rcases family_descends (prefixWord ++ tailWord_255320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255395 : List Nat := [1, 1, 1, 4, 1, 3, 3, 1, 1, 6]
def baseStart_255395 : Nat := 118140960795 + 255395 * 2 ^ 59
def prefixEnd_255395 : Nat := 4983230072969 + 3 ^ 40 * 255395 * 2
def baseEnd_255395 : Nat := 87426927836755666391977

theorem tailTrace_255395 : CollatzResearch.WordTrace tailWord_255395 prefixEnd_255395 87426927836755666391977 := by
  unfold tailWord_255395
  simp only [CollatzResearch.WordTrace]
  refine ⟨9315020909755007838503639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6210013939836671892335759 9315020909755007838503639)
  ·
    refine ⟨13972531364632511757755459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9315020909755007838503639 13972531364632511757755459)
    ·
      refine ⟨20958797046948767636633189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 13972531364632511757755459 20958797046948767636633189)
      ·
        refine ⟨3929774446302893931868723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 20958797046948767636633189 3929774446302893931868723)
        ·
          refine ⟨5894661669454340897803085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3929774446302893931868723 5894661669454340897803085)
          ·
            refine ⟨2210498126045377836676157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5894661669454340897803085 2210498126045377836676157)
            ·
              refine ⟨828936797267016688753559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2210498126045377836676157 828936797267016688753559)
              ·
                refine ⟨1243405195900525033130339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 828936797267016688753559 1243405195900525033130339)
                ·
                  refine ⟨1865107793850787549695509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1243405195900525033130339 1865107793850787549695509)
                  ·
                    refine ⟨87426927836755666391977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1865107793850787549695509 87426927836755666391977)
                    ·
                      rfl

theorem cell22_255395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 3, 1, 1, 6].length) (baseStart_255395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_255395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_255395 prefixEnd_255395 := by exact prefixLift 255395
  have htrace : WordTrace (prefixWord ++ tailWord_255395) baseStart_255395 baseEnd_255395 := by
    simpa [prefixWord, tailWord_255395, baseEnd_255395] using wordTrace_append hprefix tailTrace_255395
  have hstable : (prefixWord ++ tailWord_255395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255395).length < 2 ^ (prefixWord ++ tailWord_255395).sum := by decide
  have hdescent : baseEnd_255395 < baseStart_255395 := by decide
  rcases family_descends (prefixWord ++ tailWord_255395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255399 : List Nat := [1, 1, 6, 1, 1, 1, 4, 3, 4]
def baseStart_255399 : Nat := 118140960795 + 255399 * 2 ^ 59
def prefixEnd_255399 : Nat := 4983230072969 + 3 ^ 40 * 255399 * 2
def baseEnd_255399 : Nat := 29142765706166996430655

theorem tailTrace_255399 : CollatzResearch.WordTrace tailWord_255399 prefixEnd_255399 29142765706166996430655 := by
  unfold tailWord_255399
  simp only [CollatzResearch.WordTrace]
  refine ⟨9315166801740516521649251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6210111201160344347766167 9315166801740516521649251)
  ·
    refine ⟨13972750202610774782473877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9315166801740516521649251 13972750202610774782473877)
    ·
      refine ⟨654972665747380067928463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 13972750202610774782473877 654972665747380067928463)
      ·
        refine ⟨982458998621070101892695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 654972665747380067928463 982458998621070101892695)
        ·
          refine ⟨1473688497931605152839043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 982458998621070101892695 1473688497931605152839043)
          ·
            refine ⟨2210532746897407729258565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1473688497931605152839043 2210532746897407729258565)
            ·
              refine ⟨414474890043263949235981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2210532746897407729258565 414474890043263949235981)
              ·
                refine ⟨155428083766223980963493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 414474890043263949235981 155428083766223980963493)
                ·
                  refine ⟨29142765706166996430655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155428083766223980963493 29142765706166996430655)
                  ·
                    rfl

theorem cell22_255399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 4, 3, 4].length) (baseStart_255399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_255399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_255399 prefixEnd_255399 := by exact prefixLift 255399
  have htrace : WordTrace (prefixWord ++ tailWord_255399) baseStart_255399 baseEnd_255399 := by
    simpa [prefixWord, tailWord_255399, baseEnd_255399] using wordTrace_append hprefix tailTrace_255399
  have hstable : (prefixWord ++ tailWord_255399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255399).length < 2 ^ (prefixWord ++ tailWord_255399).sum := by decide
  have hdescent : baseEnd_255399 < baseStart_255399 := by decide
  rcases family_descends (prefixWord ++ tailWord_255399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255455 : List Nat := [1, 1, 2, 3, 3, 1, 1, 1, 9]
def baseStart_255455 : Nat := 118140960795 + 255455 * 2 ^ 59
def prefixEnd_255455 : Nat := 4983230072969 + 3 ^ 40 * 255455 * 2
def baseEnd_255455 : Nat := 29149155687645169963931

theorem tailTrace_255455 : CollatzResearch.WordTrace tailWord_255455 prefixEnd_255455 29149155687645169963931 := by
  unfold tailWord_255455
  simp only [CollatzResearch.WordTrace]
  refine ⟨9317209289537638085687819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6211472859691758723791879 9317209289537638085687819)
  ·
    refine ⟨13975813934306457128531729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9317209289537638085687819 13975813934306457128531729)
    ·
      refine ⟨10481860450729842846398797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13975813934306457128531729 10481860450729842846398797)
      ·
        refine ⟨3930697669023691067399549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10481860450729842846398797 3930697669023691067399549)
        ·
          refine ⟨1474011625883884150274831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3930697669023691067399549 1474011625883884150274831)
          ·
            refine ⟨2211017438825826225412247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1474011625883884150274831 2211017438825826225412247)
            ·
              refine ⟨3316526158238739338118371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2211017438825826225412247 3316526158238739338118371)
              ·
                refine ⟨4974789237358109007177557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3316526158238739338118371 4974789237358109007177557)
                ·
                  refine ⟨29149155687645169963931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4974789237358109007177557 29149155687645169963931)
                  ·
                    rfl

theorem cell22_255455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 1, 9].length) (baseStart_255455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_255455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_255455 prefixEnd_255455 := by exact prefixLift 255455
  have htrace : WordTrace (prefixWord ++ tailWord_255455) baseStart_255455 baseEnd_255455 := by
    simpa [prefixWord, tailWord_255455, baseEnd_255455] using wordTrace_append hprefix tailTrace_255455
  have hstable : (prefixWord ++ tailWord_255455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255455).length < 2 ^ (prefixWord ++ tailWord_255455).sum := by decide
  have hdescent : baseEnd_255455 < baseStart_255455 := by decide
  rcases family_descends (prefixWord ++ tailWord_255455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255489 : List Nat := [1, 2, 4, 1, 4, 1, 1, 3, 5]
def baseStart_255489 : Nat := 118140960795 + 255489 * 2 ^ 59
def prefixEnd_255489 : Nat := 4983230072969 + 3 ^ 40 * 255489 * 2
def baseEnd_255489 : Nat := 29153035319256918180563

theorem tailTrace_255489 : CollatzResearch.WordTrace tailWord_255489 prefixEnd_255489 29153035319256918180563 := by
  unfold tailWord_255489
  simp only [CollatzResearch.WordTrace]
  refine ⟨9318449371414461892425521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6212299580942974594950347 9318449371414461892425521)
  ·
    refine ⟨6988837028560846419319141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9318449371414461892425521 6988837028560846419319141)
    ·
      refine ⟨1310406942855158703622339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 6988837028560846419319141 1310406942855158703622339)
      ·
        refine ⟨1965610414282738055433509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1310406942855158703622339 1965610414282738055433509)
        ·
          refine ⟨368551952678013385393783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1965610414282738055433509 368551952678013385393783)
          ·
            refine ⟨552827929017020078090675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 368551952678013385393783 552827929017020078090675)
            ·
              refine ⟨829241893525530117136013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 552827929017020078090675 829241893525530117136013)
              ·
                refine ⟨310965710072073793926005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 829241893525530117136013 310965710072073793926005)
                ·
                  refine ⟨29153035319256918180563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 310965710072073793926005 29153035319256918180563)
                  ·
                    rfl

theorem cell22_255489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 1, 3, 5].length) (baseStart_255489 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_255489 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_255489 prefixEnd_255489 := by exact prefixLift 255489
  have htrace : WordTrace (prefixWord ++ tailWord_255489) baseStart_255489 baseEnd_255489 := by
    simpa [prefixWord, tailWord_255489, baseEnd_255489] using wordTrace_append hprefix tailTrace_255489
  have hstable : (prefixWord ++ tailWord_255489).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255489).length < 2 ^ (prefixWord ++ tailWord_255489).sum := by decide
  have hdescent : baseEnd_255489 < baseStart_255489 := by decide
  rcases family_descends (prefixWord ++ tailWord_255489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255564 : List Nat := [2, 2, 1, 3, 1, 3, 3, 1, 2, 4]
def baseStart_255564 : Nat := 118140960795 + 255564 * 2 ^ 59
def prefixEnd_255564 : Nat := 4983230072969 + 3 ^ 40 * 255564 * 2
def baseEnd_255564 : Nat := 87484779990495558916459

theorem tailTrace_255564 : CollatzResearch.WordTrace tailWord_255564 prefixEnd_255564 87484779990495558916459 := by
  unfold tailWord_255564
  simp only [CollatzResearch.WordTrace]
  refine ⟨4660592423071374850702873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6214123230761833134270497 4660592423071374850702873)
  ·
    refine ⟨3495444317303531138027155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4660592423071374850702873 3495444317303531138027155)
    ·
      refine ⟨5243166475955296707040733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3495444317303531138027155 5243166475955296707040733)
      ·
        refine ⟨1966187428483236265140275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5243166475955296707040733 1966187428483236265140275)
        ·
          refine ⟨2949281142724854397710413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1966187428483236265140275 2949281142724854397710413)
          ·
            refine ⟨1105980428521820399141405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2949281142724854397710413 1105980428521820399141405)
            ·
              refine ⟨414742660695682649678027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1105980428521820399141405 414742660695682649678027)
              ·
                refine ⟨622113991043523974517041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 414742660695682649678027 622113991043523974517041)
                ·
                  refine ⟨466585493282642980887781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 622113991043523974517041 466585493282642980887781)
                  ·
                    refine ⟨87484779990495558916459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 466585493282642980887781 87484779990495558916459)
                    ·
                      rfl

theorem cell22_255564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_255564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_255564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_255564 prefixEnd_255564 := by exact prefixLift 255564
  have htrace : WordTrace (prefixWord ++ tailWord_255564) baseStart_255564 baseEnd_255564 := by
    simpa [prefixWord, tailWord_255564, baseEnd_255564] using wordTrace_append hprefix tailTrace_255564
  have hstable : (prefixWord ++ tailWord_255564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255564).length < 2 ^ (prefixWord ++ tailWord_255564).sum := by decide
  have hdescent : baseEnd_255564 < baseStart_255564 := by decide
  rcases family_descends (prefixWord ++ tailWord_255564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255671 : List Nat := [1, 1, 3, 1, 5, 1, 3, 2, 1, 4]
def baseStart_255671 : Nat := 118140960795 + 255671 * 2 ^ 59
def prefixEnd_255671 : Nat := 4983230072969 + 3 ^ 40 * 255671 * 2
def baseEnd_255671 : Nat := 87521408277182946491131

theorem tailTrace_255671 : CollatzResearch.WordTrace tailWord_255671 prefixEnd_255671 87521408277182946491131 := by
  unfold tailWord_255671
  simp only [CollatzResearch.WordTrace]
  refine ⟨9325087456755106975550867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6216724971170071317033911 9325087456755106975550867)
  ·
    refine ⟨13987631185132660463326301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9325087456755106975550867 13987631185132660463326301)
    ·
      refine ⟨5245361694424747673747363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 13987631185132660463326301 5245361694424747673747363)
      ·
        refine ⟨7868042541637121510621045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5245361694424747673747363 7868042541637121510621045)
        ·
          refine ⟨737628988278480141620723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 7868042541637121510621045 737628988278480141620723)
          ·
            refine ⟨1106443482417720212431085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 737628988278480141620723 1106443482417720212431085)
            ·
              refine ⟨414916305906645079661657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1106443482417720212431085 414916305906645079661657)
              ·
                refine ⟨311187229429983809746243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 414916305906645079661657 311187229429983809746243)
                ·
                  refine ⟨466780844144975714619365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 311187229429983809746243 466780844144975714619365)
                  ·
                    refine ⟨87521408277182946491131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 466780844144975714619365 87521408277182946491131)
                    ·
                      rfl

theorem cell22_255671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_255671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_255671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_255671 prefixEnd_255671 := by exact prefixLift 255671
  have htrace : WordTrace (prefixWord ++ tailWord_255671) baseStart_255671 baseEnd_255671 := by
    simpa [prefixWord, tailWord_255671, baseEnd_255671] using wordTrace_append hprefix tailTrace_255671
  have hstable : (prefixWord ++ tailWord_255671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255671).length < 2 ^ (prefixWord ++ tailWord_255671).sum := by decide
  have hdescent : baseEnd_255671 < baseStart_255671 := by decide
  rcases family_descends (prefixWord ++ tailWord_255671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255697 : List Nat := [1, 2, 2, 1, 2, 14]
def baseStart_255697 : Nat := 118140960795 + 255697 * 2 ^ 59
def prefixEnd_255697 : Nat := 4983230072969 + 3 ^ 40 * 255697 * 2
def baseEnd_255697 : Nat := 1080621093932438831371

theorem tailTrace_255697 : CollatzResearch.WordTrace tailWord_255697 prefixEnd_255697 1080621093932438831371 := by
  unfold tailWord_255697
  simp only [CollatzResearch.WordTrace]
  refine ⟨9326035754660913415997345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6217357169773942277331563 9326035754660913415997345)
  ·
    refine ⟨6994526815995685061998009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9326035754660913415997345 6994526815995685061998009)
    ·
      refine ⟨5245895111996763796498507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6994526815995685061998009 5245895111996763796498507)
      ·
        refine ⟨7868842667995145694747761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5245895111996763796498507 7868842667995145694747761)
        ·
          refine ⟨5901632000996359271060821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7868842667995145694747761 5901632000996359271060821)
          ·
            refine ⟨1080621093932438831371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 14 5901632000996359271060821 1080621093932438831371)
            ·
              rfl

theorem cell22_255697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 14].length) (baseStart_255697 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_255697 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_255697 prefixEnd_255697 := by exact prefixLift 255697
  have htrace : WordTrace (prefixWord ++ tailWord_255697) baseStart_255697 baseEnd_255697 := by
    simpa [prefixWord, tailWord_255697, baseEnd_255697] using wordTrace_append hprefix tailTrace_255697
  have hstable : (prefixWord ++ tailWord_255697).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255697).length < 2 ^ (prefixWord ++ tailWord_255697).sum := by decide
  have hdescent : baseEnd_255697 < baseStart_255697 := by decide
  rcases family_descends (prefixWord ++ tailWord_255697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255759 : List Nat := [1, 1, 2, 1, 1, 1, 4, 6, 5]
def baseStart_255759 : Nat := 118140960795 + 255759 * 2 ^ 59
def prefixEnd_255759 : Nat := 4983230072969 + 3 ^ 40 * 255759 * 2
def baseEnd_255759 : Nat := 29183844158526683430287

theorem tailTrace_255759 : CollatzResearch.WordTrace tailWord_255759 prefixEnd_255759 29183844158526683430287 := by
  unfold tailWord_255759
  simp only [CollatzResearch.WordTrace]
  refine ⟨9328297080436298004754331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6218864720290865336502887 9328297080436298004754331)
  ·
    refine ⟨13992445620654447007131497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9328297080436298004754331 13992445620654447007131497)
    ·
      refine ⟨10494334215490835255348623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 13992445620654447007131497 10494334215490835255348623)
      ·
        refine ⟨15741501323236252883022935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10494334215490835255348623 15741501323236252883022935)
        ·
          refine ⟨23612251984854379324534403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15741501323236252883022935 23612251984854379324534403)
          ·
            refine ⟨35418377977281568986801605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23612251984854379324534403 35418377977281568986801605)
            ·
              refine ⟨6640945870740294185025301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 35418377977281568986801605 6640945870740294185025301)
              ·
                refine ⟨311294337690951289923061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6640945870740294185025301 311294337690951289923061)
                ·
                  refine ⟨29183844158526683430287, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 311294337690951289923061 29183844158526683430287)
                  ·
                    rfl

theorem cell22_255759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 6, 5].length) (baseStart_255759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_255759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_255759 prefixEnd_255759 := by exact prefixLift 255759
  have htrace : WordTrace (prefixWord ++ tailWord_255759) baseStart_255759 baseEnd_255759 := by
    simpa [prefixWord, tailWord_255759, baseEnd_255759] using wordTrace_append hprefix tailTrace_255759
  have hstable : (prefixWord ++ tailWord_255759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255759).length < 2 ^ (prefixWord ++ tailWord_255759).sum := by decide
  have hdescent : baseEnd_255759 < baseStart_255759 := by decide
  rcases family_descends (prefixWord ++ tailWord_255759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255797 : List Nat := [1, 3, 3, 1, 4, 2, 1, 3, 1, 3]
def baseStart_255797 : Nat := 118140960795 + 255797 * 2 ^ 59
def prefixEnd_255797 : Nat := 4983230072969 + 3 ^ 40 * 255797 * 2
def baseEnd_255797 : Nat := 87564540652160617840745

theorem tailTrace_255797 : CollatzResearch.WordTrace tailWord_255797 prefixEnd_255797 87564540652160617840745 := by
  unfold tailWord_255797
  simp only [CollatzResearch.WordTrace]
  refine ⟨9329683054298630494637645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6219788702865753663091763 9329683054298630494637645)
  ·
    refine ⟨3498631145361986435489117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9329683054298630494637645 3498631145361986435489117)
    ·
      refine ⟨1311986679510744913308419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3498631145361986435489117 1311986679510744913308419)
      ·
        refine ⟨1967980019266117369962629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1311986679510744913308419 1967980019266117369962629)
        ·
          refine ⟨368996253612397006867993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1967980019266117369962629 368996253612397006867993)
          ·
            refine ⟨276747190209297755150995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 368996253612397006867993 276747190209297755150995)
            ·
              refine ⟨415120785313946632726493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 276747190209297755150995 415120785313946632726493)
              ·
                refine ⟨155670294492729987272435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 415120785313946632726493 155670294492729987272435)
                ·
                  refine ⟨233505441739094980908653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 155670294492729987272435 233505441739094980908653)
                  ·
                    refine ⟨87564540652160617840745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 233505441739094980908653 87564540652160617840745)
                    ·
                      rfl

theorem cell22_255797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 4, 2, 1, 3, 1, 3].length) (baseStart_255797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_255797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_255797 prefixEnd_255797 := by exact prefixLift 255797
  have htrace : WordTrace (prefixWord ++ tailWord_255797) baseStart_255797 baseEnd_255797 := by
    simpa [prefixWord, tailWord_255797, baseEnd_255797] using wordTrace_append hprefix tailTrace_255797
  have hstable : (prefixWord ++ tailWord_255797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255797).length < 2 ^ (prefixWord ++ tailWord_255797).sum := by decide
  have hdescent : baseEnd_255797 < baseStart_255797 := by decide
  rcases family_descends (prefixWord ++ tailWord_255797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255804 : List Nat := [2, 2, 2, 2, 1, 1, 2, 2, 8]
def baseStart_255804 : Nat := 118140960795 + 255804 * 2 ^ 59
def prefixEnd_255804 : Nat := 4983230072969 + 3 ^ 40 * 255804 * 2
def baseEnd_255804 : Nat := 29188978965071644305241

theorem tailTrace_255804 : CollatzResearch.WordTrace tailWord_255804 prefixEnd_255804 29188978965071644305241 := by
  unfold tailWord_255804
  simp only [CollatzResearch.WordTrace]
  refine ⟨4664969182636635345071233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6219958910182180460094977 4664969182636635345071233)
  ·
    refine ⟨3498726886977476508803425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4664969182636635345071233 3498726886977476508803425)
    ·
      refine ⟨2624045165233107381602569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3498726886977476508803425 2624045165233107381602569)
      ·
        refine ⟨1968033873924830536201927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2624045165233107381602569 1968033873924830536201927)
        ·
          refine ⟨2952050810887245804302891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1968033873924830536201927 2952050810887245804302891)
          ·
            refine ⟨4428076216330868706454337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2952050810887245804302891 4428076216330868706454337)
            ·
              refine ⟨3321057162248151529840753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4428076216330868706454337 3321057162248151529840753)
              ·
                refine ⟨2490792871686113647380565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3321057162248151529840753 2490792871686113647380565)
                ·
                  refine ⟨29188978965071644305241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2490792871686113647380565 29188978965071644305241)
                  ·
                    rfl

theorem cell22_255804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 2, 2, 8].length) (baseStart_255804 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_255804 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_255804 prefixEnd_255804 := by exact prefixLift 255804
  have htrace : WordTrace (prefixWord ++ tailWord_255804) baseStart_255804 baseEnd_255804 := by
    simpa [prefixWord, tailWord_255804, baseEnd_255804] using wordTrace_append hprefix tailTrace_255804
  have hstable : (prefixWord ++ tailWord_255804).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255804).length < 2 ^ (prefixWord ++ tailWord_255804).sum := by decide
  have hdescent : baseEnd_255804 < baseStart_255804 := by decide
  rcases family_descends (prefixWord ++ tailWord_255804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255864 : List Nat := [2, 1, 2, 1, 1, 1, 1, 2, 4, 7]
def baseStart_255864 : Nat := 118140960795 + 255864 * 2 ^ 59
def prefixEnd_255864 : Nat := 4983230072969 + 3 ^ 40 * 255864 * 2
def baseEnd_255864 : Nat := 87587476121394776415539

theorem tailTrace_255864 : CollatzResearch.WordTrace tailWord_255864 prefixEnd_255864 87587476121394776415539 := by
  unfold tailWord_255864
  simp only [CollatzResearch.WordTrace]
  refine ⟨4666063372527950468663323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6221417830037267291551097 4666063372527950468663323)
  ·
    refine ⟨6999095058791925702994985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4666063372527950468663323 6999095058791925702994985)
    ·
      refine ⟨5249321294093944277246239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 6999095058791925702994985 5249321294093944277246239)
      ·
        refine ⟨7873981941140916415869359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5249321294093944277246239 7873981941140916415869359)
        ·
          refine ⟨11810972911711374623804039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7873981941140916415869359 11810972911711374623804039)
          ·
            refine ⟨17716459367567061935706059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11810972911711374623804039 17716459367567061935706059)
            ·
              refine ⟨26574689051350592903559089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17716459367567061935706059 26574689051350592903559089)
              ·
                refine ⟨19931016788512944677669317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 26574689051350592903559089 19931016788512944677669317)
                ·
                  refine ⟨3737065647846177127062997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 19931016788512944677669317 3737065647846177127062997)
                  ·
                    refine ⟨87587476121394776415539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3737065647846177127062997 87587476121394776415539)
                    ·
                      rfl

theorem cell22_255864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 2, 4, 7].length) (baseStart_255864 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_255864 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_255864 prefixEnd_255864 := by exact prefixLift 255864
  have htrace : WordTrace (prefixWord ++ tailWord_255864) baseStart_255864 baseEnd_255864 := by
    simpa [prefixWord, tailWord_255864, baseEnd_255864] using wordTrace_append hprefix tailTrace_255864
  have hstable : (prefixWord ++ tailWord_255864).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255864).length < 2 ^ (prefixWord ++ tailWord_255864).sum := by decide
  have hdescent : baseEnd_255864 < baseStart_255864 := by decide
  rcases family_descends (prefixWord ++ tailWord_255864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255898 : List Nat := [3, 1, 1, 4, 2, 1, 1, 1, 5, 3]
def baseStart_255898 : Nat := 118140960795 + 255898 * 2 ^ 59
def prefixEnd_255898 : Nat := 4983230072969 + 3 ^ 40 * 255898 * 2
def baseEnd_255898 : Nat := 87599115016230021065435

theorem tailTrace_255898 : CollatzResearch.WordTrace tailWord_255898 prefixEnd_255898 87599115016230021065435 := by
  unfold tailWord_255898
  simp only [CollatzResearch.WordTrace]
  refine ⟨2333341706733181186016087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6222244551288483162709565 2333341706733181186016087)
  ·
    refine ⟨3500012560099771779024131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2333341706733181186016087 3500012560099771779024131)
    ·
      refine ⟨5250018840149657668536197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3500012560099771779024131 5250018840149657668536197)
      ·
        refine ⟨984378532528060812850537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5250018840149657668536197 984378532528060812850537)
        ·
          refine ⟨738283899396045609637903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 984378532528060812850537 738283899396045609637903)
          ·
            refine ⟨1107425849094068414456855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 738283899396045609637903 1107425849094068414456855)
            ·
              refine ⟨1661138773641102621685283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1107425849094068414456855 1661138773641102621685283)
              ·
                refine ⟨2491708160461653932527925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1661138773641102621685283 2491708160461653932527925)
                ·
                  refine ⟨233597640043280056174493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2491708160461653932527925 233597640043280056174493)
                  ·
                    refine ⟨87599115016230021065435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 233597640043280056174493 87599115016230021065435)
                    ·
                      rfl

theorem cell22_255898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 1, 5, 3].length) (baseStart_255898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_255898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_255898 prefixEnd_255898 := by exact prefixLift 255898
  have htrace : WordTrace (prefixWord ++ tailWord_255898) baseStart_255898 baseEnd_255898 := by
    simpa [prefixWord, tailWord_255898, baseEnd_255898] using wordTrace_append hprefix tailTrace_255898
  have hstable : (prefixWord ++ tailWord_255898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255898).length < 2 ^ (prefixWord ++ tailWord_255898).sum := by decide
  have hdescent : baseEnd_255898 < baseStart_255898 := by decide
  rcases family_descends (prefixWord ++ tailWord_255898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255932 : List Nat := [2, 2, 2, 5, 1, 1, 2, 1, 3, 3]
def baseStart_255932 : Nat := 118140960795 + 255932 * 2 ^ 59
def prefixEnd_255932 : Nat := 4983230072969 + 3 ^ 40 * 255932 * 2
def baseEnd_255932 : Nat := 87610753911065265715331

theorem tailTrace_255932 : CollatzResearch.WordTrace tailWord_255932 prefixEnd_255932 87610753911065265715331 := by
  unfold tailWord_255932
  simp only [CollatzResearch.WordTrace]
  refine ⟨4667303454404774275401025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6223071272539699033868033 4667303454404774275401025)
  ·
    refine ⟨3500477590803580706550769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4667303454404774275401025 3500477590803580706550769)
    ·
      refine ⟨2625358193102685529913077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3500477590803580706550769 2625358193102685529913077)
      ·
        refine ⟨246127330603376768429351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 2625358193102685529913077 246127330603376768429351)
        ·
          refine ⟨369190995905065152644027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 246127330603376768429351 369190995905065152644027)
          ·
            refine ⟨553786493857597728966041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369190995905065152644027 553786493857597728966041)
            ·
              refine ⟨415339870393198296724531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 553786493857597728966041 415339870393198296724531)
              ·
                refine ⟨623009805589797445086797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415339870393198296724531 623009805589797445086797)
                ·
                  refine ⟨233628677096174041907549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 623009805589797445086797 233628677096174041907549)
                  ·
                    refine ⟨87610753911065265715331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 233628677096174041907549 87610753911065265715331)
                    ·
                      rfl

theorem cell22_255932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 1, 2, 1, 3, 3].length) (baseStart_255932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_255932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_255932 prefixEnd_255932 := by exact prefixLift 255932
  have htrace : WordTrace (prefixWord ++ tailWord_255932) baseStart_255932 baseEnd_255932 := by
    simpa [prefixWord, tailWord_255932, baseEnd_255932] using wordTrace_append hprefix tailTrace_255932
  have hstable : (prefixWord ++ tailWord_255932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255932).length < 2 ^ (prefixWord ++ tailWord_255932).sum := by decide
  have hdescent : baseEnd_255932 < baseStart_255932 := by decide
  rcases family_descends (prefixWord ++ tailWord_255932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_255941 : List Nat := [1, 3, 1, 1, 1, 1, 1, 6, 3, 4]
def baseStart_255941 : Nat := 118140960795 + 255941 * 2 ^ 59
def prefixEnd_255941 : Nat := 4983230072969 + 3 ^ 40 * 255941 * 2
def baseEnd_255941 : Nat := 87613834794992242240303

theorem tailTrace_255941 : CollatzResearch.WordTrace tailWord_255941 prefixEnd_255941 87613834794992242240303 := by
  unfold tailWord_255941
  simp only [CollatzResearch.WordTrace]
  refine ⟨9334935165776943087879677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6223290110517962058586451 9334935165776943087879677)
  ·
    refine ⟨3500600687166353657954879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9334935165776943087879677 3500600687166353657954879)
    ·
      refine ⟨5250901030749530486932319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3500600687166353657954879 5250901030749530486932319)
      ·
        refine ⟨7876351546124295730398479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5250901030749530486932319 7876351546124295730398479)
        ·
          refine ⟨11814527319186443595597719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7876351546124295730398479 11814527319186443595597719)
          ·
            refine ⟨17721790978779665393396579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11814527319186443595597719 17721790978779665393396579)
            ·
              refine ⟨26582686468169498090094869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17721790978779665393396579 26582686468169498090094869)
              ·
                refine ⟨1246063428195445222973197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 26582686468169498090094869 1246063428195445222973197)
                ·
                  refine ⟨467273785573291958614949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1246063428195445222973197 467273785573291958614949)
                  ·
                    refine ⟨87613834794992242240303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 467273785573291958614949 87613834794992242240303)
                    ·
                      rfl

theorem cell22_255941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 6, 3, 4].length) (baseStart_255941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_255941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_255941 prefixEnd_255941 := by exact prefixLift 255941
  have htrace : WordTrace (prefixWord ++ tailWord_255941) baseStart_255941 baseEnd_255941 := by
    simpa [prefixWord, tailWord_255941, baseEnd_255941] using wordTrace_append hprefix tailTrace_255941
  have hstable : (prefixWord ++ tailWord_255941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_255941).length < 2 ^ (prefixWord ++ tailWord_255941).sum := by decide
  have hdescent : baseEnd_255941 < baseStart_255941 := by decide
  rcases family_descends (prefixWord ++ tailWord_255941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256005 : List Nat := [1, 3, 1, 1, 2, 5, 1, 3, 2, 3]
def baseStart_256005 : Nat := 118140960795 + 256005 * 2 ^ 59
def prefixEnd_256005 : Nat := 4983230072969 + 3 ^ 40 * 256005 * 2
def baseEnd_256005 : Nat := 87635743302917408640107

theorem tailTrace_256005 : CollatzResearch.WordTrace tailWord_256005 prefixEnd_256005 87635743302917408640107 := by
  unfold tailWord_256005
  simp only [CollatzResearch.WordTrace]
  refine ⟨9337269437545082018209469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6224846291696721345472979 9337269437545082018209469)
  ·
    refine ⟨3501476039079405756828551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9337269437545082018209469 3501476039079405756828551)
    ·
      refine ⟨5252214058619108635242827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3501476039079405756828551 5252214058619108635242827)
      ·
        refine ⟨7878321087928662952864241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5252214058619108635242827 7878321087928662952864241)
        ·
          refine ⟨5908740815946497214648181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7878321087928662952864241 5908740815946497214648181)
          ·
            refine ⟨553944451494984113873267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5908740815946497214648181 553944451494984113873267)
            ·
              refine ⟨830916677242476170809901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 553944451494984113873267 830916677242476170809901)
              ·
                refine ⟨311593753965928564053713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 830916677242476170809901 311593753965928564053713)
                ·
                  refine ⟨233695315474446423040285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311593753965928564053713 233695315474446423040285)
                  ·
                    refine ⟨87635743302917408640107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 233695315474446423040285 87635743302917408640107)
                    ·
                      rfl

theorem cell22_256005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 1, 3, 2, 3].length) (baseStart_256005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_256005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_256005 prefixEnd_256005 := by exact prefixLift 256005
  have htrace : WordTrace (prefixWord ++ tailWord_256005) baseStart_256005 baseEnd_256005 := by
    simpa [prefixWord, tailWord_256005, baseEnd_256005] using wordTrace_append hprefix tailTrace_256005
  have hstable : (prefixWord ++ tailWord_256005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256005).length < 2 ^ (prefixWord ++ tailWord_256005).sum := by decide
  have hdescent : baseEnd_256005 < baseStart_256005 := by decide
  rcases family_descends (prefixWord ++ tailWord_256005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256039 : List Nat := [1, 1, 7, 1, 2, 1, 2, 2, 2, 3]
def baseStart_256039 : Nat := 118140960795 + 256039 * 2 ^ 59
def prefixEnd_256039 : Nat := 4983230072969 + 3 ^ 40 * 256039 * 2
def baseEnd_256039 : Nat := 87647382197752653290003

theorem tailTrace_256039 : CollatzResearch.WordTrace tailWord_256039 prefixEnd_256039 87647382197752653290003 := by
  unfold tailWord_256039
  simp only [CollatzResearch.WordTrace]
  refine ⟨9338509519421905824947171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6225673012947937216631447 9338509519421905824947171)
  ·
    refine ⟨14007764279132858737420757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9338509519421905824947171 14007764279132858737420757)
    ·
      refine ⟨328306975292176376658299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 14007764279132858737420757 328306975292176376658299)
      ·
        refine ⟨492460462938264564987449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 328306975292176376658299 492460462938264564987449)
        ·
          refine ⟨369345347203698423740587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492460462938264564987449 369345347203698423740587)
          ·
            refine ⟨554018020805547635610881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 369345347203698423740587 554018020805547635610881)
            ·
              refine ⟨415513515604160726708161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 554018020805547635610881 415513515604160726708161)
              ·
                refine ⟨311635136703120545031121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 415513515604160726708161 311635136703120545031121)
                ·
                  refine ⟨233726352527340408773341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 311635136703120545031121 233726352527340408773341)
                  ·
                    refine ⟨87647382197752653290003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 233726352527340408773341 87647382197752653290003)
                    ·
                      rfl

theorem cell22_256039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_256039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_256039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_256039 prefixEnd_256039 := by exact prefixLift 256039
  have htrace : WordTrace (prefixWord ++ tailWord_256039) baseStart_256039 baseEnd_256039 := by
    simpa [prefixWord, tailWord_256039, baseEnd_256039] using wordTrace_append hprefix tailTrace_256039
  have hstable : (prefixWord ++ tailWord_256039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256039).length < 2 ^ (prefixWord ++ tailWord_256039).sum := by decide
  have hdescent : baseEnd_256039 < baseStart_256039 := by decide
  rcases family_descends (prefixWord ++ tailWord_256039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256052 : List Nat := [2, 5, 1, 2, 2, 2, 1, 7]
def baseStart_256052 : Nat := 118140960795 + 256052 * 2 ^ 59
def prefixEnd_256052 : Nat := 4983230072969 + 3 ^ 40 * 256052 * 2
def baseEnd_256052 : Nat := 9739092484824994746107

theorem tailTrace_256052 : CollatzResearch.WordTrace tailWord_256052 prefixEnd_256052 9739092484824994746107 := by
  unfold tailWord_256052
  simp only [CollatzResearch.WordTrace]
  refine ⟨4669491834187404522585205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6225989112249872696780273 4669491834187404522585205)
  ·
    refine ⟨437764859455069173992363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4669491834187404522585205 437764859455069173992363)
    ·
      refine ⟨656647289182603760988545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 437764859455069173992363 656647289182603760988545)
      ·
        refine ⟨492485466886952820741409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 656647289182603760988545 492485466886952820741409)
        ·
          refine ⟨369364100165214615556057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 492485466886952820741409 369364100165214615556057)
          ·
            refine ⟨277023075123910961667043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 369364100165214615556057 277023075123910961667043)
            ·
              refine ⟨415534612685866442500565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277023075123910961667043 415534612685866442500565)
              ·
                refine ⟨9739092484824994746107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 415534612685866442500565 9739092484824994746107)
                ·
                  rfl

theorem cell22_256052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 2, 1, 7].length) (baseStart_256052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_256052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_256052 prefixEnd_256052 := by exact prefixLift 256052
  have htrace : WordTrace (prefixWord ++ tailWord_256052) baseStart_256052 baseEnd_256052 := by
    simpa [prefixWord, tailWord_256052, baseEnd_256052] using wordTrace_append hprefix tailTrace_256052
  have hstable : (prefixWord ++ tailWord_256052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256052).length < 2 ^ (prefixWord ++ tailWord_256052).sum := by decide
  have hdescent : baseEnd_256052 < baseStart_256052 := by decide
  rcases family_descends (prefixWord ++ tailWord_256052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256063 : List Nat := [1, 1, 2, 2, 3, 1, 4, 3, 5]
def baseStart_256063 : Nat := 118140960795 + 256063 * 2 ^ 59
def prefixEnd_256063 : Nat := 4983230072969 + 3 ^ 40 * 256063 * 2
def baseEnd_256063 : Nat := 29218532629408196896643

theorem tailTrace_256063 : CollatzResearch.WordTrace tailWord_256063 prefixEnd_256063 29218532629408196896643 := by
  unfold tailWord_256063
  simp only [CollatzResearch.WordTrace]
  refine ⟨9339384871334957923820843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6226256580889971949213895 9339384871334957923820843)
  ·
    refine ⟨14009077307002436885731265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9339384871334957923820843 14009077307002436885731265)
    ·
      refine ⟨10506807980251827664298449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14009077307002436885731265 10506807980251827664298449)
      ·
        refine ⟨7880105985188870748223837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10506807980251827664298449 7880105985188870748223837)
        ·
          refine ⟨2955039744445826530583939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7880105985188870748223837 2955039744445826530583939)
          ·
            refine ⟨4432559616668739795875909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2955039744445826530583939 4432559616668739795875909)
            ·
              refine ⟨831104928125388711726733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4432559616668739795875909 831104928125388711726733)
              ·
                refine ⟨311664348047020766897525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 831104928125388711726733 311664348047020766897525)
                ·
                  refine ⟨29218532629408196896643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 311664348047020766897525 29218532629408196896643)
                  ·
                    rfl

theorem cell22_256063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 4, 3, 5].length) (baseStart_256063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_256063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_256063 prefixEnd_256063 := by exact prefixLift 256063
  have htrace : WordTrace (prefixWord ++ tailWord_256063) baseStart_256063 baseEnd_256063 := by
    simpa [prefixWord, tailWord_256063, baseEnd_256063] using wordTrace_append hprefix tailTrace_256063
  have hstable : (prefixWord ++ tailWord_256063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256063).length < 2 ^ (prefixWord ++ tailWord_256063).sum := by decide
  have hdescent : baseEnd_256063 < baseStart_256063 := by decide
  rcases family_descends (prefixWord ++ tailWord_256063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256108 : List Nat := [2, 2, 1, 1, 3, 3, 1, 3, 6]
def baseStart_256108 : Nat := 118140960795 + 256108 * 2 ^ 59
def prefixEnd_256108 : Nat := 4983230072969 + 3 ^ 40 * 256108 * 2
def baseEnd_256108 : Nat := 29223667435953157771597

theorem tailTrace_256108 : CollatzResearch.WordTrace tailWord_256108 prefixEnd_256108 29223667435953157771597 := by
  unfold tailWord_256108
  simp only [CollatzResearch.WordTrace]
  refine ⟨4670513078085965304604489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6227350770781287072805985 4670513078085965304604489)
  ·
    refine ⟨3502884808564473978453367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4670513078085965304604489 3502884808564473978453367)
    ·
      refine ⟨5254327212846710967680051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3502884808564473978453367 5254327212846710967680051)
      ·
        refine ⟨7881490819270066451520077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5254327212846710967680051 7881490819270066451520077)
        ·
          refine ⟨2955559057226274919320029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7881490819270066451520077 2955559057226274919320029)
          ·
            refine ⟨1108334646459853094745011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2955559057226274919320029 1108334646459853094745011)
            ·
              refine ⟨1662501969689779642117517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1108334646459853094745011 1662501969689779642117517)
              ·
                refine ⟨623438238633667365794069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1662501969689779642117517 623438238633667365794069)
                ·
                  refine ⟨29223667435953157771597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 623438238633667365794069 29223667435953157771597)
                  ·
                    rfl

theorem cell22_256108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 6].length) (baseStart_256108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_256108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_256108 prefixEnd_256108 := by exact prefixLift 256108
  have htrace : WordTrace (prefixWord ++ tailWord_256108) baseStart_256108 baseEnd_256108 := by
    simpa [prefixWord, tailWord_256108, baseEnd_256108] using wordTrace_append hprefix tailTrace_256108
  have hstable : (prefixWord ++ tailWord_256108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256108).length < 2 ^ (prefixWord ++ tailWord_256108).sum := by decide
  have hdescent : baseEnd_256108 < baseStart_256108 := by decide
  rcases family_descends (prefixWord ++ tailWord_256108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256159 : List Nat := [1, 1, 2, 6, 1, 2, 3, 2, 4]
def baseStart_256159 : Nat := 118140960795 + 256159 * 2 ^ 59
def prefixEnd_256159 : Nat := 4983230072969 + 3 ^ 40 * 256159 * 2
def baseEnd_256159 : Nat := 29229486883370780096545

theorem tailTrace_256159 : CollatzResearch.WordTrace tailWord_256159 prefixEnd_256159 29229486883370780096545 := by
  unfold tailWord_256159
  simp only [CollatzResearch.WordTrace]
  refine ⟨9342886278987166319315531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6228590852658110879543687 9342886278987166319315531)
  ·
    refine ⟨14014329418480749478973297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9342886278987166319315531 14014329418480749478973297)
    ·
      refine ⟨10510747063860562109229973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14014329418480749478973297 10510747063860562109229973)
      ·
        refine ⟨492691268618463848870155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 10510747063860562109229973 492691268618463848870155)
        ·
          refine ⟨739036902927695773305233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 492691268618463848870155 739036902927695773305233)
          ·
            refine ⟨554277677195771829978925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 739036902927695773305233 554277677195771829978925)
            ·
              refine ⟨207854128948414436242097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 554277677195771829978925 207854128948414436242097)
              ·
                refine ⟨155890596711310827181573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 207854128948414436242097 155890596711310827181573)
                ·
                  refine ⟨29229486883370780096545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155890596711310827181573 29229486883370780096545)
                  ·
                    rfl

theorem cell22_256159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 2, 3, 2, 4].length) (baseStart_256159 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_256159 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_256159 prefixEnd_256159 := by exact prefixLift 256159
  have htrace : WordTrace (prefixWord ++ tailWord_256159) baseStart_256159 baseEnd_256159 := by
    simpa [prefixWord, tailWord_256159, baseEnd_256159] using wordTrace_append hprefix tailTrace_256159
  have hstable : (prefixWord ++ tailWord_256159).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256159).length < 2 ^ (prefixWord ++ tailWord_256159).sum := by decide
  have hdescent : baseEnd_256159 < baseStart_256159 := by decide
  rcases family_descends (prefixWord ++ tailWord_256159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256185 : List Nat := [1, 2, 1, 4, 1, 2, 2, 1, 5, 3]
def baseStart_256185 : Nat := 118140960795 + 256185 * 2 ^ 59
def prefixEnd_256185 : Nat := 4983230072969 + 3 ^ 40 * 256185 * 2
def baseEnd_256185 : Nat := 87697360981456939139555

theorem tailTrace_256185 : CollatzResearch.WordTrace tailWord_256185 prefixEnd_256185 87697360981456939139555 := by
  unfold tailWord_256185
  simp only [CollatzResearch.WordTrace]
  refine ⟨9343834576892972759762009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6229223051261981839841339 9343834576892972759762009)
  ·
    refine ⟨7007875932669729569821507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9343834576892972759762009 7007875932669729569821507)
    ·
      refine ⟨10511813899004594354732261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7007875932669729569821507 10511813899004594354732261)
      ·
        refine ⟨1970965106063361441512299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10511813899004594354732261 1970965106063361441512299)
        ·
          refine ⟨2956447659095042162268449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1970965106063361441512299 2956447659095042162268449)
          ·
            refine ⟨2217335744321281621701337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2956447659095042162268449 2217335744321281621701337)
            ·
              refine ⟨1663001808240961216276003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2217335744321281621701337 1663001808240961216276003)
              ·
                refine ⟨2494502712361441824414005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1663001808240961216276003 2494502712361441824414005)
                ·
                  refine ⟨233859629283885171038813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2494502712361441824414005 233859629283885171038813)
                  ·
                    refine ⟨87697360981456939139555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 233859629283885171038813 87697360981456939139555)
                    ·
                      rfl

theorem cell22_256185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 1, 5, 3].length) (baseStart_256185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_256185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_256185 prefixEnd_256185 := by exact prefixLift 256185
  have htrace : WordTrace (prefixWord ++ tailWord_256185) baseStart_256185 baseEnd_256185 := by
    simpa [prefixWord, tailWord_256185, baseEnd_256185] using wordTrace_append hprefix tailTrace_256185
  have hstable : (prefixWord ++ tailWord_256185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256185).length < 2 ^ (prefixWord ++ tailWord_256185).sum := by decide
  have hdescent : baseEnd_256185 < baseStart_256185 := by decide
  rcases family_descends (prefixWord ++ tailWord_256185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256277 : List Nat := [1, 3, 2, 1, 2, 1, 4, 4, 4]
def baseStart_256277 : Nat := 118140960795 + 256277 * 2 ^ 59
def prefixEnd_256277 : Nat := 4983230072969 + 3 ^ 40 * 256277 * 2
def baseEnd_256277 : Nat := 29242951487199788613091

theorem tailTrace_256277 : CollatzResearch.WordTrace tailWord_256277 prefixEnd_256277 29242951487199788613091 := by
  unfold tailWord_256277
  simp only [CollatzResearch.WordTrace]
  refine ⟨9347190092559672472111085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6231460061706448314740723 9347190092559672472111085)
  ·
    refine ⟨3505196284709877177041657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9347190092559672472111085 3505196284709877177041657)
    ·
      refine ⟨2628897213532407882781243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3505196284709877177041657 2628897213532407882781243)
      ·
        refine ⟨3943345820298611824171865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2628897213532407882781243 3943345820298611824171865)
        ·
          refine ⟨2957509365223958868128899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3943345820298611824171865 2957509365223958868128899)
          ·
            refine ⟨4436264047835938302193349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2957509365223958868128899 4436264047835938302193349)
            ·
              refine ⟨831799508969238431661253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4436264047835938302193349 831799508969238431661253)
              ·
                refine ⟨155962407931732205936485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 831799508969238431661253 155962407931732205936485)
                ·
                  refine ⟨29242951487199788613091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 155962407931732205936485 29242951487199788613091)
                  ·
                    rfl

theorem cell22_256277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 4, 4, 4].length) (baseStart_256277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_256277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_256277 prefixEnd_256277 := by exact prefixLift 256277
  have htrace : WordTrace (prefixWord ++ tailWord_256277) baseStart_256277 baseEnd_256277 := by
    simpa [prefixWord, tailWord_256277, baseEnd_256277] using wordTrace_append hprefix tailTrace_256277
  have hstable : (prefixWord ++ tailWord_256277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256277).length < 2 ^ (prefixWord ++ tailWord_256277).sum := by decide
  have hdescent : baseEnd_256277 < baseStart_256277 := by decide
  rcases family_descends (prefixWord ++ tailWord_256277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256292 : List Nat := [2, 3, 1, 3, 1, 2, 3, 1, 1, 5]
def baseStart_256292 : Nat := 118140960795 + 256292 * 2 ^ 59
def prefixEnd_256292 : Nat := 4983230072969 + 3 ^ 40 * 256292 * 2
def baseEnd_256292 : Nat := 87733989268144326714227

theorem tailTrace_256292 : CollatzResearch.WordTrace tailWord_256292 prefixEnd_256292 87733989268144326714227 := by
  unfold tailWord_256292
  simp only [CollatzResearch.WordTrace]
  refine ⟨4673868593752665016953565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6231824791670220022604753 4673868593752665016953565)
  ·
    refine ⟨1752700722657249381357587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4673868593752665016953565 1752700722657249381357587)
    ·
      refine ⟨2629051083985874072036381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1752700722657249381357587 2629051083985874072036381)
      ·
        refine ⟨985894156494702777013643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2629051083985874072036381 985894156494702777013643)
        ·
          refine ⟨1478841234742054165520465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 985894156494702777013643 1478841234742054165520465)
          ·
            refine ⟨1109130926056540624140349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1478841234742054165520465 1109130926056540624140349)
            ·
              refine ⟨415924097271202734052631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1109130926056540624140349 415924097271202734052631)
              ·
                refine ⟨623886145906804101078947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 415924097271202734052631 623886145906804101078947)
                ·
                  refine ⟨935829218860206151618421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 623886145906804101078947 935829218860206151618421)
                  ·
                    refine ⟨87733989268144326714227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 935829218860206151618421 87733989268144326714227)
                    ·
                      rfl

theorem cell22_256292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 3, 1, 1, 5].length) (baseStart_256292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_256292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_256292 prefixEnd_256292 := by exact prefixLift 256292
  have htrace : WordTrace (prefixWord ++ tailWord_256292) baseStart_256292 baseEnd_256292 := by
    simpa [prefixWord, tailWord_256292, baseEnd_256292] using wordTrace_append hprefix tailTrace_256292
  have hstable : (prefixWord ++ tailWord_256292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256292).length < 2 ^ (prefixWord ++ tailWord_256292).sum := by decide
  have hdescent : baseEnd_256292 < baseStart_256292 := by decide
  rcases family_descends (prefixWord ++ tailWord_256292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256442 : List Nat := [3, 1, 1, 1, 2, 1, 1, 6, 2, 4]
def baseStart_256442 : Nat := 118140960795 + 256442 * 2 ^ 59
def prefixEnd_256442 : Nat := 4983230072969 + 3 ^ 40 * 256442 * 2
def baseEnd_256442 : Nat := 87785337333593935463767

theorem tailTrace_256442 : CollatzResearch.WordTrace tailWord_256442 prefixEnd_256442 87785337333593935463767 := by
  unfold tailWord_256442
  simp only [CollatzResearch.WordTrace]
  refine ⟨2338302034240476412966895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6235472091307937101245053 2338302034240476412966895)
  ·
    refine ⟨3507453051360714619450343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2338302034240476412966895 3507453051360714619450343)
    ·
      refine ⟨5261179577041071929175515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3507453051360714619450343 5261179577041071929175515)
      ·
        refine ⟨7891769365561607893763273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5261179577041071929175515 7891769365561607893763273)
        ·
          refine ⟨5918827024171205920322455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7891769365561607893763273 5918827024171205920322455)
          ·
            refine ⟨8878240536256808880483683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5918827024171205920322455 8878240536256808880483683)
            ·
              refine ⟨13317360804385213320725525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8878240536256808880483683 13317360804385213320725525)
              ·
                refine ⟨624251287705556874409009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 13317360804385213320725525 624251287705556874409009)
                ·
                  refine ⟨468188465779167655806757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 624251287705556874409009 468188465779167655806757)
                  ·
                    refine ⟨87785337333593935463767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 468188465779167655806757 87785337333593935463767)
                    ·
                      rfl

theorem cell22_256442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_256442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_256442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_256442 prefixEnd_256442 := by exact prefixLift 256442
  have htrace : WordTrace (prefixWord ++ tailWord_256442) baseStart_256442 baseEnd_256442 := by
    simpa [prefixWord, tailWord_256442, baseEnd_256442] using wordTrace_append hprefix tailTrace_256442
  have hstable : (prefixWord ++ tailWord_256442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256442).length < 2 ^ (prefixWord ++ tailWord_256442).sum := by decide
  have hdescent : baseEnd_256442 < baseStart_256442 := by decide
  rcases family_descends (prefixWord ++ tailWord_256442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256517 : List Nat := [1, 3, 1, 1, 2, 2, 2, 3, 2, 5]
def baseStart_256517 : Nat := 118140960795 + 256517 * 2 ^ 59
def prefixEnd_256517 : Nat := 4983230072969 + 3 ^ 40 * 256517 * 2
def baseEnd_256517 : Nat := 87811011366318739838537

theorem tailTrace_256517 : CollatzResearch.WordTrace tailWord_256517 prefixEnd_256517 87811011366318739838537 := by
  unfold tailWord_256517
  simp only [CollatzResearch.WordTrace]
  refine ⟨9355943611690193460847805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6237295741126795640565203 9355943611690193460847805)
  ·
    refine ⟨3508478854383822547817927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9355943611690193460847805 3508478854383822547817927)
    ·
      refine ⟨5262718281575733821726891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3508478854383822547817927 5262718281575733821726891)
      ·
        refine ⟨7894077422363600732590337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5262718281575733821726891 7894077422363600732590337)
        ·
          refine ⟨5920558066772700549442753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7894077422363600732590337 5920558066772700549442753)
          ·
            refine ⟨4440418550079525412082065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5920558066772700549442753 4440418550079525412082065)
            ·
              refine ⟨3330313912559644059061549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4440418550079525412082065 3330313912559644059061549)
              ·
                refine ⟨1248867717209866522148081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3330313912559644059061549 1248867717209866522148081)
                ·
                  refine ⟨936650787907399891611061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1248867717209866522148081 936650787907399891611061)
                  ·
                    refine ⟨87811011366318739838537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 936650787907399891611061 87811011366318739838537)
                    ·
                      rfl

theorem cell22_256517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 3, 2, 5].length) (baseStart_256517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_256517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_256517 prefixEnd_256517 := by exact prefixLift 256517
  have htrace : WordTrace (prefixWord ++ tailWord_256517) baseStart_256517 baseEnd_256517 := by
    simpa [prefixWord, tailWord_256517, baseEnd_256517] using wordTrace_append hprefix tailTrace_256517
  have hstable : (prefixWord ++ tailWord_256517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256517).length < 2 ^ (prefixWord ++ tailWord_256517).sum := by decide
  have hdescent : baseEnd_256517 < baseStart_256517 := by decide
  rcases family_descends (prefixWord ++ tailWord_256517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256549 : List Nat := [1, 3, 1, 2, 2, 1, 2, 5, 1, 4]
def baseStart_256549 : Nat := 118140960795 + 256549 * 2 ^ 59
def prefixEnd_256549 : Nat := 4983230072969 + 3 ^ 40 * 256549 * 2
def baseEnd_256549 : Nat := 87821965620281323038439

theorem tailTrace_256549 : CollatzResearch.WordTrace tailWord_256549 prefixEnd_256549 87821965620281323038439 := by
  unfold tailWord_256549
  simp only [CollatzResearch.WordTrace]
  refine ⟨9357110747574262926012701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6238073831716175284008467 9357110747574262926012701)
  ·
    refine ⟨3508916530340348597254763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9357110747574262926012701 3508916530340348597254763)
    ·
      refine ⟨5263374795510522895882145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3508916530340348597254763 5263374795510522895882145)
      ·
        refine ⟨3947531096632892171911609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5263374795510522895882145 3947531096632892171911609)
        ·
          refine ⟨2960648322474669128933707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3947531096632892171911609 2960648322474669128933707)
          ·
            refine ⟨4440972483712003693400561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2960648322474669128933707 4440972483712003693400561)
            ·
              refine ⟨3330729362784002770050421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4440972483712003693400561 3330729362784002770050421)
              ·
                refine ⟨312255877761000259692227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 3330729362784002770050421 312255877761000259692227)
                ·
                  refine ⟨468383816641500389538341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 312255877761000259692227 468383816641500389538341)
                  ·
                    refine ⟨87821965620281323038439, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 468383816641500389538341 87821965620281323038439)
                    ·
                      rfl

theorem cell22_256549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 5, 1, 4].length) (baseStart_256549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_256549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_256549 prefixEnd_256549 := by exact prefixLift 256549
  have htrace : WordTrace (prefixWord ++ tailWord_256549) baseStart_256549 baseEnd_256549 := by
    simpa [prefixWord, tailWord_256549, baseEnd_256549] using wordTrace_append hprefix tailTrace_256549
  have hstable : (prefixWord ++ tailWord_256549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256549).length < 2 ^ (prefixWord ++ tailWord_256549).sum := by decide
  have hdescent : baseEnd_256549 < baseStart_256549 := by decide
  rcases family_descends (prefixWord ++ tailWord_256549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256566 : List Nat := [5, 1, 2, 1, 2, 1, 1, 2, 3, 4]
def baseStart_256566 : Nat := 118140960795 + 256566 * 2 ^ 59
def prefixEnd_256566 : Nat := 4983230072969 + 3 ^ 40 * 256566 * 2
def baseEnd_256566 : Nat := 87827785067698945363387

theorem tailTrace_256566 : CollatzResearch.WordTrace tailWord_256566 prefixEnd_256566 87827785067698945363387 := by
  unfold tailWord_256566
  simp only [CollatzResearch.WordTrace]
  refine ⟨584858174282042176836347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6238487192341783219587701 584858174282042176836347)
  ·
    refine ⟨877287261423063265254521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 584858174282042176836347 877287261423063265254521)
    ·
      refine ⟨657965446067297448940891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 877287261423063265254521 657965446067297448940891)
      ·
        refine ⟨986948169100946173411337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 657965446067297448940891 986948169100946173411337)
        ·
          refine ⟨740211126825709630058503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 986948169100946173411337 740211126825709630058503)
          ·
            refine ⟨1110316690238564445087755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 740211126825709630058503 1110316690238564445087755)
            ·
              refine ⟨1665475035357846667631633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1110316690238564445087755 1665475035357846667631633)
              ·
                refine ⟨1249106276518385000723725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1665475035357846667631633 1249106276518385000723725)
                ·
                  refine ⟨468414853694394375271397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1249106276518385000723725 468414853694394375271397)
                  ·
                    refine ⟨87827785067698945363387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 468414853694394375271397 87827785067698945363387)
                    ·
                      rfl

theorem cell22_256566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_256566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_256566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_256566 prefixEnd_256566 := by exact prefixLift 256566
  have htrace : WordTrace (prefixWord ++ tailWord_256566) baseStart_256566 baseEnd_256566 := by
    simpa [prefixWord, tailWord_256566, baseEnd_256566] using wordTrace_append hprefix tailTrace_256566
  have hstable : (prefixWord ++ tailWord_256566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256566).length < 2 ^ (prefixWord ++ tailWord_256566).sum := by decide
  have hdescent : baseEnd_256566 < baseStart_256566 := by decide
  rcases family_descends (prefixWord ++ tailWord_256566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256594 : List Nat := [3, 2, 2, 1, 2, 1, 3, 1, 1, 6]
def baseStart_256594 : Nat := 118140960795 + 256594 * 2 ^ 59
def prefixEnd_256594 : Nat := 4983230072969 + 3 ^ 40 * 256594 * 2
def baseEnd_256594 : Nat := 87837370039916205663301

theorem tailTrace_256594 : CollatzResearch.WordTrace tailWord_256594 prefixEnd_256594 87837370039916205663301 := by
  unfold tailWord_256594
  simp only [CollatzResearch.WordTrace]
  refine ⟨2339688008102808902850209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6239168021607490407600557 2339688008102808902850209)
  ·
    refine ⟨1754766006077106677137657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2339688008102808902850209 1754766006077106677137657)
    ·
      refine ⟨1316074504557830007853243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1754766006077106677137657 1316074504557830007853243)
      ·
        refine ⟨1974111756836745011779865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1316074504557830007853243 1974111756836745011779865)
        ·
          refine ⟨1480583817627558758834899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1974111756836745011779865 1480583817627558758834899)
          ·
            refine ⟨2220875726441338138252349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1480583817627558758834899 2220875726441338138252349)
            ·
              refine ⟨832828397415501801844631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2220875726441338138252349 832828397415501801844631)
              ·
                refine ⟨1249242596123252702766947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 832828397415501801844631 1249242596123252702766947)
                ·
                  refine ⟨1873863894184879054150421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1249242596123252702766947 1873863894184879054150421)
                  ·
                    refine ⟨87837370039916205663301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1873863894184879054150421 87837370039916205663301)
                    ·
                      rfl

theorem cell22_256594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_256594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_256594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_256594 prefixEnd_256594 := by exact prefixLift 256594
  have htrace : WordTrace (prefixWord ++ tailWord_256594) baseStart_256594 baseEnd_256594 := by
    simpa [prefixWord, tailWord_256594, baseEnd_256594] using wordTrace_append hprefix tailTrace_256594
  have hstable : (prefixWord ++ tailWord_256594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256594).length < 2 ^ (prefixWord ++ tailWord_256594).sum := by decide
  have hdescent : baseEnd_256594 < baseStart_256594 := by decide
  rcases family_descends (prefixWord ++ tailWord_256594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256607 : List Nat := [1, 1, 2, 3, 1, 1, 1, 2, 1, 9]
def baseStart_256607 : Nat := 118140960795 + 256607 * 2 ^ 59
def prefixEnd_256607 : Nat := 4983230072969 + 3 ^ 40 * 256607 * 2
def baseEnd_256607 : Nat := 87841820205588505088261

theorem tailTrace_256607 : CollatzResearch.WordTrace tailWord_256607 prefixEnd_256607 87841820205588505088261 := by
  unfold tailWord_256607
  simp only [CollatzResearch.WordTrace]
  refine ⟨9359226181364138831624075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6239484120909425887749383 9359226181364138831624075)
  ·
    refine ⟨14038839272046208247436113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9359226181364138831624075 14038839272046208247436113)
    ·
      refine ⟨10529129454034656185577085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14038839272046208247436113 10529129454034656185577085)
      ·
        refine ⟨3948423545262996069591407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10529129454034656185577085 3948423545262996069591407)
        ·
          refine ⟨5922635317894494104387111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3948423545262996069591407 5922635317894494104387111)
          ·
            refine ⟨8883952976841741156580667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5922635317894494104387111 8883952976841741156580667)
            ·
              refine ⟨13325929465262611734871001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8883952976841741156580667 13325929465262611734871001)
              ·
                refine ⟨9994447098946958801153251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13325929465262611734871001 9994447098946958801153251)
                ·
                  refine ⟨14991670648420438201729877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 9994447098946958801153251 14991670648420438201729877)
                  ·
                    refine ⟨87841820205588505088261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 14991670648420438201729877 87841820205588505088261)
                    ·
                      rfl

theorem cell22_256607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_256607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_256607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_256607 prefixEnd_256607 := by exact prefixLift 256607
  have htrace : WordTrace (prefixWord ++ tailWord_256607) baseStart_256607 baseEnd_256607 := by
    simpa [prefixWord, tailWord_256607, baseEnd_256607] using wordTrace_append hprefix tailTrace_256607
  have hstable : (prefixWord ++ tailWord_256607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256607).length < 2 ^ (prefixWord ++ tailWord_256607).sum := by decide
  have hdescent : baseEnd_256607 < baseStart_256607 := by decide
  rcases family_descends (prefixWord ++ tailWord_256607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256630 : List Nat := [5, 1, 1, 2, 4, 1, 1, 1, 1, 5]
def baseStart_256630 : Nat := 118140960795 + 256630 * 2 ^ 59
def prefixEnd_256630 : Nat := 4983230072969 + 3 ^ 40 * 256630 * 2
def baseEnd_256630 : Nat := 87849693575624111763191

theorem tailTrace_256630 : CollatzResearch.WordTrace tailWord_256630 prefixEnd_256630 87849693575624111763191 := by
  unfold tailWord_256630
  simp only [CollatzResearch.WordTrace]
  refine ⟨585004066267550859981959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6240043373520542506474229 585004066267550859981959)
  ·
    refine ⟨877506099401326289972939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 585004066267550859981959 877506099401326289972939)
    ·
      refine ⟨1316259149101989434959409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 877506099401326289972939 1316259149101989434959409)
      ·
        refine ⟨987194361826492076219557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1316259149101989434959409 987194361826492076219557)
        ·
          refine ⟨185098942842467264291167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 987194361826492076219557 185098942842467264291167)
          ·
            refine ⟨277648414263700896436751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185098942842467264291167 277648414263700896436751)
            ·
              refine ⟨416472621395551344655127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 277648414263700896436751 416472621395551344655127)
              ·
                refine ⟨624708932093327016982691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 416472621395551344655127 624708932093327016982691)
                ·
                  refine ⟨937063398139990525474037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 624708932093327016982691 937063398139990525474037)
                  ·
                    refine ⟨87849693575624111763191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 937063398139990525474037 87849693575624111763191)
                    ·
                      rfl

theorem cell22_256630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_256630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_256630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_256630 prefixEnd_256630 := by exact prefixLift 256630
  have htrace : WordTrace (prefixWord ++ tailWord_256630) baseStart_256630 baseEnd_256630 := by
    simpa [prefixWord, tailWord_256630, baseEnd_256630] using wordTrace_append hprefix tailTrace_256630
  have hstable : (prefixWord ++ tailWord_256630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256630).length < 2 ^ (prefixWord ++ tailWord_256630).sum := by decide
  have hdescent : baseEnd_256630 < baseStart_256630 := by decide
  rcases family_descends (prefixWord ++ tailWord_256630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256641 : List Nat := [1, 2, 4, 2, 1, 1, 1, 4, 3, 3]
def baseStart_256641 : Nat := 118140960795 + 256641 * 2 ^ 59
def prefixEnd_256641 : Nat := 4983230072969 + 3 ^ 40 * 256641 * 2
def baseEnd_256641 : Nat := 87853459100423749738157

theorem tailTrace_256641 : CollatzResearch.WordTrace tailWord_256641 prefixEnd_256641 87853459100423749738157 := by
  unfold tailWord_256641
  simp only [CollatzResearch.WordTrace]
  refine ⟨9360466263240962638361777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6240310842160641758907851 9360466263240962638361777)
  ·
    refine ⟨7020349697430721978771333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9360466263240962638361777 7020349697430721978771333)
    ·
      refine ⟨1316315568268260371019625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7020349697430721978771333 1316315568268260371019625)
      ·
        refine ⟨987236676201195278264719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1316315568268260371019625 987236676201195278264719)
        ·
          refine ⟨1480855014301792917397079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 987236676201195278264719 1480855014301792917397079)
          ·
            refine ⟨2221282521452689376095619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1480855014301792917397079 2221282521452689376095619)
            ·
              refine ⟨3331923782179034064143429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2221282521452689376095619 3331923782179034064143429)
              ·
                refine ⟨624735709158568887026893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3331923782179034064143429 624735709158568887026893)
                ·
                  refine ⟨234275890934463332635085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 624735709158568887026893 234275890934463332635085)
                  ·
                    refine ⟨87853459100423749738157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 234275890934463332635085 87853459100423749738157)
                    ·
                      rfl

theorem cell22_256641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 1, 4, 3, 3].length) (baseStart_256641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_256641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_256641 prefixEnd_256641 := by exact prefixLift 256641
  have htrace : WordTrace (prefixWord ++ tailWord_256641) baseStart_256641 baseEnd_256641 := by
    simpa [prefixWord, tailWord_256641, baseEnd_256641] using wordTrace_append hprefix tailTrace_256641
  have hstable : (prefixWord ++ tailWord_256641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256641).length < 2 ^ (prefixWord ++ tailWord_256641).sum := by decide
  have hdescent : baseEnd_256641 < baseStart_256641 := by decide
  rcases family_descends (prefixWord ++ tailWord_256641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256654 : List Nat := [4, 1, 1, 3, 1, 1, 1, 1, 9]
def baseStart_256654 : Nat := 118140960795 + 256654 * 2 ^ 59
def prefixEnd_256654 : Nat := 4983230072969 + 3 ^ 40 * 256654 * 2
def baseEnd_256654 : Nat := 29285969755365349721039

theorem tailTrace_256654 : CollatzResearch.WordTrace tailWord_256654 prefixEnd_256654 29285969755365349721039 := by
  unfold tailWord_256654
  simp only [CollatzResearch.WordTrace]
  refine ⟨1170117551524233232323127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6240626941462577239056677 1170117551524233232323127)
  ·
    refine ⟨1755176327286349848484691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1170117551524233232323127 1755176327286349848484691)
    ·
      refine ⟨2632764490929524772727037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1755176327286349848484691 2632764490929524772727037)
      ·
        refine ⟨987286684098571789772639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2632764490929524772727037 987286684098571789772639)
        ·
          refine ⟨1480930026147857684658959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 987286684098571789772639 1480930026147857684658959)
          ·
            refine ⟨2221395039221786526988439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1480930026147857684658959 2221395039221786526988439)
            ·
              refine ⟨3332092558832679790482659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2221395039221786526988439 3332092558832679790482659)
              ·
                refine ⟨4998138838249019685723989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3332092558832679790482659 4998138838249019685723989)
                ·
                  refine ⟨29285969755365349721039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 4998138838249019685723989 29285969755365349721039)
                  ·
                    rfl

theorem cell22_256654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 1, 9].length) (baseStart_256654 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_256654 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_256654 prefixEnd_256654 := by exact prefixLift 256654
  have htrace : WordTrace (prefixWord ++ tailWord_256654) baseStart_256654 baseEnd_256654 := by
    simpa [prefixWord, tailWord_256654, baseEnd_256654] using wordTrace_append hprefix tailTrace_256654
  have hstable : (prefixWord ++ tailWord_256654).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256654).length < 2 ^ (prefixWord ++ tailWord_256654).sum := by decide
  have hdescent : baseEnd_256654 < baseStart_256654 := by decide
  rcases family_descends (prefixWord ++ tailWord_256654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256669 : List Nat := [1, 4, 2, 1, 1, 1, 2, 1, 4, 5]
def baseStart_256669 : Nat := 118140960795 + 256669 * 2 ^ 59
def prefixEnd_256669 : Nat := 4983230072969 + 3 ^ 40 * 256669 * 2
def baseEnd_256669 : Nat := 87863044072641010038071

theorem tailTrace_256669 : CollatzResearch.WordTrace tailWord_256669 prefixEnd_256669 87863044072641010038071 := by
  unfold tailWord_256669
  simp only [CollatzResearch.WordTrace]
  refine ⟨9361487507139523420381061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6240991671426348946920707 9361487507139523420381061)
  ·
    refine ⟨1755278907588660641321449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9361487507139523420381061 1755278907588660641321449)
    ·
      refine ⟨1316459180691495480991087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1755278907588660641321449 1316459180691495480991087)
      ·
        refine ⟨1974688771037243221486631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1316459180691495480991087 1974688771037243221486631)
        ·
          refine ⟨2962033156555864832229947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1974688771037243221486631 2962033156555864832229947)
          ·
            refine ⟨4443049734833797248344921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2962033156555864832229947 4443049734833797248344921)
            ·
              refine ⟨3332287301125347936258691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4443049734833797248344921 3332287301125347936258691)
              ·
                refine ⟨4998430951688021904388037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3332287301125347936258691 4998430951688021904388037)
                ·
                  refine ⟨937205803441504107072757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4998430951688021904388037 937205803441504107072757)
                  ·
                    refine ⟨87863044072641010038071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 937205803441504107072757 87863044072641010038071)
                    ·
                      rfl

theorem cell22_256669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_256669 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_256669 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_256669 prefixEnd_256669 := by exact prefixLift 256669
  have htrace : WordTrace (prefixWord ++ tailWord_256669) baseStart_256669 baseEnd_256669 := by
    simpa [prefixWord, tailWord_256669, baseEnd_256669] using wordTrace_append hprefix tailTrace_256669
  have hstable : (prefixWord ++ tailWord_256669).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256669).length < 2 ^ (prefixWord ++ tailWord_256669).sum := by decide
  have hdescent : baseEnd_256669 < baseStart_256669 := by decide
  rcases family_descends (prefixWord ++ tailWord_256669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256701 : List Nat := [1, 4, 1, 2, 1, 4, 1, 1, 3, 4]
def baseStart_256701 : Nat := 118140960795 + 256701 * 2 ^ 59
def prefixEnd_256701 : Nat := 4983230072969 + 3 ^ 40 * 256701 * 2
def baseEnd_256701 : Nat := 87873998326603593237973

theorem tailTrace_256701 : CollatzResearch.WordTrace tailWord_256701 prefixEnd_256701 87873998326603593237973 := by
  unfold tailWord_256701
  simp only [CollatzResearch.WordTrace]
  refine ⟨9362654643023592885545957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6241769762015728590363971 9362654643023592885545957)
  ·
    refine ⟨1755497745566923666039867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9362654643023592885545957 1755497745566923666039867)
    ·
      refine ⟨2633246618350385499059801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1755497745566923666039867 2633246618350385499059801)
      ·
        refine ⟨1974934963762789124294851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2633246618350385499059801 1974934963762789124294851)
        ·
          refine ⟨2962402445644183686442277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1974934963762789124294851 2962402445644183686442277)
          ·
            refine ⟨555450458558284441207927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2962402445644183686442277 555450458558284441207927)
            ·
              refine ⟨833175687837426661811891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 555450458558284441207927 833175687837426661811891)
              ·
                refine ⟨1249763531756139992717837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 833175687837426661811891 1249763531756139992717837)
                ·
                  refine ⟨468661324408552497269189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1249763531756139992717837 468661324408552497269189)
                  ·
                    refine ⟨87873998326603593237973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 468661324408552497269189 87873998326603593237973)
                    ·
                      rfl

theorem cell22_256701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_256701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_256701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_256701 prefixEnd_256701 := by exact prefixLift 256701
  have htrace : WordTrace (prefixWord ++ tailWord_256701) baseStart_256701 baseEnd_256701 := by
    simpa [prefixWord, tailWord_256701, baseEnd_256701] using wordTrace_append hprefix tailTrace_256701
  have hstable : (prefixWord ++ tailWord_256701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256701).length < 2 ^ (prefixWord ++ tailWord_256701).sum := by decide
  have hdescent : baseEnd_256701 < baseStart_256701 := by decide
  rcases family_descends (prefixWord ++ tailWord_256701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256928 : List Nat := [2, 1, 1, 4, 1, 1, 3, 1, 5, 3]
def baseStart_256928 : Nat := 118140960795 + 256928 * 2 ^ 59
def prefixEnd_256928 : Nat := 4983230072969 + 3 ^ 40 * 256928 * 2
def baseEnd_256928 : Nat := 87951705065650667812277

theorem tailTrace_256928 : CollatzResearch.WordTrace tailWord_256928 prefixEnd_256928 87951705065650667812277 := by
  unfold tailWord_256928
  simp only [CollatzResearch.WordTrace]
  refine ⟨4685467006600605327029719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6247289342134140436039625 4685467006600605327029719)
  ·
    refine ⟨7028200509900907990544579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4685467006600605327029719 7028200509900907990544579)
    ·
      refine ⟨10542300764851361985816869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7028200509900907990544579 10542300764851361985816869)
      ·
        refine ⟨1976681393409630372340663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 10542300764851361985816869 1976681393409630372340663)
        ·
          refine ⟨2965022090114445558510995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1976681393409630372340663 2965022090114445558510995)
          ·
            refine ⟨4447533135171668337766493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2965022090114445558510995 4447533135171668337766493)
            ·
              refine ⟨1667824925689375626662435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4447533135171668337766493 1667824925689375626662435)
              ·
                refine ⟨2501737388534063439993653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1667824925689375626662435 2501737388534063439993653)
                ·
                  refine ⟨234537880175068447499405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2501737388534063439993653 234537880175068447499405)
                  ·
                    refine ⟨87951705065650667812277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 234537880175068447499405 87951705065650667812277)
                    ·
                      rfl

theorem cell22_256928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 1, 5, 3].length) (baseStart_256928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_256928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_256928 prefixEnd_256928 := by exact prefixLift 256928
  have htrace : WordTrace (prefixWord ++ tailWord_256928) baseStart_256928 baseEnd_256928 := by
    simpa [prefixWord, tailWord_256928, baseEnd_256928] using wordTrace_append hprefix tailTrace_256928
  have hstable : (prefixWord ++ tailWord_256928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256928).length < 2 ^ (prefixWord ++ tailWord_256928).sum := by decide
  have hdescent : baseEnd_256928 < baseStart_256928 := by decide
  rcases family_descends (prefixWord ++ tailWord_256928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256930 : List Nat := [3, 3, 1, 2, 2, 2, 3, 6]
def baseStart_256930 : Nat := 118140960795 + 256930 * 2 ^ 59
def prefixEnd_256930 : Nat := 4983230072969 + 3 ^ 40 * 256930 * 2
def baseEnd_256930 : Nat := 9772487745169258806919

theorem tailTrace_256930 : CollatzResearch.WordTrace tailWord_256930 prefixEnd_256930 9772487745169258806919 := by
  unfold tailWord_256930
  simp only [CollatzResearch.WordTrace]
  refine ⟨2342751739798491248908061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6247337972795976663754829 2342751739798491248908061)
  ·
    refine ⟨878531902424434218340523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 2342751739798491248908061 878531902424434218340523)
    ·
      refine ⟨1317797853636651327510785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 878531902424434218340523 1317797853636651327510785)
      ·
        refine ⟨988348390227488495633089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1317797853636651327510785 988348390227488495633089)
        ·
          refine ⟨741261292670616371724817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 988348390227488495633089 741261292670616371724817)
          ·
            refine ⟨555945969502962278793613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 741261292670616371724817 555945969502962278793613)
            ·
              refine ⟨208479738563610854547605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 555945969502962278793613 208479738563610854547605)
              ·
                refine ⟨9772487745169258806919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 208479738563610854547605 9772487745169258806919)
                ·
                  rfl

theorem cell22_256930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 3, 6].length) (baseStart_256930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_256930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_256930 prefixEnd_256930 := by exact prefixLift 256930
  have htrace : WordTrace (prefixWord ++ tailWord_256930) baseStart_256930 baseEnd_256930 := by
    simpa [prefixWord, tailWord_256930, baseEnd_256930] using wordTrace_append hprefix tailTrace_256930
  have hstable : (prefixWord ++ tailWord_256930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256930).length < 2 ^ (prefixWord ++ tailWord_256930).sum := by decide
  have hdescent : baseEnd_256930 < baseStart_256930 := by decide
  rcases family_descends (prefixWord ++ tailWord_256930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256958 : List Nat := [4, 2, 1, 1, 1, 2, 3, 1, 7]
def baseStart_256958 : Nat := 118140960795 + 256958 * 2 ^ 59
def prefixEnd_256958 : Nat := 4983230072969 + 3 ^ 40 * 256958 * 2
def baseEnd_256958 : Nat := 29320658226246863187395

theorem tailTrace_256958 : CollatzResearch.WordTrace tailWord_256958 prefixEnd_256958 29320658226246863187395 := by
  unfold tailWord_256958
  simp only [CollatzResearch.WordTrace]
  refine ⟨1171503525386565722206441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6248018802061683851767685 1171503525386565722206441)
  ·
    refine ⟨878627644039924291654831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1171503525386565722206441 878627644039924291654831)
    ·
      refine ⟨1317941466059886437482247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 878627644039924291654831 1317941466059886437482247)
      ·
        refine ⟨1976912199089829656223371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1317941466059886437482247 1976912199089829656223371)
        ·
          refine ⟨2965368298634744484335057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1976912199089829656223371 2965368298634744484335057)
          ·
            refine ⟨2224026223976058363251293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2965368298634744484335057 2224026223976058363251293)
            ·
              refine ⟨834009833991021886219235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2224026223976058363251293 834009833991021886219235)
              ·
                refine ⟨1251014750986532829328853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 834009833991021886219235 1251014750986532829328853)
                ·
                  refine ⟨29320658226246863187395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1251014750986532829328853 29320658226246863187395)
                  ·
                    rfl

theorem cell22_256958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 3, 1, 7].length) (baseStart_256958 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_256958 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_256958 prefixEnd_256958 := by exact prefixLift 256958
  have htrace : WordTrace (prefixWord ++ tailWord_256958) baseStart_256958 baseEnd_256958 := by
    simpa [prefixWord, tailWord_256958, baseEnd_256958] using wordTrace_append hprefix tailTrace_256958
  have hstable : (prefixWord ++ tailWord_256958).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256958).length < 2 ^ (prefixWord ++ tailWord_256958).sum := by decide
  have hdescent : baseEnd_256958 < baseStart_256958 := by decide
  rcases family_descends (prefixWord ++ tailWord_256958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_256975 : List Nat := [1, 1, 2, 1, 1, 7, 3, 1, 5]
def baseStart_256975 : Nat := 118140960795 + 256975 * 2 ^ 59
def prefixEnd_256975 : Nat := 4983230072969 + 3 ^ 40 * 256975 * 2
def baseEnd_256975 : Nat := 29322598042052737295711

theorem tailTrace_256975 : CollatzResearch.WordTrace tailWord_256975 prefixEnd_256975 29322598042052737295711 := by
  unfold tailWord_256975
  simp only [CollatzResearch.WordTrace]
  refine ⟨9372648244030937681020379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6248432162687291787346919 9372648244030937681020379)
  ·
    refine ⟨14058972366046406521530569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9372648244030937681020379 14058972366046406521530569)
    ·
      refine ⟨10544229274534804891147927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14058972366046406521530569 10544229274534804891147927)
      ·
        refine ⟨15816343911802207336721891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10544229274534804891147927 15816343911802207336721891)
        ·
          refine ⟨23724515867703311005082837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15816343911802207336721891 23724515867703311005082837)
          ·
            refine ⟨556043340649296351681629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 23724515867703311005082837 556043340649296351681629)
            ·
              refine ⟨208516252743486131880611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 556043340649296351681629 208516252743486131880611)
              ·
                refine ⟨312774379115229197820917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208516252743486131880611 312774379115229197820917)
                ·
                  refine ⟨29322598042052737295711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 312774379115229197820917 29322598042052737295711)
                  ·
                    rfl

theorem cell22_256975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 3, 1, 5].length) (baseStart_256975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_256975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_256975 prefixEnd_256975 := by exact prefixLift 256975
  have htrace : WordTrace (prefixWord ++ tailWord_256975) baseStart_256975 baseEnd_256975 := by
    simpa [prefixWord, tailWord_256975, baseEnd_256975] using wordTrace_append hprefix tailTrace_256975
  have hstable : (prefixWord ++ tailWord_256975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_256975).length < 2 ^ (prefixWord ++ tailWord_256975).sum := by decide
  have hdescent : baseEnd_256975 < baseStart_256975 := by decide
  rcases family_descends (prefixWord ++ tailWord_256975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257013 : List Nat := [1, 3, 5, 2, 1, 1, 3, 2, 1, 3]
def baseStart_257013 : Nat := 118140960795 + 257013 * 2 ^ 59
def prefixEnd_257013 : Nat := 4983230072969 + 3 ^ 40 * 257013 * 2
def baseEnd_257013 : Nat := 87980802302738779437017

theorem tailTrace_257013 : CollatzResearch.WordTrace tailWord_257013 prefixEnd_257013 87980802302738779437017 := by
  unfold tailWord_257013
  simp only [CollatzResearch.WordTrace]
  refine ⟨9374034217893270170903693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6249356145262180113935795 9374034217893270170903693)
  ·
    refine ⟨3515262831709976314088885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9374034217893270170903693 3515262831709976314088885)
    ·
      refine ⟨329555890472810279445833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3515262831709976314088885 329555890472810279445833)
      ·
        refine ⟨247166917854607709584375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329555890472810279445833 247166917854607709584375)
        ·
          refine ⟨370750376781911564376563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247166917854607709584375 370750376781911564376563)
          ·
            refine ⟨556125565172867346564845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 370750376781911564376563 556125565172867346564845)
            ·
              refine ⟨208547086939825254961817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 556125565172867346564845 208547086939825254961817)
              ·
                refine ⟨156410315204868941221363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208547086939825254961817 156410315204868941221363)
                ·
                  refine ⟨234615472807303411832045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156410315204868941221363 234615472807303411832045)
                  ·
                    refine ⟨87980802302738779437017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 234615472807303411832045 87980802302738779437017)
                    ·
                      rfl

theorem cell22_257013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_257013 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257013 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257013 prefixEnd_257013 := by exact prefixLift 257013
  have htrace : WordTrace (prefixWord ++ tailWord_257013) baseStart_257013 baseEnd_257013 := by
    simpa [prefixWord, tailWord_257013, baseEnd_257013] using wordTrace_append hprefix tailTrace_257013
  have hstable : (prefixWord ++ tailWord_257013).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257013).length < 2 ^ (prefixWord ++ tailWord_257013).sum := by decide
  have hdescent : baseEnd_257013 < baseStart_257013 := by decide
  rcases family_descends (prefixWord ++ tailWord_257013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257020 : List Nat := [2, 2, 2, 1, 2, 5, 1, 1, 6]
def baseStart_257020 : Nat := 118140960795 + 257020 * 2 ^ 59
def prefixEnd_257020 : Nat := 4983230072969 + 3 ^ 40 * 257020 * 2
def baseEnd_257020 : Nat := 29327732848597698170665

theorem tailTrace_257020 : CollatzResearch.WordTrace tailWord_257020 prefixEnd_257020 29327732848597698170665 := by
  unfold tailWord_257020
  simp only [CollatzResearch.WordTrace]
  refine ⟨4687144764433955183204257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6249526352578606910939009 4687144764433955183204257)
  ·
    refine ⟨3515358573325466387403193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4687144764433955183204257 3515358573325466387403193)
    ·
      refine ⟨2636518929994099790552395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3515358573325466387403193 2636518929994099790552395)
      ·
        refine ⟨3954778394991149685828593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2636518929994099790552395 3954778394991149685828593)
        ·
          refine ⟨2966083796243362264371445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3954778394991149685828593 2966083796243362264371445)
          ·
            refine ⟨278070355897815212284823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2966083796243362264371445 278070355897815212284823)
            ·
              refine ⟨417105533846722818427235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278070355897815212284823 417105533846722818427235)
              ·
                refine ⟨625658300770084227640853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417105533846722818427235 625658300770084227640853)
                ·
                  refine ⟨29327732848597698170665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 625658300770084227640853 29327732848597698170665)
                  ·
                    rfl

theorem cell22_257020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 5, 1, 1, 6].length) (baseStart_257020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257020 prefixEnd_257020 := by exact prefixLift 257020
  have htrace : WordTrace (prefixWord ++ tailWord_257020) baseStart_257020 baseEnd_257020 := by
    simpa [prefixWord, tailWord_257020, baseEnd_257020] using wordTrace_append hprefix tailTrace_257020
  have hstable : (prefixWord ++ tailWord_257020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257020).length < 2 ^ (prefixWord ++ tailWord_257020).sum := by decide
  have hdescent : baseEnd_257020 < baseStart_257020 := by decide
  rcases family_descends (prefixWord ++ tailWord_257020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257026 : List Nat := [3, 4, 1, 3, 1, 2, 2, 1, 5]
def baseStart_257026 : Nat := 118140960795 + 257026 * 2 ^ 59
def prefixEnd_257026 : Nat := 4983230072969 + 3 ^ 40 * 257026 * 2
def baseEnd_257026 : Nat := 29328417489470359620659

theorem tailTrace_257026 : CollatzResearch.WordTrace tailWord_257026 prefixEnd_257026 29328417489470359620659 := by
  unfold tailWord_257026
  simp only [CollatzResearch.WordTrace]
  refine ⟨2343627091711543347781733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6249672244564115594084621 2343627091711543347781733)
  ·
    refine ⟨439430079695914377709075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2343627091711543347781733 439430079695914377709075)
    ·
      refine ⟨659145119543871566563613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439430079695914377709075 659145119543871566563613)
      ·
        refine ⟨247179419828951837461355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 659145119543871566563613 247179419828951837461355)
        ·
          refine ⟨370769129743427756192033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247179419828951837461355 370769129743427756192033)
          ·
            refine ⟨278076847307570817144025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 370769129743427756192033 278076847307570817144025)
            ·
              refine ⟨208557635480678112858019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278076847307570817144025 208557635480678112858019)
              ·
                refine ⟨312836453221017169287029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 208557635480678112858019 312836453221017169287029)
                ·
                  refine ⟨29328417489470359620659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 312836453221017169287029 29328417489470359620659)
                  ·
                    rfl

theorem cell22_257026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_257026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257026 prefixEnd_257026 := by exact prefixLift 257026
  have htrace : WordTrace (prefixWord ++ tailWord_257026) baseStart_257026 baseEnd_257026 := by
    simpa [prefixWord, tailWord_257026, baseEnd_257026] using wordTrace_append hprefix tailTrace_257026
  have hstable : (prefixWord ++ tailWord_257026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257026).length < 2 ^ (prefixWord ++ tailWord_257026).sum := by decide
  have hdescent : baseEnd_257026 < baseStart_257026 := by decide
  rcases family_descends (prefixWord ++ tailWord_257026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257048 : List Nat := [2, 1, 2, 3, 2, 2, 2, 8]
def baseStart_257048 : Nat := 118140960795 + 257048 * 2 ^ 59
def prefixEnd_257048 : Nat := 4983230072969 + 3 ^ 40 * 257048 * 2
def baseEnd_257048 : Nat := 9776975946445594979101

theorem tailTrace_257048 : CollatzResearch.WordTrace tailWord_257048 prefixEnd_257048 9776975946445594979101 := by
  unfold tailWord_257048
  simp only [CollatzResearch.WordTrace]
  refine ⟨4687655386383235574213899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6250207181844314098951865 4687655386383235574213899)
  ·
    refine ⟨7031483079574853361320849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4687655386383235574213899 7031483079574853361320849)
    ·
      refine ⟨5273612309681140020990637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7031483079574853361320849 5273612309681140020990637)
      ·
        refine ⟨1977604616130427507871489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5273612309681140020990637 1977604616130427507871489)
        ·
          refine ⟨1483203462097820630903617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1977604616130427507871489 1483203462097820630903617)
          ·
            refine ⟨1112402596573365473177713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1483203462097820630903617 1112402596573365473177713)
            ·
              refine ⟨834301947430024104883285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1112402596573365473177713 834301947430024104883285)
              ·
                refine ⟨9776975946445594979101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 834301947430024104883285 9776975946445594979101)
                ·
                  rfl

theorem cell22_257048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 2, 8].length) (baseStart_257048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257048 prefixEnd_257048 := by exact prefixLift 257048
  have htrace : WordTrace (prefixWord ++ tailWord_257048) baseStart_257048 baseEnd_257048 := by
    simpa [prefixWord, tailWord_257048, baseEnd_257048] using wordTrace_append hprefix tailTrace_257048
  have hstable : (prefixWord ++ tailWord_257048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257048).length < 2 ^ (prefixWord ++ tailWord_257048).sum := by decide
  have hdescent : baseEnd_257048 < baseStart_257048 := by decide
  rcases family_descends (prefixWord ++ tailWord_257048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257050 : List Nat := [3, 1, 1, 3, 1, 2, 4, 1, 2, 4]
def baseStart_257050 : Nat := 118140960795 + 257050 * 2 ^ 59
def prefixEnd_257050 : Nat := 4983230072969 + 3 ^ 40 * 257050 * 2
def baseEnd_257050 : Nat := 87993468158883016261903

theorem tailTrace_257050 : CollatzResearch.WordTrace tailWord_257050 prefixEnd_257050 87993468158883016261903 := by
  unfold tailWord_257050
  simp only [CollatzResearch.WordTrace]
  refine ⟨2343845929689806372500151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6250255812506150326667069 2343845929689806372500151)
  ·
    refine ⟨3515768894534709558750227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2343845929689806372500151 3515768894534709558750227)
    ·
      refine ⟨5273653341802064338125341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3515768894534709558750227 5273653341802064338125341)
      ·
        refine ⟨1977620003175774126797003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5273653341802064338125341 1977620003175774126797003)
        ·
          refine ⟨2966430004763661190195505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1977620003175774126797003 2966430004763661190195505)
          ·
            refine ⟨2224822503572745892646629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2966430004763661190195505 2224822503572745892646629)
            ·
              refine ⟨417154219419889854871243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2224822503572745892646629 417154219419889854871243)
              ·
                refine ⟨625731329129834782306865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417154219419889854871243 625731329129834782306865)
                ·
                  refine ⟨469298496847376086730149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 625731329129834782306865 469298496847376086730149)
                  ·
                    refine ⟨87993468158883016261903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 469298496847376086730149 87993468158883016261903)
                    ·
                      rfl

theorem cell22_257050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 4, 1, 2, 4].length) (baseStart_257050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257050 prefixEnd_257050 := by exact prefixLift 257050
  have htrace : WordTrace (prefixWord ++ tailWord_257050) baseStart_257050 baseEnd_257050 := by
    simpa [prefixWord, tailWord_257050, baseEnd_257050] using wordTrace_append hprefix tailTrace_257050
  have hstable : (prefixWord ++ tailWord_257050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257050).length < 2 ^ (prefixWord ++ tailWord_257050).sum := by decide
  have hdescent : baseEnd_257050 < baseStart_257050 := by decide
  rcases family_descends (prefixWord ++ tailWord_257050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257127 : List Nat := [1, 1, 5, 1, 1, 5, 1, 2, 5]
def baseStart_257127 : Nat := 118140960795 + 257127 * 2 ^ 59
def prefixEnd_257127 : Nat := 4983230072969 + 3 ^ 40 * 257127 * 2
def baseEnd_257127 : Nat := 29339942277493494028889

theorem tailTrace_257127 : CollatzResearch.WordTrace tailWord_257127 prefixEnd_257127 29339942277493494028889 := by
  unfold tailWord_257127
  simp only [CollatzResearch.WordTrace]
  refine ⟨9378192139480267640553635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6252128092986845093702423 9378192139480267640553635)
  ·
    refine ⟨14067288209220401460830453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9378192139480267640553635 14067288209220401460830453)
    ·
      refine ⟨1318808269614412636952855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 14067288209220401460830453 1318808269614412636952855)
      ·
        refine ⟨1978212404421618955429283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1318808269614412636952855 1978212404421618955429283)
        ·
          refine ⟨2967318606632428433143925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1978212404421618955429283 2967318606632428433143925)
          ·
            refine ⟨278186119371790165607243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 2967318606632428433143925 278186119371790165607243)
            ·
              refine ⟨417279179057685248410865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 278186119371790165607243 417279179057685248410865)
              ·
                refine ⟨312959384293263936308149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417279179057685248410865 312959384293263936308149)
                ·
                  refine ⟨29339942277493494028889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 312959384293263936308149 29339942277493494028889)
                  ·
                    rfl

theorem cell22_257127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 5, 1, 2, 5].length) (baseStart_257127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257127 prefixEnd_257127 := by exact prefixLift 257127
  have htrace : WordTrace (prefixWord ++ tailWord_257127) baseStart_257127 baseEnd_257127 := by
    simpa [prefixWord, tailWord_257127, baseEnd_257127] using wordTrace_append hprefix tailTrace_257127
  have hstable : (prefixWord ++ tailWord_257127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257127).length < 2 ^ (prefixWord ++ tailWord_257127).sum := by decide
  have hdescent : baseEnd_257127 < baseStart_257127 := by decide
  rcases family_descends (prefixWord ++ tailWord_257127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257189 : List Nat := [1, 3, 1, 2, 1, 5, 3, 2, 4]
def baseStart_257189 : Nat := 118140960795 + 257189 * 2 ^ 59
def prefixEnd_257189 : Nat := 4983230072969 + 3 ^ 40 * 257189 * 2
def baseEnd_257189 : Nat := 29347016899844329012159

theorem tailTrace_257189 : CollatzResearch.WordTrace tailWord_257189 prefixEnd_257189 29347016899844329012159 := by
  unfold tailWord_257189
  simp only [CollatzResearch.WordTrace]
  refine ⟨9380453465255652229310621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6253635643503768152873747 9380453465255652229310621)
  ·
    refine ⟨3517670049470869585991483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9380453465255652229310621 3517670049470869585991483)
    ·
      refine ⟨5276505074206304378987225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3517670049470869585991483 5276505074206304378987225)
      ·
        refine ⟨3957378805654728284240419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5276505074206304378987225 3957378805654728284240419)
        ·
          refine ⟨5936068208482092426360629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3957378805654728284240419 5936068208482092426360629)
          ·
            refine ⟨556506394545196164971309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 5936068208482092426360629 556506394545196164971309)
            ·
              refine ⟨208689897954448561864241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 556506394545196164971309 208689897954448561864241)
              ·
                refine ⟨156517423465836421398181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 208689897954448561864241 156517423465836421398181)
                ·
                  refine ⟨29347016899844329012159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156517423465836421398181 29347016899844329012159)
                  ·
                    rfl

theorem cell22_257189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 3, 2, 4].length) (baseStart_257189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257189 prefixEnd_257189 := by exact prefixLift 257189
  have htrace : WordTrace (prefixWord ++ tailWord_257189) baseStart_257189 baseEnd_257189 := by
    simpa [prefixWord, tailWord_257189, baseEnd_257189] using wordTrace_append hprefix tailTrace_257189
  have hstable : (prefixWord ++ tailWord_257189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257189).length < 2 ^ (prefixWord ++ tailWord_257189).sum := by decide
  have hdescent : baseEnd_257189 < baseStart_257189 := by decide
  rcases family_descends (prefixWord ++ tailWord_257189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257217 : List Nat := [1, 2, 6, 1, 1, 1, 2, 8]
def baseStart_257217 : Nat := 118140960795 + 257217 * 2 ^ 59
def prefixEnd_257217 : Nat := 4983230072969 + 3 ^ 40 * 257217 * 2
def baseEnd_257217 : Nat := 9783403963527805259599

theorem tailTrace_257217 : CollatzResearch.WordTrace tailWord_257217 prefixEnd_257217 9783403963527805259599 := by
  unfold tailWord_257217
  simp only [CollatzResearch.WordTrace]
  refine ⟨9381474709154213011329905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6254316472769475340886603 9381474709154213011329905)
  ·
    refine ⟨7036106031865659758497429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9381474709154213011329905 7036106031865659758497429)
    ·
      refine ⟨329817470243702801179567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 7036106031865659758497429 329817470243702801179567)
      ·
        refine ⟨494726205365554201769351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 329817470243702801179567 494726205365554201769351)
        ·
          refine ⟨742089308048331302654027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 494726205365554201769351 742089308048331302654027)
          ·
            refine ⟨1113133962072496953981041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 742089308048331302654027 1113133962072496953981041)
            ·
              refine ⟨834850471554372715485781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1113133962072496953981041 834850471554372715485781)
              ·
                refine ⟨9783403963527805259599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 834850471554372715485781 9783403963527805259599)
                ·
                  rfl

theorem cell22_257217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 2, 8].length) (baseStart_257217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257217 prefixEnd_257217 := by exact prefixLift 257217
  have htrace : WordTrace (prefixWord ++ tailWord_257217) baseStart_257217 baseEnd_257217 := by
    simpa [prefixWord, tailWord_257217, baseEnd_257217] using wordTrace_append hprefix tailTrace_257217
  have hstable : (prefixWord ++ tailWord_257217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257217).length < 2 ^ (prefixWord ++ tailWord_257217).sum := by decide
  have hdescent : baseEnd_257217 < baseStart_257217 := by decide
  rcases family_descends (prefixWord ++ tailWord_257217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257238 : List Nat := [5, 2, 1, 2, 2, 1, 2, 2, 2, 3]
def baseStart_257238 : Nat := 118140960795 + 257238 * 2 ^ 59
def prefixEnd_257238 : Nat := 4983230072969 + 3 ^ 40 * 257238 * 2
def baseEnd_257238 : Nat := 88057824400913192561327

theorem tailTrace_257238 : CollatzResearch.WordTrace tailWord_257238 prefixEnd_257238 88057824400913192561327 := by
  unfold tailWord_257238
  simp only [CollatzResearch.WordTrace]
  refine ⟨586390040129883349865273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6254827094718755731896245 586390040129883349865273)
  ·
    refine ⟨439792530097412512398955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 586390040129883349865273 439792530097412512398955)
    ·
      refine ⟨659688795146118768598433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 439792530097412512398955 659688795146118768598433)
      ·
        refine ⟨494766596359589076448825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 659688795146118768598433 494766596359589076448825)
        ·
          refine ⟨371074947269691807336619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 494766596359589076448825 371074947269691807336619)
          ·
            refine ⟨556612420904537711004929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371074947269691807336619 556612420904537711004929)
            ·
              refine ⟨417459315678403283253697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 556612420904537711004929 417459315678403283253697)
              ·
                refine ⟨313094486758802462440273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 417459315678403283253697 313094486758802462440273)
                ·
                  refine ⟨234820865069101846830205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 313094486758802462440273 234820865069101846830205)
                  ·
                    refine ⟨88057824400913192561327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 234820865069101846830205 88057824400913192561327)
                    ·
                      rfl

theorem cell22_257238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 1, 2, 2, 2, 3].length) (baseStart_257238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257238 prefixEnd_257238 := by exact prefixLift 257238
  have htrace : WordTrace (prefixWord ++ tailWord_257238) baseStart_257238 baseEnd_257238 := by
    simpa [prefixWord, tailWord_257238, baseEnd_257238] using wordTrace_append hprefix tailTrace_257238
  have hstable : (prefixWord ++ tailWord_257238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257238).length < 2 ^ (prefixWord ++ tailWord_257238).sum := by decide
  have hdescent : baseEnd_257238 < baseStart_257238 := by decide
  rcases family_descends (prefixWord ++ tailWord_257238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257260 : List Nat := [2, 2, 1, 1, 2, 4, 1, 1, 1, 7]
def baseStart_257260 : Nat := 118140960795 + 257260 * 2 ^ 59
def prefixEnd_257260 : Nat := 4983230072969 + 3 ^ 40 * 257260 * 2
def baseEnd_257260 : Nat := 88065355450512468511259

theorem tailTrace_257260 : CollatzResearch.WordTrace tailWord_257260 prefixEnd_257260 88065355450512468511259 := by
  unfold tailWord_257260
  simp only [CollatzResearch.WordTrace]
  refine ⟨4691521523999215677572617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6255362031998954236763489 4691521523999215677572617)
  ·
    refine ⟨3518641142999411758179463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4691521523999215677572617 3518641142999411758179463)
    ·
      refine ⟨5277961714499117637269195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3518641142999411758179463 5277961714499117637269195)
      ·
        refine ⟨7916942571748676455903793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5277961714499117637269195 7916942571748676455903793)
        ·
          refine ⟨5937706928811507341927845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7916942571748676455903793 5937706928811507341927845)
          ·
            refine ⟨1113320049152157626611471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5937706928811507341927845 1113320049152157626611471)
            ·
              refine ⟨1669980073728236439917207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1113320049152157626611471 1669980073728236439917207)
              ·
                refine ⟨2504970110592354659875811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1669980073728236439917207 2504970110592354659875811)
                ·
                  refine ⟨3757455165888531989813717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2504970110592354659875811 3757455165888531989813717)
                  ·
                    refine ⟨88065355450512468511259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3757455165888531989813717 88065355450512468511259)
                    ·
                      rfl

theorem cell22_257260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 7].length) (baseStart_257260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257260 prefixEnd_257260 := by exact prefixLift 257260
  have htrace : WordTrace (prefixWord ++ tailWord_257260) baseStart_257260 baseEnd_257260 := by
    simpa [prefixWord, tailWord_257260, baseEnd_257260] using wordTrace_append hprefix tailTrace_257260
  have hstable : (prefixWord ++ tailWord_257260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257260).length < 2 ^ (prefixWord ++ tailWord_257260).sum := by decide
  have hdescent : baseEnd_257260 < baseStart_257260 := by decide
  rcases family_descends (prefixWord ++ tailWord_257260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257262 : List Nat := [4, 1, 2, 1, 1, 1, 4, 3, 5]
def baseStart_257262 : Nat := 118140960795 + 257262 * 2 ^ 59
def prefixEnd_257262 : Nat := 4983230072969 + 3 ^ 40 * 257262 * 2
def baseEnd_257262 : Nat := 29355346697128376653751

theorem tailTrace_257262 : CollatzResearch.WordTrace tailWord_257262 prefixEnd_257262 29355346697128376653751 := by
  unfold tailWord_257262
  simp only [CollatzResearch.WordTrace]
  refine ⟨1172889499248898212089755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6255410662660790464478693 1172889499248898212089755)
  ·
    refine ⟨1759334248873347318134633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1172889499248898212089755 1759334248873347318134633)
    ·
      refine ⟨1319500686655010488600975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1759334248873347318134633 1319500686655010488600975)
      ·
        refine ⟨1979251029982515732901463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1319500686655010488600975 1979251029982515732901463)
        ·
          refine ⟨2968876544973773599352195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1979251029982515732901463 2968876544973773599352195)
          ·
            refine ⟨4453314817460660399028293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2968876544973773599352195 4453314817460660399028293)
            ·
              refine ⟨834996528273873824817805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4453314817460660399028293 834996528273873824817805)
              ·
                refine ⟨313123698102702684306677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 834996528273873824817805 313123698102702684306677)
                ·
                  refine ⟨29355346697128376653751, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 313123698102702684306677 29355346697128376653751)
                  ·
                    rfl

theorem cell22_257262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 4, 3, 5].length) (baseStart_257262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257262 prefixEnd_257262 := by exact prefixLift 257262
  have htrace : WordTrace (prefixWord ++ tailWord_257262) baseStart_257262 baseEnd_257262 := by
    simpa [prefixWord, tailWord_257262, baseEnd_257262] using wordTrace_append hprefix tailTrace_257262
  have hstable : (prefixWord ++ tailWord_257262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257262).length < 2 ^ (prefixWord ++ tailWord_257262).sum := by decide
  have hdescent : baseEnd_257262 < baseStart_257262 := by decide
  rcases family_descends (prefixWord ++ tailWord_257262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257268 : List Nat := [2, 6, 1, 2, 1, 1, 3, 6]
def baseStart_257268 : Nat := 118140960795 + 257268 * 2 ^ 59
def prefixEnd_257268 : Nat := 4983230072969 + 3 ^ 40 * 257268 * 2
def baseEnd_257268 : Nat := 9785343779333679367915

theorem tailTrace_257268 : CollatzResearch.WordTrace tailWord_257268 prefixEnd_257268 9785343779333679367915 := by
  unfold tailWord_257268
  simp only [CollatzResearch.WordTrace]
  refine ⟨4691667415984724360718229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6255556554646299147624305 4691667415984724360718229)
  ·
    refine ⟨219921910124283954408667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4691667415984724360718229 219921910124283954408667)
    ·
      refine ⟨329882865186425931613001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 219921910124283954408667 329882865186425931613001)
      ·
        refine ⟨247412148889819448709751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 329882865186425931613001 247412148889819448709751)
        ·
          refine ⟨371118223334729173064627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 247412148889819448709751 371118223334729173064627)
          ·
            refine ⟨556677335002093759596941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 371118223334729173064627 556677335002093759596941)
            ·
              refine ⟨208754000625785159848853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 556677335002093759596941 208754000625785159848853)
              ·
                refine ⟨9785343779333679367915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 208754000625785159848853 9785343779333679367915)
                ·
                  rfl

theorem cell22_257268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 3, 6].length) (baseStart_257268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257268 prefixEnd_257268 := by exact prefixLift 257268
  have htrace : WordTrace (prefixWord ++ tailWord_257268) baseStart_257268 baseEnd_257268 := by
    simpa [prefixWord, tailWord_257268, baseEnd_257268] using wordTrace_append hprefix tailTrace_257268
  have hstable : (prefixWord ++ tailWord_257268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257268).length < 2 ^ (prefixWord ++ tailWord_257268).sum := by decide
  have hdescent : baseEnd_257268 < baseStart_257268 := by decide
  rcases family_descends (prefixWord ++ tailWord_257268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257290 : List Nat := [3, 1, 2, 2, 1, 1, 1, 1, 10]
def baseStart_257290 : Nat := 118140960795 + 257290 * 2 ^ 59
def prefixEnd_257290 : Nat := 4983230072969 + 3 ^ 40 * 257290 * 2
def baseEnd_257290 : Nat := 29358541687867463420389

theorem tailTrace_257290 : CollatzResearch.WordTrace tailWord_257290 prefixEnd_257290 29358541687867463420389 := by
  unfold tailWord_257290
  simp only [CollatzResearch.WordTrace]
  refine ⟨2346034309472436619684331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6256091491926497652491549 2346034309472436619684331)
  ·
    refine ⟨3519051464208654929526497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2346034309472436619684331 3519051464208654929526497)
    ·
      refine ⟨2639288598156491197144873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3519051464208654929526497 2639288598156491197144873)
      ·
        refine ⟨1979466448617368397858655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2639288598156491197144873 1979466448617368397858655)
        ·
          refine ⟨2969199672926052596787983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1979466448617368397858655 2969199672926052596787983)
          ·
            refine ⟨4453799509389078895181975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2969199672926052596787983 4453799509389078895181975)
            ·
              refine ⟨6680699264083618342772963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4453799509389078895181975 6680699264083618342772963)
              ·
                refine ⟨10021048896125427514159445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6680699264083618342772963 10021048896125427514159445)
                ·
                  refine ⟨29358541687867463420389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 10021048896125427514159445 29358541687867463420389)
                  ·
                    rfl

theorem cell22_257290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 1, 10].length) (baseStart_257290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257290 prefixEnd_257290 := by exact prefixLift 257290
  have htrace : WordTrace (prefixWord ++ tailWord_257290) baseStart_257290 baseEnd_257290 := by
    simpa [prefixWord, tailWord_257290, baseEnd_257290] using wordTrace_append hprefix tailTrace_257290
  have hstable : (prefixWord ++ tailWord_257290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257290).length < 2 ^ (prefixWord ++ tailWord_257290).sum := by decide
  have hdescent : baseEnd_257290 < baseStart_257290 := by decide
  rcases family_descends (prefixWord ++ tailWord_257290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257444 : List Nat := [2, 3, 1, 2, 1, 1, 1, 6, 1, 4]
def baseStart_257444 : Nat := 118140960795 + 257444 * 2 ^ 59
def prefixEnd_257444 : Nat := 4983230072969 + 3 ^ 40 * 257444 * 2
def baseEnd_257444 : Nat := 88128342410797321910695

theorem tailTrace_257444 : CollatzResearch.WordTrace tailWord_257444 prefixEnd_257444 88128342410797321910695 := by
  unfold tailWord_257444
  simp only [CollatzResearch.WordTrace]
  refine ⟨4694877039665915389921693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6259836052887887186562257 4694877039665915389921693)
  ·
    refine ⟨1760578889874718271220635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4694877039665915389921693 1760578889874718271220635)
    ·
      refine ⟨2640868334812077406830953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1760578889874718271220635 2640868334812077406830953)
      ·
        refine ⟨1980651251109058055123215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2640868334812077406830953 1980651251109058055123215)
        ·
          refine ⟨2970976876663587082684823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1980651251109058055123215 2970976876663587082684823)
          ·
            refine ⟨4456465314995380624027235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2970976876663587082684823 4456465314995380624027235)
            ·
              refine ⟨6684697972493070936040853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4456465314995380624027235 6684697972493070936040853)
              ·
                refine ⟨313345217460612700126915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 6684697972493070936040853 313345217460612700126915)
                ·
                  refine ⟨470017826190919050190373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313345217460612700126915 470017826190919050190373)
                  ·
                    refine ⟨88128342410797321910695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 470017826190919050190373 88128342410797321910695)
                    ·
                      rfl

theorem cell22_257444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 6, 1, 4].length) (baseStart_257444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257444 prefixEnd_257444 := by exact prefixLift 257444
  have htrace : WordTrace (prefixWord ++ tailWord_257444) baseStart_257444 baseEnd_257444 := by
    simpa [prefixWord, tailWord_257444, baseEnd_257444] using wordTrace_append hprefix tailTrace_257444
  have hstable : (prefixWord ++ tailWord_257444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257444).length < 2 ^ (prefixWord ++ tailWord_257444).sum := by decide
  have hdescent : baseEnd_257444 < baseStart_257444 := by decide
  rcases family_descends (prefixWord ++ tailWord_257444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257461 : List Nat := [1, 3, 3, 2, 2, 2, 1, 3, 1, 4]
def baseStart_257461 : Nat := 118140960795 + 257461 * 2 ^ 59
def prefixEnd_257461 : Nat := 4983230072969 + 3 ^ 40 * 257461 * 2
def baseEnd_257461 : Nat := 88134161858214944235643

theorem tailTrace_257461 : CollatzResearch.WordTrace tailWord_257461 prefixEnd_257461 88134161858214944235643 := by
  unfold tailWord_257461
  simp only [CollatzResearch.WordTrace]
  refine ⟨9390374120270242683212237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6260249413513495122141491 9390374120270242683212237)
  ·
    refine ⟨3521390295101341006204589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9390374120270242683212237 3521390295101341006204589)
    ·
      refine ⟨1320521360663002877326721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3521390295101341006204589 1320521360663002877326721)
      ·
        refine ⟨990391020497252157995041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1320521360663002877326721 990391020497252157995041)
        ·
          refine ⟨742793265372939118496281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 990391020497252157995041 742793265372939118496281)
          ·
            refine ⟨557094949029704338872211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 742793265372939118496281 557094949029704338872211)
            ·
              refine ⟨835642423544556508308317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 557094949029704338872211 835642423544556508308317)
              ·
                refine ⟨313365908829208690615619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 835642423544556508308317 313365908829208690615619)
                ·
                  refine ⟨470048863243813035923429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313365908829208690615619 470048863243813035923429)
                  ·
                    refine ⟨88134161858214944235643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 470048863243813035923429 88134161858214944235643)
                    ·
                      rfl

theorem cell22_257461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 2, 1, 3, 1, 4].length) (baseStart_257461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257461 prefixEnd_257461 := by exact prefixLift 257461
  have htrace : WordTrace (prefixWord ++ tailWord_257461) baseStart_257461 baseEnd_257461 := by
    simpa [prefixWord, tailWord_257461, baseEnd_257461] using wordTrace_append hprefix tailTrace_257461
  have hstable : (prefixWord ++ tailWord_257461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257461).length < 2 ^ (prefixWord ++ tailWord_257461).sum := by decide
  have hdescent : baseEnd_257461 < baseStart_257461 := by decide
  rcases family_descends (prefixWord ++ tailWord_257461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257476 : List Nat := [2, 3, 3, 2, 1, 2, 2, 1, 6]
def baseStart_257476 : Nat := 118140960795 + 257476 * 2 ^ 59
def prefixEnd_257476 : Nat := 4983230072969 + 3 ^ 40 * 257476 * 2
def baseEnd_257476 : Nat := 29379765554919968370199

theorem tailTrace_257476 : CollatzResearch.WordTrace tailWord_257476 prefixEnd_257476 29379765554919968370199 := by
  unfold tailWord_257476
  simp only [CollatzResearch.WordTrace]
  refine ⟨4695460607607950122504141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6260614143477266830005521 4695460607607950122504141)
  ·
    refine ⟨1760797727852981295939053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4695460607607950122504141 1760797727852981295939053)
    ·
      refine ⟨660299147944867985977145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1760797727852981295939053 660299147944867985977145)
      ·
        refine ⟨495224360958650989482859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 660299147944867985977145 495224360958650989482859)
        ·
          refine ⟨742836541437976484224289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495224360958650989482859 742836541437976484224289)
          ·
            refine ⟨557127406078482363168217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 742836541437976484224289 557127406078482363168217)
            ·
              refine ⟨417845554558861772376163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 557127406078482363168217 417845554558861772376163)
              ·
                refine ⟨626768331838292658564245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 417845554558861772376163 626768331838292658564245)
                ·
                  refine ⟨29379765554919968370199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 626768331838292658564245 29379765554919968370199)
                  ·
                    rfl

theorem cell22_257476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 2, 2, 1, 6].length) (baseStart_257476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257476 prefixEnd_257476 := by exact prefixLift 257476
  have htrace : WordTrace (prefixWord ++ tailWord_257476) baseStart_257476 baseEnd_257476 := by
    simpa [prefixWord, tailWord_257476, baseEnd_257476] using wordTrace_append hprefix tailTrace_257476
  have hstable : (prefixWord ++ tailWord_257476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257476).length < 2 ^ (prefixWord ++ tailWord_257476).sum := by decide
  have hdescent : baseEnd_257476 < baseStart_257476 := by decide
  rcases family_descends (prefixWord ++ tailWord_257476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257519 : List Nat := [1, 1, 2, 1, 4, 1, 2, 2, 5, 3]
def baseStart_257519 : Nat := 118140960795 + 257519 * 2 ^ 59
def prefixEnd_257519 : Nat := 4983230072969 + 3 ^ 40 * 257519 * 2
def baseEnd_257519 : Nat := 88154016443522126285465

theorem tailTrace_257519 : CollatzResearch.WordTrace tailWord_257519 prefixEnd_257519 88154016443522126285465 := by
  unfold tailWord_257519
  simp only [CollatzResearch.WordTrace]
  refine ⟨9392489554060118588823611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6261659702706745725882407 9392489554060118588823611)
  ·
    refine ⟨14088734331090177883235417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9392489554060118588823611 14088734331090177883235417)
    ·
      refine ⟨10566550748317633412426563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14088734331090177883235417 10566550748317633412426563)
      ·
        refine ⟨15849826122476450118639845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10566550748317633412426563 15849826122476450118639845)
        ·
          refine ⟨2971842397964334397244971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15849826122476450118639845 2971842397964334397244971)
          ·
            refine ⟨4457763596946501595867457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2971842397964334397244971 4457763596946501595867457)
            ·
              refine ⟨3343322697709876196900593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4457763596946501595867457 3343322697709876196900593)
              ·
                refine ⟨2507492023282407147675445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3343322697709876196900593 2507492023282407147675445)
                ·
                  refine ⟨235077377182725670094573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2507492023282407147675445 235077377182725670094573)
                  ·
                    refine ⟨88154016443522126285465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 235077377182725670094573 88154016443522126285465)
                    ·
                      rfl

theorem cell22_257519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 2, 5, 3].length) (baseStart_257519 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257519 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257519 prefixEnd_257519 := by exact prefixLift 257519
  have htrace : WordTrace (prefixWord ++ tailWord_257519) baseStart_257519 baseEnd_257519 := by
    simpa [prefixWord, tailWord_257519, baseEnd_257519] using wordTrace_append hprefix tailTrace_257519
  have hstable : (prefixWord ++ tailWord_257519).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257519).length < 2 ^ (prefixWord ++ tailWord_257519).sum := by decide
  have hdescent : baseEnd_257519 < baseStart_257519 := by decide
  rcases family_descends (prefixWord ++ tailWord_257519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257594 : List Nat := [3, 1, 1, 1, 3, 2, 2, 3, 6]
def baseStart_257594 : Nat := 118140960795 + 257594 * 2 ^ 59
def prefixEnd_257594 : Nat := 4983230072969 + 3 ^ 40 * 257594 * 2
def baseEnd_257594 : Nat := 29393230158748976886745

theorem tailTrace_257594 : CollatzResearch.WordTrace tailWord_257594 prefixEnd_257594 29393230158748976886745 := by
  unfold tailWord_257594
  simp only [CollatzResearch.WordTrace]
  refine ⟨2348806257197101599450959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6263483352525604265202557 2348806257197101599450959)
  ·
    refine ⟨3523209385795652399176439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2348806257197101599450959 3523209385795652399176439)
    ·
      refine ⟨5284814078693478598764659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3523209385795652399176439 5284814078693478598764659)
      ·
        refine ⟨7927221118040217898146989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5284814078693478598764659 7927221118040217898146989)
        ·
          refine ⟨2972707919265081711805121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7927221118040217898146989 2972707919265081711805121)
          ·
            refine ⟨2229530939448811283853841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2972707919265081711805121 2229530939448811283853841)
            ·
              refine ⟨1672148204586608462890381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2229530939448811283853841 1672148204586608462890381)
              ·
                refine ⟨627055576719978173583893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1672148204586608462890381 627055576719978173583893)
                ·
                  refine ⟨29393230158748976886745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 627055576719978173583893 29393230158748976886745)
                  ·
                    rfl

theorem cell22_257594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 2, 3, 6].length) (baseStart_257594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257594 prefixEnd_257594 := by exact prefixLift 257594
  have htrace : WordTrace (prefixWord ++ tailWord_257594) baseStart_257594 baseEnd_257594 := by
    simpa [prefixWord, tailWord_257594, baseEnd_257594] using wordTrace_append hprefix tailTrace_257594
  have hstable : (prefixWord ++ tailWord_257594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257594).length < 2 ^ (prefixWord ++ tailWord_257594).sum := by decide
  have hdescent : baseEnd_257594 < baseStart_257594 := by decide
  rcases family_descends (prefixWord ++ tailWord_257594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257628 : List Nat := [2, 2, 4, 1, 2, 1, 1, 5, 4]
def baseStart_257628 : Nat := 118140960795 + 257628 * 2 ^ 59
def prefixEnd_257628 : Nat := 4983230072969 + 3 ^ 40 * 257628 * 2
def baseEnd_257628 : Nat := 29397109790360725103377

theorem tailTrace_257628 : CollatzResearch.WordTrace tailWord_257628 prefixEnd_257628 29397109790360725103377 := by
  unfold tailWord_257628
  simp only [CollatzResearch.WordTrace]
  refine ⟨4698232555332615102270769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6264310073776820136361025 4698232555332615102270769)
  ·
    refine ⟨3523674416499461326703077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4698232555332615102270769 3523674416499461326703077)
    ·
      refine ⟨660688953093648998756827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 3523674416499461326703077 660688953093648998756827)
      ·
        refine ⟨991033429640473498135241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 660688953093648998756827 991033429640473498135241)
        ·
          refine ⟨743275072230355123601431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 991033429640473498135241 743275072230355123601431)
          ·
            refine ⟨1114912608345532685402147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743275072230355123601431 1114912608345532685402147)
            ·
              refine ⟨1672368912518299028103221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1114912608345532685402147 1672368912518299028103221)
              ·
                refine ⟨156784585548590533884677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1672368912518299028103221 156784585548590533884677)
                ·
                  refine ⟨29397109790360725103377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 156784585548590533884677 29397109790360725103377)
                  ·
                    rfl

theorem cell22_257628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 1, 1, 5, 4].length) (baseStart_257628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257628 prefixEnd_257628 := by exact prefixLift 257628
  have htrace : WordTrace (prefixWord ++ tailWord_257628) baseStart_257628 baseEnd_257628 := by
    simpa [prefixWord, tailWord_257628, baseEnd_257628] using wordTrace_append hprefix tailTrace_257628
  have hstable : (prefixWord ++ tailWord_257628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257628).length < 2 ^ (prefixWord ++ tailWord_257628).sum := by decide
  have hdescent : baseEnd_257628 < baseStart_257628 := by decide
  rcases family_descends (prefixWord ++ tailWord_257628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257756 : List Nat := [2, 2, 5, 1, 2, 2, 2, 2, 1, 3]
def baseStart_257756 : Nat := 118140960795 + 257756 * 2 ^ 59
def prefixEnd_257756 : Nat := 4983230072969 + 3 ^ 40 * 257756 * 2
def baseEnd_257756 : Nat := 88235146386932508109739

theorem tailTrace_257756 : CollatzResearch.WordTrace tailWord_257756 prefixEnd_257756 88235146386932508109739 := by
  unfold tailWord_257756
  simp only [CollatzResearch.WordTrace]
  refine ⟨4700566827100754032600561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6267422436134338710134081 4700566827100754032600561)
  ·
    refine ⟨3525425120325565524450421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4700566827100754032600561 3525425120325565524450421)
    ·
      refine ⟨330508605030521767917227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 3525425120325565524450421 330508605030521767917227)
      ·
        refine ⟨495762907545782651875841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330508605030521767917227 495762907545782651875841)
        ·
          refine ⟨371822180659336988906881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 495762907545782651875841 371822180659336988906881)
          ·
            refine ⟨278866635494502741680161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 371822180659336988906881 278866635494502741680161)
            ·
              refine ⟨209149976620877056260121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278866635494502741680161 209149976620877056260121)
              ·
                refine ⟨156862482465657792195091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209149976620877056260121 156862482465657792195091)
                ·
                  refine ⟨235293723698486688292637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156862482465657792195091 235293723698486688292637)
                  ·
                    refine ⟨88235146386932508109739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 235293723698486688292637 88235146386932508109739)
                    ·
                      rfl

theorem cell22_257756_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_257756 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257756 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257756 prefixEnd_257756 := by exact prefixLift 257756
  have htrace : WordTrace (prefixWord ++ tailWord_257756) baseStart_257756 baseEnd_257756 := by
    simpa [prefixWord, tailWord_257756, baseEnd_257756] using wordTrace_append hprefix tailTrace_257756
  have hstable : (prefixWord ++ tailWord_257756).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257756).length < 2 ^ (prefixWord ++ tailWord_257756).sum := by decide
  have hdescent : baseEnd_257756 < baseStart_257756 := by decide
  rcases family_descends (prefixWord ++ tailWord_257756) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257778 : List Nat := [3, 2, 1, 3, 1, 1, 4, 1, 1, 5]
def baseStart_257778 : Nat := 118140960795 + 257778 * 2 ^ 59
def prefixEnd_257778 : Nat := 4983230072969 + 3 ^ 40 * 257778 * 2
def baseEnd_257778 : Nat := 88242677436531784059671

theorem tailTrace_257778 : CollatzResearch.WordTrace tailWord_257778 prefixEnd_257778 88242677436531784059671 := by
  unfold tailWord_257778
  simp only [CollatzResearch.WordTrace]
  refine ⟨2350484015030451455625497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6267957373414537215001325 2350484015030451455625497)
  ·
    refine ⟨1762863011272838591719123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2350484015030451455625497 1762863011272838591719123)
    ·
      refine ⟨2644294516909257887578685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1762863011272838591719123 2644294516909257887578685)
      ·
        refine ⟨991610443840971707842007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2644294516909257887578685 991610443840971707842007)
        ·
          refine ⟨1487415665761457561763011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 991610443840971707842007 1487415665761457561763011)
          ·
            refine ⟨2231123498642186342644517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1487415665761457561763011 2231123498642186342644517)
            ·
              refine ⟨418335655995409939245847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2231123498642186342644517 418335655995409939245847)
              ·
                refine ⟨627503483993114908868771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418335655995409939245847 627503483993114908868771)
                ·
                  refine ⟨941255225989672363303157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 627503483993114908868771 941255225989672363303157)
                  ·
                    refine ⟨88242677436531784059671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 941255225989672363303157 88242677436531784059671)
                    ·
                      rfl

theorem cell22_257778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_257778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257778 prefixEnd_257778 := by exact prefixLift 257778
  have htrace : WordTrace (prefixWord ++ tailWord_257778) baseStart_257778 baseEnd_257778 := by
    simpa [prefixWord, tailWord_257778, baseEnd_257778] using wordTrace_append hprefix tailTrace_257778
  have hstable : (prefixWord ++ tailWord_257778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257778).length < 2 ^ (prefixWord ++ tailWord_257778).sum := by decide
  have hdescent : baseEnd_257778 < baseStart_257778 := by decide
  rcases family_descends (prefixWord ++ tailWord_257778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257780 : List Nat := [2, 6, 1, 1, 1, 1, 1, 1, 8]
def baseStart_257780 : Nat := 118140960795 + 257780 * 2 ^ 59
def prefixEnd_257780 : Nat := 4983230072969 + 3 ^ 40 * 257780 * 2
def baseEnd_257780 : Nat := 29414454025801481836555

theorem tailTrace_257780 : CollatzResearch.WordTrace tailWord_257780 prefixEnd_257780 29414454025801481836555 := by
  unfold tailWord_257780
  simp only [CollatzResearch.WordTrace]
  refine ⟨4701004503057280082037397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6268006004076373442716529 4701004503057280082037397)
  ·
    refine ⟨220359586080810003845503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 4701004503057280082037397 220359586080810003845503)
    ·
      refine ⟨330539379121215005768255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 220359586080810003845503 330539379121215005768255)
      ·
        refine ⟨495809068681822508652383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 330539379121215005768255 495809068681822508652383)
        ·
          refine ⟨743713603022733762978575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495809068681822508652383 743713603022733762978575)
          ·
            refine ⟨1115570404534100644467863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743713603022733762978575 1115570404534100644467863)
            ·
              refine ⟨1673355606801150966701795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1115570404534100644467863 1673355606801150966701795)
              ·
                refine ⟨2510033410201726450052693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1673355606801150966701795 2510033410201726450052693)
                ·
                  refine ⟨29414454025801481836555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2510033410201726450052693 29414454025801481836555)
                  ·
                    rfl

theorem cell22_257780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 1, 8].length) (baseStart_257780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257780 prefixEnd_257780 := by exact prefixLift 257780
  have htrace : WordTrace (prefixWord ++ tailWord_257780) baseStart_257780 baseEnd_257780 := by
    simpa [prefixWord, tailWord_257780, baseEnd_257780] using wordTrace_append hprefix tailTrace_257780
  have hstable : (prefixWord ++ tailWord_257780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257780).length < 2 ^ (prefixWord ++ tailWord_257780).sum := by decide
  have hdescent : baseEnd_257780 < baseStart_257780 := by decide
  rcases family_descends (prefixWord ++ tailWord_257780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257793 : List Nat := [1, 2, 4, 1, 1, 1, 5, 1, 2, 4]
def baseStart_257793 : Nat := 118140960795 + 257793 * 2 ^ 59
def prefixEnd_257793 : Nat := 4983230072969 + 3 ^ 40 * 257793 * 2
def baseEnd_257793 : Nat := 88247812243076744934625

theorem tailTrace_257793 : CollatzResearch.WordTrace tailWord_257793 prefixEnd_257793 88247812243076744934625 := by
  unfold tailWord_257793
  simp only [CollatzResearch.WordTrace]
  refine ⟨9402483155067463384298033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6268322103378308922865355 9402483155067463384298033)
  ·
    refine ⟨7051862366300597538223525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9402483155067463384298033 7051862366300597538223525)
    ·
      refine ⟨1322224193681362038416911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7051862366300597538223525 1322224193681362038416911)
      ·
        refine ⟨1983336290522043057625367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1322224193681362038416911 1983336290522043057625367)
        ·
          refine ⟨2975004435783064586438051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1983336290522043057625367 2975004435783064586438051)
          ·
            refine ⟨4462506653674596879657077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2975004435783064586438051 4462506653674596879657077)
            ·
              refine ⟨418359998781993457467851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4462506653674596879657077 418359998781993457467851)
              ·
                refine ⟨627539998172990186201777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418359998781993457467851 627539998172990186201777)
                ·
                  refine ⟨470654998629742639651333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 627539998172990186201777 470654998629742639651333)
                  ·
                    refine ⟨88247812243076744934625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 470654998629742639651333 88247812243076744934625)
                    ·
                      rfl

theorem cell22_257793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 5, 1, 2, 4].length) (baseStart_257793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257793 prefixEnd_257793 := by exact prefixLift 257793
  have htrace : WordTrace (prefixWord ++ tailWord_257793) baseStart_257793 baseEnd_257793 := by
    simpa [prefixWord, tailWord_257793, baseEnd_257793] using wordTrace_append hprefix tailTrace_257793
  have hstable : (prefixWord ++ tailWord_257793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257793).length < 2 ^ (prefixWord ++ tailWord_257793).sum := by decide
  have hdescent : baseEnd_257793 < baseStart_257793 := by decide
  rcases family_descends (prefixWord ++ tailWord_257793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257799 : List Nat := [1, 1, 4, 4, 3, 1, 2, 1, 1, 4]
def baseStart_257799 : Nat := 118140960795 + 257799 * 2 ^ 59
def prefixEnd_257799 : Nat := 4983230072969 + 3 ^ 40 * 257799 * 2
def baseEnd_257799 : Nat := 88249866165694729284607

theorem tailTrace_257799 : CollatzResearch.WordTrace tailWord_257799 prefixEnd_257799 88249866165694729284607 := by
  unfold tailWord_257799
  simp only [CollatzResearch.WordTrace]
  refine ⟨9402701993045726409016451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6268467995363817606010967 9402701993045726409016451)
  ·
    refine ⟨14104052989568589613524677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9402701993045726409016451 14104052989568589613524677)
    ·
      refine ⟨2644509935544110552535877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14104052989568589613524677 2644509935544110552535877)
      ·
        refine ⟨495845612914520728600477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2644509935544110552535877 495845612914520728600477)
        ·
          refine ⟨185942104842945273225179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 495845612914520728600477 185942104842945273225179)
          ·
            refine ⟨278913157264417909837769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 185942104842945273225179 278913157264417909837769)
            ·
              refine ⟨209184867948313432378327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 278913157264417909837769 209184867948313432378327)
              ·
                refine ⟨313777301922470148567491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 209184867948313432378327 313777301922470148567491)
                ·
                  refine ⟨470665952883705222851237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313777301922470148567491 470665952883705222851237)
                  ·
                    refine ⟨88249866165694729284607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 470665952883705222851237 88249866165694729284607)
                    ·
                      rfl

theorem cell22_257799_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_257799 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257799 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257799 prefixEnd_257799 := by exact prefixLift 257799
  have htrace : WordTrace (prefixWord ++ tailWord_257799) baseStart_257799 baseEnd_257799 := by
    simpa [prefixWord, tailWord_257799, baseEnd_257799] using wordTrace_append hprefix tailTrace_257799
  have hstable : (prefixWord ++ tailWord_257799).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257799).length < 2 ^ (prefixWord ++ tailWord_257799).sum := by decide
  have hdescent : baseEnd_257799 < baseStart_257799 := by decide
  rcases family_descends (prefixWord ++ tailWord_257799) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257853 : List Nat := [1, 4, 1, 4, 1, 1, 1, 2, 7]
def baseStart_257853 : Nat := 118140960795 + 257853 * 2 ^ 59
def prefixEnd_257853 : Nat := 4983230072969 + 3 ^ 40 * 257853 * 2
def baseEnd_257853 : Nat := 29422783823085529478147

theorem tailTrace_257853 : CollatzResearch.WordTrace tailWord_257853 prefixEnd_257853 29422783823085529478147 := by
  unfold tailWord_257853
  simp only [CollatzResearch.WordTrace]
  refine ⟨9404671534850093631482213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6269781023233395754321475 9404671534850093631482213)
  ·
    refine ⟨1763375912784392555902915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9404671534850093631482213 1763375912784392555902915)
    ·
      refine ⟨2645063869176588833854373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1763375912784392555902915 2645063869176588833854373)
      ·
        refine ⟨495949475470610406347695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2645063869176588833854373 495949475470610406347695)
        ·
          refine ⟨743924213205915609521543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 495949475470610406347695 743924213205915609521543)
          ·
            refine ⟨1115886319808873414282315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 743924213205915609521543 1115886319808873414282315)
            ·
              refine ⟨1673829479713310121423473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1115886319808873414282315 1673829479713310121423473)
              ·
                refine ⟨1255372109784982591067605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1673829479713310121423473 1255372109784982591067605)
                ·
                  refine ⟨29422783823085529478147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1255372109784982591067605 29422783823085529478147)
                  ·
                    rfl

theorem cell22_257853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 1, 2, 7].length) (baseStart_257853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257853 prefixEnd_257853 := by exact prefixLift 257853
  have htrace : WordTrace (prefixWord ++ tailWord_257853) baseStart_257853 baseEnd_257853 := by
    simpa [prefixWord, tailWord_257853, baseEnd_257853] using wordTrace_append hprefix tailTrace_257853
  have hstable : (prefixWord ++ tailWord_257853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257853).length < 2 ^ (prefixWord ++ tailWord_257853).sum := by decide
  have hdescent : baseEnd_257853 < baseStart_257853 := by decide
  rcases family_descends (prefixWord ++ tailWord_257853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257874 : List Nat := [3, 2, 2, 1, 1, 4, 3, 2, 1, 3]
def baseStart_257874 : Nat := 118140960795 + 257874 * 2 ^ 59
def prefixEnd_257874 : Nat := 4983230072969 + 3 ^ 40 * 257874 * 2
def baseEnd_257874 : Nat := 88275540198419533659377

theorem tailTrace_257874 : CollatzResearch.WordTrace tailWord_257874 prefixEnd_257874 88275540198419533659377 := by
  unfold tailWord_257874
  simp only [CollatzResearch.WordTrace]
  refine ⟨2351359366943503554499169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6270291645182676145331117 2351359366943503554499169)
  ·
    refine ⟨1763519525207627665874377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2351359366943503554499169 1763519525207627665874377)
    ·
      refine ⟨1322639643905720749405783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1763519525207627665874377 1322639643905720749405783)
      ·
        refine ⟨1983959465858581124108675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1322639643905720749405783 1983959465858581124108675)
        ·
          refine ⟨2975939198787871686163013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1983959465858581124108675 2975939198787871686163013)
          ·
            refine ⟨557988599772725941155565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2975939198787871686163013 557988599772725941155565)
            ·
              refine ⟨209245724914772227933337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 557988599772725941155565 209245724914772227933337)
              ·
                refine ⟨156934293686079170950003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209245724914772227933337 156934293686079170950003)
                ·
                  refine ⟨235401440529118756425005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 156934293686079170950003 235401440529118756425005)
                  ·
                    refine ⟨88275540198419533659377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 235401440529118756425005 88275540198419533659377)
                    ·
                      rfl

theorem cell22_257874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 4, 3, 2, 1, 3].length) (baseStart_257874 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257874 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257874 prefixEnd_257874 := by exact prefixLift 257874
  have htrace : WordTrace (prefixWord ++ tailWord_257874) baseStart_257874 baseEnd_257874 := by
    simpa [prefixWord, tailWord_257874, baseEnd_257874] using wordTrace_append hprefix tailTrace_257874
  have hstable : (prefixWord ++ tailWord_257874).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257874).length < 2 ^ (prefixWord ++ tailWord_257874).sum := by decide
  have hdescent : baseEnd_257874 < baseStart_257874 := by decide
  rcases family_descends (prefixWord ++ tailWord_257874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257900 : List Nat := [2, 2, 1, 1, 4, 2, 3, 2, 1, 4]
def baseStart_257900 : Nat := 118140960795 + 257900 * 2 ^ 59
def prefixEnd_257900 : Nat := 4983230072969 + 3 ^ 40 * 257900 * 2
def baseEnd_257900 : Nat := 88284440529764132509297

theorem tailTrace_257900 : CollatzResearch.WordTrace tailWord_257900 prefixEnd_257900 88284440529764132509297 := by
  unfold tailWord_257900
  simp only [CollatzResearch.WordTrace]
  refine ⟨4703192882839910329221577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6270923843786547105628769 4703192882839910329221577)
  ·
    refine ⟨3527394662129932746916183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4703192882839910329221577 3527394662129932746916183)
    ·
      refine ⟨5291091993194899120374275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3527394662129932746916183 5291091993194899120374275)
      ·
        refine ⟨7936637989792348680561413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5291091993194899120374275 7936637989792348680561413)
        ·
          refine ⟨1488119623086065377605265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7936637989792348680561413 1488119623086065377605265)
          ·
            refine ⟨1116089717314549033203949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1488119623086065377605265 1116089717314549033203949)
            ·
              refine ⟨418533643992955887451481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1116089717314549033203949 418533643992955887451481)
              ·
                refine ⟨313900232994716915588611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 418533643992955887451481 313900232994716915588611)
                ·
                  refine ⟨470850349492075373382917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 313900232994716915588611 470850349492075373382917)
                  ·
                    refine ⟨88284440529764132509297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 470850349492075373382917 88284440529764132509297)
                    ·
                      rfl

theorem cell22_257900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 4].length) (baseStart_257900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257900 prefixEnd_257900 := by exact prefixLift 257900
  have htrace : WordTrace (prefixWord ++ tailWord_257900) baseStart_257900 baseEnd_257900 := by
    simpa [prefixWord, tailWord_257900, baseEnd_257900] using wordTrace_append hprefix tailTrace_257900
  have hstable : (prefixWord ++ tailWord_257900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257900).length < 2 ^ (prefixWord ++ tailWord_257900).sum := by decide
  have hdescent : baseEnd_257900 < baseStart_257900 := by decide
  rcases family_descends (prefixWord ++ tailWord_257900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257913 : List Nat := [1, 2, 1, 3, 2, 2, 3, 2, 1, 5]
def baseStart_257913 : Nat := 118140960795 + 257913 * 2 ^ 59
def prefixEnd_257913 : Nat := 4983230072969 + 3 ^ 40 * 257913 * 2
def baseEnd_257913 : Nat := 88288890695436431934257

theorem tailTrace_257913 : CollatzResearch.WordTrace tailWord_257913 prefixEnd_257913 88288890695436431934257 := by
  unfold tailWord_257913
  simp only [CollatzResearch.WordTrace]
  refine ⟨9406859914632723878666393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6271239943088482585777595 9406859914632723878666393)
  ·
    refine ⟨7055144935974542908999795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9406859914632723878666393 7055144935974542908999795)
    ·
      refine ⟨10582717403961814363499693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7055144935974542908999795 10582717403961814363499693)
      ·
        refine ⟨3968519026485680386312385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10582717403961814363499693 3968519026485680386312385)
        ·
          refine ⟨2976389269864260289734289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3968519026485680386312385 2976389269864260289734289)
          ·
            refine ⟨2232291952398195217300717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2976389269864260289734289 2232291952398195217300717)
            ·
              refine ⟨837109482149323206487769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2232291952398195217300717 837109482149323206487769)
              ·
                refine ⟨627832111611992404865827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 837109482149323206487769 627832111611992404865827)
                ·
                  refine ⟨941748167417988607298741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 627832111611992404865827 941748167417988607298741)
                  ·
                    refine ⟨88288890695436431934257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 941748167417988607298741 88288890695436431934257)
                    ·
                      rfl

theorem cell22_257913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 3, 2, 1, 5].length) (baseStart_257913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257913 prefixEnd_257913 := by exact prefixLift 257913
  have htrace : WordTrace (prefixWord ++ tailWord_257913) baseStart_257913 baseEnd_257913 := by
    simpa [prefixWord, tailWord_257913, baseEnd_257913] using wordTrace_append hprefix tailTrace_257913
  have hstable : (prefixWord ++ tailWord_257913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257913).length < 2 ^ (prefixWord ++ tailWord_257913).sum := by decide
  have hdescent : baseEnd_257913 < baseStart_257913 := by decide
  rcases family_descends (prefixWord ++ tailWord_257913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257943 : List Nat := [1, 1, 3, 3, 1, 3, 3, 7]
def baseStart_257943 : Nat := 118140960795 + 257943 * 2 ^ 59
def prefixEnd_257943 : Nat := 4983230072969 + 3 ^ 40 * 257943 * 2
def baseEnd_257943 : Nat := 9811017812058483742685

theorem tailTrace_257943 : CollatzResearch.WordTrace tailWord_257943 prefixEnd_257943 9811017812058483742685 := by
  unfold tailWord_257943
  simp only [CollatzResearch.WordTrace]
  refine ⟨9407954104524039002258483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6271969403016026001505655 9407954104524039002258483)
  ·
    refine ⟨14111931156786058503387725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9407954104524039002258483 14111931156786058503387725)
    ·
      refine ⟨5291974183794771938770397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14111931156786058503387725 5291974183794771938770397)
      ·
        refine ⟨1984490318923039477038899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5291974183794771938770397 1984490318923039477038899)
        ·
          refine ⟨2976735478384559215558349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1984490318923039477038899 2976735478384559215558349)
          ·
            refine ⟨1116275804394209705834381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2976735478384559215558349 1116275804394209705834381)
            ·
              refine ⟨418603426647828639687893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1116275804394209705834381 418603426647828639687893)
              ·
                refine ⟨9811017812058483742685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 418603426647828639687893 9811017812058483742685)
                ·
                  rfl

theorem cell22_257943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 3, 7].length) (baseStart_257943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257943 prefixEnd_257943 := by exact prefixLift 257943
  have htrace : WordTrace (prefixWord ++ tailWord_257943) baseStart_257943 baseEnd_257943 := by
    simpa [prefixWord, tailWord_257943, baseEnd_257943] using wordTrace_append hprefix tailTrace_257943
  have hstable : (prefixWord ++ tailWord_257943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257943).length < 2 ^ (prefixWord ++ tailWord_257943).sum := by decide
  have hdescent : baseEnd_257943 < baseStart_257943 := by decide
  rcases family_descends (prefixWord ++ tailWord_257943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_257992 : List Nat := [2, 1, 3, 1, 4, 2, 2, 1, 3, 3]
def baseStart_257992 : Nat := 118140960795 + 257992 * 2 ^ 59
def prefixEnd_257992 : Nat := 4983230072969 + 3 ^ 40 * 257992 * 2
def baseEnd_257992 : Nat := 88315934009906559209015

theorem tailTrace_257992 : CollatzResearch.WordTrace tailWord_257992 prefixEnd_257992 88315934009906559209015 := by
  unfold tailWord_257992
  simp only [CollatzResearch.WordTrace]
  refine ⟨4704870640673260185396115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6273160854231013580528153 4704870640673260185396115)
  ·
    refine ⟨7057305961009890278094173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4704870640673260185396115 7057305961009890278094173)
    ·
      refine ⟨2646489735378708854285315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7057305961009890278094173 2646489735378708854285315)
      ·
        refine ⟨3969734603068063281427973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2646489735378708854285315 3969734603068063281427973)
        ·
          refine ⟨744325238075261865267745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3969734603068063281427973 744325238075261865267745)
          ·
            refine ⟨558243928556446398950809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 744325238075261865267745 558243928556446398950809)
            ·
              refine ⟨418682946417334799213107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 558243928556446398950809 418682946417334799213107)
              ·
                refine ⟨628024419626002198819661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 418682946417334799213107 628024419626002198819661)
                ·
                  refine ⟨235509157359750824557373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 628024419626002198819661 235509157359750824557373)
                  ·
                    refine ⟨88315934009906559209015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 235509157359750824557373 88315934009906559209015)
                    ·
                      rfl

theorem cell22_257992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 2, 2, 1, 3, 3].length) (baseStart_257992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_257992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_257992 prefixEnd_257992 := by exact prefixLift 257992
  have htrace : WordTrace (prefixWord ++ tailWord_257992) baseStart_257992 baseEnd_257992 := by
    simpa [prefixWord, tailWord_257992, baseEnd_257992] using wordTrace_append hprefix tailTrace_257992
  have hstable : (prefixWord ++ tailWord_257992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_257992).length < 2 ^ (prefixWord ++ tailWord_257992).sum := by decide
  have hdescent : baseEnd_257992 < baseStart_257992 := by decide
  rcases family_descends (prefixWord ++ tailWord_257992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258048 : List Nat := [2, 1, 1, 2, 1, 1, 1, 3, 5, 5]
def baseStart_258048 : Nat := 118140960795 + 258048 * 2 ^ 59
def prefixEnd_258048 : Nat := 4983230072969 + 3 ^ 40 * 258048 * 2
def baseEnd_258048 : Nat := 88335103954341079808843

theorem tailTrace_258048 : CollatzResearch.WordTrace tailWord_258048 prefixEnd_258048 88335103954341079808843 := by
  unfold tailWord_258048
  simp only [CollatzResearch.WordTrace]
  refine ⟨4705891884571820967415399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6274522512762427956553865 4705891884571820967415399)
  ·
    refine ⟨7058837826857731451123099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4705891884571820967415399 7058837826857731451123099)
    ·
      refine ⟨10588256740286597176684649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7058837826857731451123099 10588256740286597176684649)
      ·
        refine ⟨7941192555214947882513487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10588256740286597176684649 7941192555214947882513487)
        ·
          refine ⟨11911788832822421823770231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7941192555214947882513487 11911788832822421823770231)
          ·
            refine ⟨17867683249233632735655347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11911788832822421823770231 17867683249233632735655347)
            ·
              refine ⟨26801524873850449103483021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 17867683249233632735655347 26801524873850449103483021)
              ·
                refine ⟨10050571827693918413806133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 26801524873850449103483021 10050571827693918413806133)
                ·
                  refine ⟨942241108846304851294325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 10050571827693918413806133 942241108846304851294325)
                  ·
                    refine ⟨88335103954341079808843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 942241108846304851294325 88335103954341079808843)
                    ·
                      rfl

theorem cell22_258048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 3, 5, 5].length) (baseStart_258048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258048 prefixEnd_258048 := by exact prefixLift 258048
  have htrace : WordTrace (prefixWord ++ tailWord_258048) baseStart_258048 baseEnd_258048 := by
    simpa [prefixWord, tailWord_258048, baseEnd_258048] using wordTrace_append hprefix tailTrace_258048
  have hstable : (prefixWord ++ tailWord_258048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258048).length < 2 ^ (prefixWord ++ tailWord_258048).sum := by decide
  have hdescent : baseEnd_258048 < baseStart_258048 := by decide
  rcases family_descends (prefixWord ++ tailWord_258048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258069 : List Nat := [1, 3, 2, 1, 5, 2, 1, 2, 1, 4]
def baseStart_258069 : Nat := 118140960795 + 258069 * 2 ^ 59
def prefixEnd_258069 : Nat := 4983230072969 + 3 ^ 40 * 258069 * 2
def baseEnd_258069 : Nat := 88342292683504025033779

theorem tailTrace_258069 : CollatzResearch.WordTrace tailWord_258069 prefixEnd_258069 88342292683504025033779 := by
  unfold tailWord_258069
  simp only [CollatzResearch.WordTrace]
  refine ⟨9412549702067562521345261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6275033134711708347563507 9412549702067562521345261)
  ·
    refine ⟨3529706138275335945504473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9412549702067562521345261 3529706138275335945504473)
    ·
      refine ⟨2647279603706501959128355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3529706138275335945504473 2647279603706501959128355)
      ·
        refine ⟨3970919405559752938692533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2647279603706501959128355 3970919405559752938692533)
        ·
          refine ⟨372273694271226838002425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3970919405559752938692533 372273694271226838002425)
          ·
            refine ⟨279205270703420128501819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 372273694271226838002425 279205270703420128501819)
            ·
              refine ⟨418807906055130192752729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279205270703420128501819 418807906055130192752729)
              ·
                refine ⟨314105929541347644564547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 418807906055130192752729 314105929541347644564547)
                ·
                  refine ⟨471158894312021466846821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314105929541347644564547 471158894312021466846821)
                  ·
                    refine ⟨88342292683504025033779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 471158894312021466846821 88342292683504025033779)
                    ·
                      rfl

theorem cell22_258069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_258069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258069 prefixEnd_258069 := by exact prefixLift 258069
  have htrace : WordTrace (prefixWord ++ tailWord_258069) baseStart_258069 baseEnd_258069 := by
    simpa [prefixWord, tailWord_258069, baseEnd_258069] using wordTrace_append hprefix tailTrace_258069
  have hstable : (prefixWord ++ tailWord_258069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258069).length < 2 ^ (prefixWord ++ tailWord_258069).sum := by decide
  have hdescent : baseEnd_258069 < baseStart_258069 := by decide
  rcases family_descends (prefixWord ++ tailWord_258069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258144 : List Nat := [2, 1, 1, 3, 2, 3, 1, 5, 1, 3]
def baseStart_258144 : Nat := 118140960795 + 258144 * 2 ^ 59
def prefixEnd_258144 : Nat := 4983230072969 + 3 ^ 40 * 258144 * 2
def baseEnd_258144 : Nat := 88367966716228829408549

theorem tailTrace_258144 : CollatzResearch.WordTrace tailWord_258144 prefixEnd_258144 88367966716228829408549 := by
  unfold tailWord_258144
  simp only [CollatzResearch.WordTrace]
  refine ⟨4707642588397925165162743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6276856784530566886883657 4707642588397925165162743)
  ·
    refine ⟨7061463882596887747744115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4707642588397925165162743 7061463882596887747744115)
    ·
      refine ⟨10592195823895331621616173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7061463882596887747744115 10592195823895331621616173)
      ·
        refine ⟨3972073433960749358106065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10592195823895331621616173 3972073433960749358106065)
        ·
          refine ⟨2979055075470562018579549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3972073433960749358106065 2979055075470562018579549)
          ·
            refine ⟨1117145653301460756967331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2979055075470562018579549 1117145653301460756967331)
            ·
              refine ⟨1675718479952191135450997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1117145653301460756967331 1675718479952191135450997)
              ·
                refine ⟨157098607495517918948531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 1675718479952191135450997 157098607495517918948531)
                ·
                  refine ⟨235647911243276878422797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 157098607495517918948531 235647911243276878422797)
                  ·
                    refine ⟨88367966716228829408549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 235647911243276878422797 88367966716228829408549)
                    ·
                      rfl

theorem cell22_258144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 3, 1, 5, 1, 3].length) (baseStart_258144 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258144 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258144 prefixEnd_258144 := by exact prefixLift 258144
  have htrace : WordTrace (prefixWord ++ tailWord_258144) baseStart_258144 baseEnd_258144 := by
    simpa [prefixWord, tailWord_258144, baseEnd_258144] using wordTrace_append hprefix tailTrace_258144
  have hstable : (prefixWord ++ tailWord_258144).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258144).length < 2 ^ (prefixWord ++ tailWord_258144).sum := by decide
  have hdescent : baseEnd_258144 < baseStart_258144 := by decide
  rcases family_descends (prefixWord ++ tailWord_258144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258185 : List Nat := [1, 2, 1, 1, 4, 2, 1, 4, 6]
def baseStart_258185 : Nat := 118140960795 + 258185 * 2 ^ 59
def prefixEnd_258185 : Nat := 4983230072969 + 3 ^ 40 * 258185 * 2
def baseEnd_258185 : Nat := 29460667284706129711141

theorem tailTrace_258185 : CollatzResearch.WordTrace tailWord_258185 prefixEnd_258185 29460667284706129711141 := by
  unfold tailWord_258185
  simp only [CollatzResearch.WordTrace]
  refine ⟨9416780569647314332568009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6277853713098209555045339 9416780569647314332568009)
  ·
    refine ⟨7062585427235485749426007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9416780569647314332568009 7062585427235485749426007)
    ·
      refine ⟨10593878140853228624139011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7062585427235485749426007 10593878140853228624139011)
      ·
        refine ⟨15890817211279842936208517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10593878140853228624139011 15890817211279842936208517)
        ·
          refine ⟨2979528227114970550539097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15890817211279842936208517 2979528227114970550539097)
          ·
            refine ⟨2234646170336227912904323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2979528227114970550539097 2234646170336227912904323)
            ·
              refine ⟨3351969255504341869356485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2234646170336227912904323 3351969255504341869356485)
              ·
                refine ⟨628494235407064100504341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3351969255504341869356485 628494235407064100504341)
                ·
                  refine ⟨29460667284706129711141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 628494235407064100504341 29460667284706129711141)
                  ·
                    rfl

theorem cell22_258185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 4, 6].length) (baseStart_258185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258185 prefixEnd_258185 := by exact prefixLift 258185
  have htrace : WordTrace (prefixWord ++ tailWord_258185) baseStart_258185 baseEnd_258185 := by
    simpa [prefixWord, tailWord_258185, baseEnd_258185] using wordTrace_append hprefix tailTrace_258185
  have hstable : (prefixWord ++ tailWord_258185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258185).length < 2 ^ (prefixWord ++ tailWord_258185).sum := by decide
  have hdescent : baseEnd_258185 < baseStart_258185 := by decide
  rcases family_descends (prefixWord ++ tailWord_258185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258238 : List Nat := [4, 2, 1, 1, 5, 1, 1, 2, 1, 4]
def baseStart_258238 : Nat := 118140960795 + 258238 * 2 ^ 59
def prefixEnd_258238 : Nat := 4983230072969 + 3 ^ 40 * 258238 * 2
def baseEnd_258238 : Nat := 88400144837243917558261

theorem tailTrace_258238 : CollatzResearch.WordTrace tailWord_258238 prefixEnd_258238 88400144837243917558261 := by
  unfold tailWord_258238
  simp only [CollatzResearch.WordTrace]
  refine ⟨1177339204806913048030921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6279142425636869589498245 1177339204806913048030921)
  ·
    refine ⟨883004403605184786023191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1177339204806913048030921 883004403605184786023191)
    ·
      refine ⟨1324506605407777179034787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 883004403605184786023191 1324506605407777179034787)
      ·
        refine ⟨1986759908111665768552181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1324506605407777179034787 1986759908111665768552181)
        ·
          refine ⟨186258741385468665801767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 1986759908111665768552181 186258741385468665801767)
          ·
            refine ⟨279388112078202998702651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 186258741385468665801767 279388112078202998702651)
            ·
              refine ⟨419082168117304498053977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279388112078202998702651 419082168117304498053977)
              ·
                refine ⟨314311626087978373540483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 419082168117304498053977 314311626087978373540483)
                ·
                  refine ⟨471467439131967560310725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314311626087978373540483 471467439131967560310725)
                  ·
                    refine ⟨88400144837243917558261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 471467439131967560310725 88400144837243917558261)
                    ·
                      rfl

theorem cell22_258238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_258238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258238 prefixEnd_258238 := by exact prefixLift 258238
  have htrace : WordTrace (prefixWord ++ tailWord_258238) baseStart_258238 baseEnd_258238 := by
    simpa [prefixWord, tailWord_258238, baseEnd_258238] using wordTrace_append hprefix tailTrace_258238
  have hstable : (prefixWord ++ tailWord_258238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258238).length < 2 ^ (prefixWord ++ tailWord_258238).sum := by decide
  have hdescent : baseEnd_258238 < baseStart_258238 := by decide
  rcases family_descends (prefixWord ++ tailWord_258238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258245 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 2, 7]
def baseStart_258245 : Nat := 118140960795 + 258245 * 2 ^ 59
def prefixEnd_258245 : Nat := 4983230072969 + 3 ^ 40 * 258245 * 2
def baseEnd_258245 : Nat := 88402541080298232633239

theorem tailTrace_258245 : CollatzResearch.WordTrace tailWord_258245 prefixEnd_258245 88402541080298232633239 := by
  unfold tailWord_258245
  simp only [CollatzResearch.WordTrace]
  refine ⟨9418968949429944579752189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6279312632953296386501459 9418968949429944579752189)
  ·
    refine ⟨3532113356036229217407071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9418968949429944579752189 3532113356036229217407071)
    ·
      refine ⟨5298170034054343826110607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3532113356036229217407071 5298170034054343826110607)
      ·
        refine ⟨7947255051081515739165911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5298170034054343826110607 7947255051081515739165911)
        ·
          refine ⟨11920882576622273608748867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7947255051081515739165911 11920882576622273608748867)
          ·
            refine ⟨17881323864933410413123301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11920882576622273608748867 17881323864933410413123301)
            ·
              refine ⟨3352748224675014452460619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 17881323864933410413123301 3352748224675014452460619)
              ·
                refine ⟨5029122337012521678690929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3352748224675014452460619 5029122337012521678690929)
                ·
                  refine ⟨3771841752759391259018197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5029122337012521678690929 3771841752759391259018197)
                  ·
                    refine ⟨88402541080298232633239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3771841752759391259018197 88402541080298232633239)
                    ·
                      rfl

theorem cell22_258245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 2, 7].length) (baseStart_258245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258245 prefixEnd_258245 := by exact prefixLift 258245
  have htrace : WordTrace (prefixWord ++ tailWord_258245) baseStart_258245 baseEnd_258245 := by
    simpa [prefixWord, tailWord_258245, baseEnd_258245] using wordTrace_append hprefix tailTrace_258245
  have hstable : (prefixWord ++ tailWord_258245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258245).length < 2 ^ (prefixWord ++ tailWord_258245).sum := by decide
  have hdescent : baseEnd_258245 < baseStart_258245 := by decide
  rcases family_descends (prefixWord ++ tailWord_258245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258277 : List Nat := [1, 3, 1, 4, 2, 1, 1, 1, 2, 6]
def baseStart_258277 : Nat := 118140960795 + 258277 * 2 ^ 59
def prefixEnd_258277 : Nat := 4983230072969 + 3 ^ 40 * 258277 * 2
def baseEnd_258277 : Nat := 88413495334260815833141

theorem tailTrace_258277 : CollatzResearch.WordTrace tailWord_258277 prefixEnd_258277 88413495334260815833141 := by
  unfold tailWord_258277
  simp only [CollatzResearch.WordTrace]
  refine ⟨9420136085314014044917085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6280090723542676029944723 9420136085314014044917085)
  ·
    refine ⟨3532551031992755266843907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9420136085314014044917085 3532551031992755266843907)
    ·
      refine ⟨5298826547989132900265861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3532551031992755266843907 5298826547989132900265861)
      ·
        refine ⟨993529977747962418799849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 5298826547989132900265861 993529977747962418799849)
        ·
          refine ⟨745147483310971814099887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 993529977747962418799849 745147483310971814099887)
          ·
            refine ⟨1117721224966457721149831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 745147483310971814099887 1117721224966457721149831)
            ·
              refine ⟨1676581837449686581724747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1117721224966457721149831 1676581837449686581724747)
              ·
                refine ⟨2514872756174529872587121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1676581837449686581724747 2514872756174529872587121)
                ·
                  refine ⟨1886154567130897404440341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2514872756174529872587121 1886154567130897404440341)
                  ·
                    refine ⟨88413495334260815833141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1886154567130897404440341 88413495334260815833141)
                    ·
                      rfl

theorem cell22_258277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 6].length) (baseStart_258277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258277 prefixEnd_258277 := by exact prefixLift 258277
  have htrace : WordTrace (prefixWord ++ tailWord_258277) baseStart_258277 baseEnd_258277 := by
    simpa [prefixWord, tailWord_258277, baseEnd_258277] using wordTrace_append hprefix tailTrace_258277
  have hstable : (prefixWord ++ tailWord_258277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258277).length < 2 ^ (prefixWord ++ tailWord_258277).sum := by decide
  have hdescent : baseEnd_258277 < baseStart_258277 := by decide
  rcases family_descends (prefixWord ++ tailWord_258277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258337 : List Nat := [1, 2, 3, 2, 1, 1, 3, 3, 6]
def baseStart_258337 : Nat := 118140960795 + 258337 * 2 ^ 59
def prefixEnd_258337 : Nat := 4983230072969 + 3 ^ 40 * 258337 * 2
def baseEnd_258337 : Nat := 29478011520146886444319

theorem tailTrace_258337 : CollatzResearch.WordTrace tailWord_258337 prefixEnd_258337 29478011520146886444319 := by
  unfold tailWord_258337
  simp only [CollatzResearch.WordTrace]
  refine ⟨9422324465096644292101265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6281549643397762861400843 9422324465096644292101265)
  ·
    refine ⟨7066743348822483219075949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9422324465096644292101265 7066743348822483219075949)
    ·
      refine ⟨2650028755808431207153481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7066743348822483219075949 2650028755808431207153481)
      ·
        refine ⟨1987521566856323405365111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2650028755808431207153481 1987521566856323405365111)
        ·
          refine ⟨2981282350284485108047667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1987521566856323405365111 2981282350284485108047667)
          ·
            refine ⟨4471923525426727662071501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2981282350284485108047667 4471923525426727662071501)
            ·
              refine ⟨1676971322035022873276813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4471923525426727662071501 1676971322035022873276813)
              ·
                refine ⟨628864245763133577478805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1676971322035022873276813 628864245763133577478805)
                ·
                  refine ⟨29478011520146886444319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 628864245763133577478805 29478011520146886444319)
                  ·
                    rfl

theorem cell22_258337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 3, 6].length) (baseStart_258337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258337 prefixEnd_258337 := by exact prefixLift 258337
  have htrace : WordTrace (prefixWord ++ tailWord_258337) baseStart_258337 baseEnd_258337 := by
    simpa [prefixWord, tailWord_258337, baseEnd_258337] using wordTrace_append hprefix tailTrace_258337
  have hstable : (prefixWord ++ tailWord_258337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258337).length < 2 ^ (prefixWord ++ tailWord_258337).sum := by decide
  have hdescent : baseEnd_258337 < baseStart_258337 := by decide
  rcases family_descends (prefixWord ++ tailWord_258337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258352 : List Nat := [2, 1, 1, 1, 2, 2, 2, 5, 1, 5]
def baseStart_258352 : Nat := 118140960795 + 258352 * 2 ^ 59
def prefixEnd_258352 : Nat := 4983230072969 + 3 ^ 40 * 258352 * 2
def baseEnd_258352 : Nat := 88439169366985620207911

theorem tailTrace_258352 : CollatzResearch.WordTrace tailWord_258352 prefixEnd_258352 88439169366985620207911 := by
  unfold tailWord_258352
  simp only [CollatzResearch.WordTrace]
  refine ⟨4711435780021150926948655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6281914373361534569264873 4711435780021150926948655)
  ·
    refine ⟨7067153670031726390422983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4711435780021150926948655 7067153670031726390422983)
    ·
      refine ⟨10600730505047589585634475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7067153670031726390422983 10600730505047589585634475)
      ·
        refine ⟨15901095757571384378451713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10600730505047589585634475 15901095757571384378451713)
        ·
          refine ⟨11925821818178538283838785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15901095757571384378451713 11925821818178538283838785)
          ·
            refine ⟨8944366363633903712879089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11925821818178538283838785 8944366363633903712879089)
            ·
              refine ⟨6708274772725427784659317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 8944366363633903712879089 6708274772725427784659317)
              ·
                refine ⟨628900759943008854811811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 6708274772725427784659317 628900759943008854811811)
                ·
                  refine ⟨943351139914513282217717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 628900759943008854811811 943351139914513282217717)
                  ·
                    refine ⟨88439169366985620207911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 943351139914513282217717 88439169366985620207911)
                    ·
                      rfl

theorem cell22_258352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 5, 1, 5].length) (baseStart_258352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258352 prefixEnd_258352 := by exact prefixLift 258352
  have htrace : WordTrace (prefixWord ++ tailWord_258352) baseStart_258352 baseEnd_258352 := by
    simpa [prefixWord, tailWord_258352, baseEnd_258352] using wordTrace_append hprefix tailTrace_258352
  have hstable : (prefixWord ++ tailWord_258352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258352).length < 2 ^ (prefixWord ++ tailWord_258352).sum := by decide
  have hdescent : baseEnd_258352 < baseStart_258352 := by decide
  rcases family_descends (prefixWord ++ tailWord_258352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258356 : List Nat := [2, 5, 1, 1, 1, 2, 1, 4, 1, 4]
def baseStart_258356 : Nat := 118140960795 + 258356 * 2 ^ 59
def prefixEnd_258356 : Nat := 4983230072969 + 3 ^ 40 * 258356 * 2
def baseEnd_258356 : Nat := 88440538648730943107899

theorem tailTrace_258356 : CollatzResearch.WordTrace tailWord_258356 prefixEnd_258356 88440538648730943107899 := by
  unfold tailWord_258356
  simp only [CollatzResearch.WordTrace]
  refine ⟨4711508726013905268521461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6282011634685207024695281 4711508726013905268521461)
  ·
    refine ⟨441703943063803618923887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4711508726013905268521461 441703943063803618923887)
    ·
      refine ⟨662555914595705428385831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 441703943063803618923887 662555914595705428385831)
      ·
        refine ⟨993833871893558142578747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 662555914595705428385831 993833871893558142578747)
        ·
          refine ⟨1490750807840337213868121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 993833871893558142578747 1490750807840337213868121)
          ·
            refine ⟨1118063105880252910401091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1490750807840337213868121 1118063105880252910401091)
            ·
              refine ⟨1677094658820379365601637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1118063105880252910401091 1677094658820379365601637)
              ·
                refine ⟨314455248528821131050307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1677094658820379365601637 314455248528821131050307)
                ·
                  refine ⟨471682872793231696575461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 314455248528821131050307 471682872793231696575461)
                  ·
                    refine ⟨88440538648730943107899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 471682872793231696575461 88440538648730943107899)
                    ·
                      rfl

theorem cell22_258356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_258356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258356 prefixEnd_258356 := by exact prefixLift 258356
  have htrace : WordTrace (prefixWord ++ tailWord_258356) baseStart_258356 baseEnd_258356 := by
    simpa [prefixWord, tailWord_258356, baseEnd_258356] using wordTrace_append hprefix tailTrace_258356
  have hstable : (prefixWord ++ tailWord_258356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258356).length < 2 ^ (prefixWord ++ tailWord_258356).sum := by decide
  have hdescent : baseEnd_258356 < baseStart_258356 := by decide
  rcases family_descends (prefixWord ++ tailWord_258356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258367 : List Nat := [1, 1, 2, 2, 4, 1, 1, 3, 1, 6]
def baseStart_258367 : Nat := 118140960795 + 258367 * 2 ^ 59
def prefixEnd_258367 : Nat := 4983230072969 + 3 ^ 40 * 258367 * 2
def baseEnd_258367 : Nat := 88444304173530581082865

theorem tailTrace_258367 : CollatzResearch.WordTrace tailWord_258367 prefixEnd_258367 88444304173530581082865 := by
  unfold tailWord_258367
  simp only [CollatzResearch.WordTrace]
  refine ⟨9423418654987959415693355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6282279103325306277128903 9423418654987959415693355)
  ·
    refine ⟨14135127982481939123540033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9423418654987959415693355 14135127982481939123540033)
    ·
      refine ⟨10601345986861454342655025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14135127982481939123540033 10601345986861454342655025)
      ·
        refine ⟨7951009490146090756991269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10601345986861454342655025 7951009490146090756991269)
        ·
          refine ⟨1490814279402392016935863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7951009490146090756991269 1490814279402392016935863)
          ·
            refine ⟨2236221419103588025403795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1490814279402392016935863 2236221419103588025403795)
            ·
              refine ⟨3354332128655382038105693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2236221419103588025403795 3354332128655382038105693)
              ·
                refine ⟨1257874548245768264289635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3354332128655382038105693 1257874548245768264289635)
                ·
                  refine ⟨1886811822368652396434453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1257874548245768264289635 1886811822368652396434453)
                  ·
                    refine ⟨88444304173530581082865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1886811822368652396434453 88444304173530581082865)
                    ·
                      rfl

theorem cell22_258367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 6].length) (baseStart_258367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258367 prefixEnd_258367 := by exact prefixLift 258367
  have htrace : WordTrace (prefixWord ++ tailWord_258367) baseStart_258367 baseEnd_258367 := by
    simpa [prefixWord, tailWord_258367, baseEnd_258367] using wordTrace_append hprefix tailTrace_258367
  have hstable : (prefixWord ++ tailWord_258367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258367).length < 2 ^ (prefixWord ++ tailWord_258367).sum := by decide
  have hdescent : baseEnd_258367 < baseStart_258367 := by decide
  rcases family_descends (prefixWord ++ tailWord_258367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258384 : List Nat := [2, 1, 1, 1, 1, 7, 1, 2, 2, 4]
def baseStart_258384 : Nat := 118140960795 + 258384 * 2 ^ 59
def prefixEnd_258384 : Nat := 4983230072969 + 3 ^ 40 * 258384 * 2
def baseEnd_258384 : Nat := 88450123620948203407813

theorem tailTrace_258384 : CollatzResearch.WordTrace tailWord_258384 prefixEnd_258384 88450123620948203407813 := by
  unfold tailWord_258384
  simp only [CollatzResearch.WordTrace]
  refine ⟨4712019347963185659531103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6282692463950914212708137 4712019347963185659531103)
  ·
    refine ⟨7068029021944778489296655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4712019347963185659531103 7068029021944778489296655)
    ·
      refine ⟨10602043532917167733944983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7068029021944778489296655 10602043532917167733944983)
      ·
        refine ⟨15903065299375751600917475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10602043532917167733944983 15903065299375751600917475)
        ·
          refine ⟨23854597949063627401376213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15903065299375751600917475 23854597949063627401376213)
          ·
            refine ⟨559092139431178767219755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 23854597949063627401376213 559092139431178767219755)
            ·
              refine ⟨838638209146768150829633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559092139431178767219755 838638209146768150829633)
              ·
                refine ⟨628978656860076113122225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 838638209146768150829633 628978656860076113122225)
                ·
                  refine ⟨471733992645057084841669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 628978656860076113122225 471733992645057084841669)
                  ·
                    refine ⟨88450123620948203407813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 471733992645057084841669 88450123620948203407813)
                    ·
                      rfl

theorem cell22_258384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 1, 2, 2, 4].length) (baseStart_258384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258384 prefixEnd_258384 := by exact prefixLift 258384
  have htrace : WordTrace (prefixWord ++ tailWord_258384) baseStart_258384 baseEnd_258384 := by
    simpa [prefixWord, tailWord_258384, baseEnd_258384] using wordTrace_append hprefix tailTrace_258384
  have hstable : (prefixWord ++ tailWord_258384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258384).length < 2 ^ (prefixWord ++ tailWord_258384).sum := by decide
  have hdescent : baseEnd_258384 < baseStart_258384 := by decide
  rcases family_descends (prefixWord ++ tailWord_258384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258388 : List Nat := [2, 4, 1, 1, 2, 3, 3, 2, 4]
def baseStart_258388 : Nat := 118140960795 + 258388 * 2 ^ 59
def prefixEnd_258388 : Nat := 4983230072969 + 3 ^ 40 * 258388 * 2
def baseEnd_258388 : Nat := 29483830967564508769267

theorem tailTrace_258388 : CollatzResearch.WordTrace tailWord_258388 prefixEnd_258388 29483830967564508769267 := by
  unfold tailWord_258388
  simp only [CollatzResearch.WordTrace]
  refine ⟨4712092293955940001103909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6282789725274586668138545 4712092293955940001103909)
  ·
    refine ⟨883517305116738750206983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4712092293955940001103909 883517305116738750206983)
    ·
      refine ⟨1325275957675108125310475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 883517305116738750206983 1325275957675108125310475)
      ·
        refine ⟨1987913936512662187965713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1325275957675108125310475 1987913936512662187965713)
        ·
          refine ⟨1490935452384496640974285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1987913936512662187965713 1490935452384496640974285)
          ·
            refine ⟨559100794644186240365357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1490935452384496640974285 559100794644186240365357)
            ·
              refine ⟨209662797991569840137009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 559100794644186240365357 209662797991569840137009)
              ·
                refine ⟨157247098493677380102757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 209662797991569840137009 157247098493677380102757)
                ·
                  refine ⟨29483830967564508769267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157247098493677380102757 29483830967564508769267)
                  ·
                    rfl

theorem cell22_258388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 3, 3, 2, 4].length) (baseStart_258388 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258388 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258388 prefixEnd_258388 := by exact prefixLift 258388
  have htrace : WordTrace (prefixWord ++ tailWord_258388) baseStart_258388 baseEnd_258388 := by
    simpa [prefixWord, tailWord_258388, baseEnd_258388] using wordTrace_append hprefix tailTrace_258388
  have hstable : (prefixWord ++ tailWord_258388).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258388).length < 2 ^ (prefixWord ++ tailWord_258388).sum := by decide
  have hdescent : baseEnd_258388 < baseStart_258388 := by decide
  rcases family_descends (prefixWord ++ tailWord_258388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258444 : List Nat := [2, 2, 1, 2, 1, 4, 1, 4, 5]
def baseStart_258444 : Nat := 118140960795 + 258444 * 2 ^ 59
def prefixEnd_258444 : Nat := 4983230072969 + 3 ^ 40 * 258444 * 2
def baseEnd_258444 : Nat := 29490220949042682302543

theorem tailTrace_258444 : CollatzResearch.WordTrace tailWord_258444 prefixEnd_258444 29490220949042682302543 := by
  unfold tailWord_258444
  simp only [CollatzResearch.WordTrace]
  refine ⟨4713113537854500783123193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6284151383806001044164257 4713113537854500783123193)
  ·
    refine ⟨3534835153390875587342395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4713113537854500783123193 3534835153390875587342395)
    ·
      refine ⟨5302252730086313381013593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3534835153390875587342395 5302252730086313381013593)
      ·
        refine ⟨3976689547564735035760195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5302252730086313381013593 3976689547564735035760195)
        ·
          refine ⟨5965034321347102553640293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3976689547564735035760195 5965034321347102553640293)
          ·
            refine ⟨1118443935252581728807555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 5965034321347102553640293 1118443935252581728807555)
            ·
              refine ⟨1677665902878872593211333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1118443935252581728807555 1677665902878872593211333)
              ·
                refine ⟨314562356789788611227125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1677665902878872593211333 314562356789788611227125)
                ·
                  refine ⟨29490220949042682302543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 314562356789788611227125 29490220949042682302543)
                  ·
                    rfl

theorem cell22_258444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 4, 5].length) (baseStart_258444 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258444 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258444 prefixEnd_258444 := by exact prefixLift 258444
  have htrace : WordTrace (prefixWord ++ tailWord_258444) baseStart_258444 baseEnd_258444 := by
    simpa [prefixWord, tailWord_258444, baseEnd_258444] using wordTrace_append hprefix tailTrace_258444
  have hstable : (prefixWord ++ tailWord_258444).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258444).length < 2 ^ (prefixWord ++ tailWord_258444).sum := by decide
  have hdescent : baseEnd_258444 < baseStart_258444 := by decide
  rcases family_descends (prefixWord ++ tailWord_258444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258506 : List Nat := [3, 1, 2, 1, 2, 2, 1, 6, 4]
def baseStart_258506 : Nat := 118140960795 + 258506 * 2 ^ 59
def prefixEnd_258506 : Nat := 4983230072969 + 3 ^ 40 * 258506 * 2
def baseEnd_258506 : Nat := 29497295571393517285813

theorem tailTrace_258506 : CollatzResearch.WordTrace tailWord_258506 prefixEnd_258506 29497295571393517285813 := by
  unfold tailWord_258506
  simp only [CollatzResearch.WordTrace]
  refine ⟨2357122100371096538750843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6285658934322924103335581 2357122100371096538750843)
  ·
    refine ⟨3535683150556644808126265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2357122100371096538750843 3535683150556644808126265)
    ·
      refine ⟨2651762362917483606094699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3535683150556644808126265 2651762362917483606094699)
      ·
        refine ⟨3977643544376225409142049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2651762362917483606094699 3977643544376225409142049)
        ·
          refine ⟨2983232658282169056856537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3977643544376225409142049 2983232658282169056856537)
          ·
            refine ⟨2237424493711626792642403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2983232658282169056856537 2237424493711626792642403)
            ·
              refine ⟨3356136740567440188963605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2237424493711626792642403 3356136740567440188963605)
              ·
                refine ⟨157318909714098758857669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 3356136740567440188963605 157318909714098758857669)
                ·
                  refine ⟨29497295571393517285813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157318909714098758857669 29497295571393517285813)
                  ·
                    rfl

theorem cell22_258506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 1, 6, 4].length) (baseStart_258506 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258506 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258506 prefixEnd_258506 := by exact prefixLift 258506
  have htrace : WordTrace (prefixWord ++ tailWord_258506) baseStart_258506 baseEnd_258506 := by
    simpa [prefixWord, tailWord_258506, baseEnd_258506] using wordTrace_append hprefix tailTrace_258506
  have hstable : (prefixWord ++ tailWord_258506).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258506).length < 2 ^ (prefixWord ++ tailWord_258506).sum := by decide
  have hdescent : baseEnd_258506 < baseStart_258506 := by decide
  rcases family_descends (prefixWord ++ tailWord_258506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258630 : List Nat := [6, 1, 1, 1, 2, 1, 2, 3, 5]
def baseStart_258630 : Nat := 118140960795 + 258630 * 2 ^ 59
def prefixEnd_258630 : Nat := 4983230072969 + 3 ^ 40 * 258630 * 2
def baseEnd_258630 : Nat := 29511444816095187252353

theorem tailTrace_258630 : CollatzResearch.WordTrace tailWord_258630 prefixEnd_258630 29511444816095187252353 := by
  unfold tailWord_258630
  simp only [CollatzResearch.WordTrace]
  refine ⟨294781595407348604141167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 6288674035356770221678229 294781595407348604141167)
  ·
    refine ⟨442172393111022906211751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 294781595407348604141167 442172393111022906211751)
    ·
      refine ⟨663258589666534359317627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 442172393111022906211751 663258589666534359317627)
      ·
        refine ⟨994887884499801538976441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 663258589666534359317627 994887884499801538976441)
        ·
          refine ⟨746165913374851154232331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 994887884499801538976441 746165913374851154232331)
          ·
            refine ⟨1119248870062276731348497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 746165913374851154232331 1119248870062276731348497)
            ·
              refine ⟨839436652546707548511373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1119248870062276731348497 839436652546707548511373)
              ·
                refine ⟨314788744705015330691765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 839436652546707548511373 314788744705015330691765)
                ·
                  refine ⟨29511444816095187252353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 314788744705015330691765 29511444816095187252353)
                  ·
                    rfl

theorem cell22_258630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_258630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258630 prefixEnd_258630 := by exact prefixLift 258630
  have htrace : WordTrace (prefixWord ++ tailWord_258630) baseStart_258630 baseEnd_258630 := by
    simpa [prefixWord, tailWord_258630, baseEnd_258630] using wordTrace_append hprefix tailTrace_258630
  have hstable : (prefixWord ++ tailWord_258630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258630).length < 2 ^ (prefixWord ++ tailWord_258630).sum := by decide
  have hdescent : baseEnd_258630 < baseStart_258630 := by decide
  rcases family_descends (prefixWord ++ tailWord_258630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258641 : List Nat := [1, 2, 2, 1, 3, 4, 1, 2, 6]
def baseStart_258641 : Nat := 118140960795 + 258641 * 2 ^ 59
def prefixEnd_258641 : Nat := 4983230072969 + 3 ^ 40 * 258641 * 2
def baseEnd_258641 : Nat := 29512699991028399910675

theorem tailTrace_258641 : CollatzResearch.WordTrace tailWord_258641 prefixEnd_258641 29512699991028399910675 := by
  unfold tailWord_258641
  simp only [CollatzResearch.WordTrace]
  refine ⟨9433412255995304211167777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6288941503996869474111851 9433412255995304211167777)
  ·
    refine ⟨7075059191996478158375833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9433412255995304211167777 7075059191996478158375833)
    ·
      refine ⟨5306294393997358618781875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7075059191996478158375833 5306294393997358618781875)
      ·
        refine ⟨7959441590996037928172813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5306294393997358618781875 7959441590996037928172813)
        ·
          refine ⟨2984790596623514223064805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7959441590996037928172813 2984790596623514223064805)
          ·
            refine ⟨559648236866908916824651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2984790596623514223064805 559648236866908916824651)
            ·
              refine ⟨839472355300363375236977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 559648236866908916824651 839472355300363375236977)
              ·
                refine ⟨629604266475272531427733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 839472355300363375236977 629604266475272531427733)
                ·
                  refine ⟨29512699991028399910675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 629604266475272531427733 29512699991028399910675)
                  ·
                    rfl

theorem cell22_258641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 6].length) (baseStart_258641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258641 prefixEnd_258641 := by exact prefixLift 258641
  have htrace : WordTrace (prefixWord ++ tailWord_258641) baseStart_258641 baseEnd_258641 := by
    simpa [prefixWord, tailWord_258641, baseEnd_258641] using wordTrace_append hprefix tailTrace_258641
  have hstable : (prefixWord ++ tailWord_258641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258641).length < 2 ^ (prefixWord ++ tailWord_258641).sum := by decide
  have hdescent : baseEnd_258641 < baseStart_258641 := by decide
  rcases family_descends (prefixWord ++ tailWord_258641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258656 : List Nat := [2, 1, 1, 3, 2, 1, 4, 2, 1, 5]
def baseStart_258656 : Nat := 118140960795 + 258656 * 2 ^ 59
def prefixEnd_258656 : Nat := 4983230072969 + 3 ^ 40 * 258656 * 2
def baseEnd_258656 : Nat := 88543234779630160606979

theorem tailTrace_258656 : CollatzResearch.WordTrace tailWord_258656 prefixEnd_258656 88543234779630160606979 := by
  unfold tailWord_258656
  simp only [CollatzResearch.WordTrace]
  refine ⟨4716979675470480886481911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6289306233960641181975881 4716979675470480886481911)
  ·
    refine ⟨7075469513205721329722867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4716979675470480886481911 7075469513205721329722867)
    ·
      refine ⟨10613204269808581994584301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7075469513205721329722867 10613204269808581994584301)
      ·
        refine ⟨3979951601178218247969113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10613204269808581994584301 3979951601178218247969113)
        ·
          refine ⟨2984963700883663685976835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3979951601178218247969113 2984963700883663685976835)
          ·
            refine ⟨4477445551325495528965253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2984963700883663685976835 4477445551325495528965253)
            ·
              refine ⟨839521040873530411680985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 4477445551325495528965253 839521040873530411680985)
              ·
                refine ⟨629640780655147808760739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 839521040873530411680985 629640780655147808760739)
                ·
                  refine ⟨944461170982721713141109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 629640780655147808760739 944461170982721713141109)
                  ·
                    refine ⟨88543234779630160606979, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 944461170982721713141109 88543234779630160606979)
                    ·
                      rfl

theorem cell22_258656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 4, 2, 1, 5].length) (baseStart_258656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258656 prefixEnd_258656 := by exact prefixLift 258656
  have htrace : WordTrace (prefixWord ++ tailWord_258656) baseStart_258656 baseEnd_258656 := by
    simpa [prefixWord, tailWord_258656, baseEnd_258656] using wordTrace_append hprefix tailTrace_258656
  have hstable : (prefixWord ++ tailWord_258656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258656).length < 2 ^ (prefixWord ++ tailWord_258656).sum := by decide
  have hdescent : baseEnd_258656 < baseStart_258656 := by decide
  rcases family_descends (prefixWord ++ tailWord_258656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258671 : List Nat := [1, 1, 2, 1, 3, 2, 2, 4, 2, 4]
def baseStart_258671 : Nat := 118140960795 + 258671 * 2 ^ 59
def prefixEnd_258671 : Nat := 4983230072969 + 3 ^ 40 * 258671 * 2
def baseEnd_258671 : Nat := 88548369586175121481933

theorem tailTrace_258671 : CollatzResearch.WordTrace tailWord_258671 prefixEnd_258671 88548369586175121481933 := by
  unfold tailWord_258671
  simp only [CollatzResearch.WordTrace]
  refine ⟨9434506445886619334759867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6289670963924412889839911 9434506445886619334759867)
  ·
    refine ⟨14151759668829929002139801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9434506445886619334759867 14151759668829929002139801)
    ·
      refine ⟨10613819751622446751604851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14151759668829929002139801 10613819751622446751604851)
      ·
        refine ⟨15920729627433670127407277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10613819751622446751604851 15920729627433670127407277)
        ·
          refine ⟨5970273610287626297777729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15920729627433670127407277 5970273610287626297777729)
          ·
            refine ⟨4477705207715719723333297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 5970273610287626297777729 4477705207715719723333297)
            ·
              refine ⟨3358278905786789792499973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4477705207715719723333297 3358278905786789792499973)
              ·
                refine ⟨629677294835023086093745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3358278905786789792499973 629677294835023086093745)
                ·
                  refine ⟨472257971126267314570309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 629677294835023086093745 472257971126267314570309)
                  ·
                    refine ⟨88548369586175121481933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 472257971126267314570309 88548369586175121481933)
                    ·
                      rfl

theorem cell22_258671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 2, 4, 2, 4].length) (baseStart_258671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258671 prefixEnd_258671 := by exact prefixLift 258671
  have htrace : WordTrace (prefixWord ++ tailWord_258671) baseStart_258671 baseEnd_258671 := by
    simpa [prefixWord, tailWord_258671, baseEnd_258671] using wordTrace_append hprefix tailTrace_258671
  have hstable : (prefixWord ++ tailWord_258671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258671).length < 2 ^ (prefixWord ++ tailWord_258671).sum := by decide
  have hdescent : baseEnd_258671 < baseStart_258671 := by decide
  rcases family_descends (prefixWord ++ tailWord_258671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258735 : List Nat := [1, 1, 2, 1, 2, 7, 1, 1, 3, 3]
def baseStart_258735 : Nat := 118140960795 + 258735 * 2 ^ 59
def prefixEnd_258735 : Nat := 4983230072969 + 3 ^ 40 * 258735 * 2
def baseEnd_258735 : Nat := 88570278094100287881737

theorem tailTrace_258735 : CollatzResearch.WordTrace tailWord_258735 prefixEnd_258735 88570278094100287881737 := by
  unfold tailWord_258735
  simp only [CollatzResearch.WordTrace]
  refine ⟨9436840717654758265089659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6291227145103172176726439 9436840717654758265089659)
  ·
    refine ⟨14155261076482137397634489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9436840717654758265089659 14155261076482137397634489)
    ·
      refine ⟨10616445807361603048225867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14155261076482137397634489 10616445807361603048225867)
      ·
        refine ⟨15924668711042404572338801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10616445807361603048225867 15924668711042404572338801)
        ·
          refine ⟨11943501533281803429254101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15924668711042404572338801 11943501533281803429254101)
          ·
            refine ⟨279925817186292267873143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 11943501533281803429254101 279925817186292267873143)
            ·
              refine ⟨419888725779438401809715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 279925817186292267873143 419888725779438401809715)
              ·
                refine ⟨629833088669157602714573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 419888725779438401809715 629833088669157602714573)
                ·
                  refine ⟨236187408250934101017965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 629833088669157602714573 236187408250934101017965)
                  ·
                    refine ⟨88570278094100287881737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 236187408250934101017965 88570278094100287881737)
                    ·
                      rfl

theorem cell22_258735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 7, 1, 1, 3, 3].length) (baseStart_258735 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258735 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258735 prefixEnd_258735 := by exact prefixLift 258735
  have htrace : WordTrace (prefixWord ++ tailWord_258735) baseStart_258735 baseEnd_258735 := by
    simpa [prefixWord, tailWord_258735, baseEnd_258735] using wordTrace_append hprefix tailTrace_258735
  have hstable : (prefixWord ++ tailWord_258735).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258735).length < 2 ^ (prefixWord ++ tailWord_258735).sum := by decide
  have hdescent : baseEnd_258735 < baseStart_258735 := by decide
  rcases family_descends (prefixWord ++ tailWord_258735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258746 : List Nat := [3, 1, 1, 1, 2, 3, 2, 1, 1, 7]
def baseStart_258746 : Nat := 118140960795 + 258746 * 2 ^ 59
def prefixEnd_258746 : Nat := 4983230072969 + 3 ^ 40 * 258746 * 2
def baseEnd_258746 : Nat := 88574043618899925856703

theorem tailTrace_258746 : CollatzResearch.WordTrace tailWord_258746 prefixEnd_258746 88574043618899925856703 := by
  unfold tailWord_258746
  simp only [CollatzResearch.WordTrace]
  refine ⟨2359310480153726785935023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6291494613743271429160061 2359310480153726785935023)
  ·
    refine ⟨3538965720230590178902535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2359310480153726785935023 3538965720230590178902535)
    ·
      refine ⟨5308448580345885268353803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3538965720230590178902535 5308448580345885268353803)
      ·
        refine ⟨7962672870518827902530705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5308448580345885268353803 7962672870518827902530705)
        ·
          refine ⟨5972004652889120926898029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7962672870518827902530705 5972004652889120926898029)
          ·
            refine ⟨2239501744833420347586761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5972004652889120926898029 2239501744833420347586761)
            ·
              refine ⟨1679626308625065260690071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2239501744833420347586761 1679626308625065260690071)
              ·
                refine ⟨2519439462937597891035107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1679626308625065260690071 2519439462937597891035107)
                ·
                  refine ⟨3779159194406396836552661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2519439462937597891035107 3779159194406396836552661)
                  ·
                    refine ⟨88574043618899925856703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3779159194406396836552661 88574043618899925856703)
                    ·
                      rfl

theorem cell22_258746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 2, 1, 1, 7].length) (baseStart_258746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258746 prefixEnd_258746 := by exact prefixLift 258746
  have htrace : WordTrace (prefixWord ++ tailWord_258746) baseStart_258746 baseEnd_258746 := by
    simpa [prefixWord, tailWord_258746, baseEnd_258746] using wordTrace_append hprefix tailTrace_258746
  have hstable : (prefixWord ++ tailWord_258746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258746).length < 2 ^ (prefixWord ++ tailWord_258746).sum := by decide
  have hdescent : baseEnd_258746 < baseStart_258746 := by decide
  rcases family_descends (prefixWord ++ tailWord_258746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258748 : List Nat := [2, 2, 2, 3, 1, 1, 3, 3, 5]
def baseStart_258748 : Nat := 118140960795 + 258748 * 2 ^ 59
def prefixEnd_258748 : Nat := 4983230072969 + 3 ^ 40 * 258748 * 2
def baseEnd_258748 : Nat := 29524909419924195768899

theorem tailTrace_258748 : CollatzResearch.WordTrace tailWord_258748 prefixEnd_258748 29524909419924195768899 := by
  unfold tailWord_258748
  simp only [CollatzResearch.WordTrace]
  refine ⟨4718657433303830742656449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6291543244405107656875265 4718657433303830742656449)
  ·
    refine ⟨3538993074977873056992337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4718657433303830742656449 3538993074977873056992337)
    ·
      refine ⟨2654244806233404792744253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3538993074977873056992337 2654244806233404792744253)
      ·
        refine ⟨995341802337526797279095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2654244806233404792744253 995341802337526797279095)
        ·
          refine ⟨1493012703506290195918643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 995341802337526797279095 1493012703506290195918643)
          ·
            refine ⟨2239519055259435293877965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1493012703506290195918643 2239519055259435293877965)
            ·
              refine ⟨839819645722288235204237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2239519055259435293877965 839819645722288235204237)
              ·
                refine ⟨314932367145858088201589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 839819645722288235204237 314932367145858088201589)
                ·
                  refine ⟨29524909419924195768899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 314932367145858088201589 29524909419924195768899)
                  ·
                    rfl

theorem cell22_258748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 5].length) (baseStart_258748 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258748 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258748 prefixEnd_258748 := by exact prefixLift 258748
  have htrace : WordTrace (prefixWord ++ tailWord_258748) baseStart_258748 baseEnd_258748 := by
    simpa [prefixWord, tailWord_258748, baseEnd_258748] using wordTrace_append hprefix tailTrace_258748
  have hstable : (prefixWord ++ tailWord_258748).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258748).length < 2 ^ (prefixWord ++ tailWord_258748).sum := by decide
  have hdescent : baseEnd_258748 < baseStart_258748 := by decide
  rcases family_descends (prefixWord ++ tailWord_258748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258808 : List Nat := [2, 1, 2, 1, 1, 2, 6, 1, 1, 5]
def baseStart_258808 : Nat := 118140960795 + 258808 * 2 ^ 59
def prefixEnd_258808 : Nat := 4983230072969 + 3 ^ 40 * 258808 * 2
def baseEnd_258808 : Nat := 88595267485952430806513

theorem tailTrace_258808 : CollatzResearch.WordTrace tailWord_258808 prefixEnd_258808 88595267485952430806513 := by
  unfold tailWord_258808
  simp only [CollatzResearch.WordTrace]
  refine ⟨4719751623195145866248539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6293002164260194488331385 4719751623195145866248539)
  ·
    refine ⟨7079627434792718799372809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4719751623195145866248539 7079627434792718799372809)
    ·
      refine ⟨5309720576094539099529607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7079627434792718799372809 5309720576094539099529607)
      ·
        refine ⟨7964580864141808649294411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5309720576094539099529607 7964580864141808649294411)
        ·
          refine ⟨11946871296212712973941617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7964580864141808649294411 11946871296212712973941617)
          ·
            refine ⟨8960153472159534730456213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 11946871296212712973941617 8960153472159534730456213)
            ·
              refine ⟨420007194007478190490135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 8960153472159534730456213 420007194007478190490135)
              ·
                refine ⟨630010791011217285735203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420007194007478190490135 630010791011217285735203)
                ·
                  refine ⟨945016186516825928602805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 630010791011217285735203 945016186516825928602805)
                  ·
                    refine ⟨88595267485952430806513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 945016186516825928602805 88595267485952430806513)
                    ·
                      rfl

theorem cell22_258808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 2, 6, 1, 1, 5].length) (baseStart_258808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258808 prefixEnd_258808 := by exact prefixLift 258808
  have htrace : WordTrace (prefixWord ++ tailWord_258808) baseStart_258808 baseEnd_258808 := by
    simpa [prefixWord, tailWord_258808, baseEnd_258808] using wordTrace_append hprefix tailTrace_258808
  have hstable : (prefixWord ++ tailWord_258808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258808).length < 2 ^ (prefixWord ++ tailWord_258808).sum := by decide
  have hdescent : baseEnd_258808 < baseStart_258808 := by decide
  rcases family_descends (prefixWord ++ tailWord_258808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258821 : List Nat := [1, 3, 1, 1, 2, 1, 1, 12]
def baseStart_258821 : Nat := 118140960795 + 258821 * 2 ^ 59
def prefixEnd_258821 : Nat := 4983230072969 + 3 ^ 40 * 258821 * 2
def baseEnd_258821 : Nat := 9844413072402747803497

theorem tailTrace_258821 : CollatzResearch.WordTrace tailWord_258821 prefixEnd_258821 9844413072402747803497 := by
  unfold tailWord_258821
  simp only [CollatzResearch.WordTrace]
  refine ⟨9439977395343194952720317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6293318263562129968480211 9439977395343194952720317)
  ·
    refine ⟨3539991523253698107270119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9439977395343194952720317 3539991523253698107270119)
    ·
      refine ⟨5309987284880547160905179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3539991523253698107270119 5309987284880547160905179)
      ·
        refine ⟨7964980927320820741357769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5309987284880547160905179 7964980927320820741357769)
        ·
          refine ⟨5973735695490615556018327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 7964980927320820741357769 5973735695490615556018327)
          ·
            refine ⟨8960603543235923334027491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5973735695490615556018327 8960603543235923334027491)
            ·
              refine ⟨13440905314853885001041237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 8960603543235923334027491 13440905314853885001041237)
              ·
                refine ⟨9844413072402747803497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 12 13440905314853885001041237 9844413072402747803497)
                ·
                  rfl

theorem cell22_258821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 1, 1, 12].length) (baseStart_258821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258821 prefixEnd_258821 := by exact prefixLift 258821
  have htrace : WordTrace (prefixWord ++ tailWord_258821) baseStart_258821 baseEnd_258821 := by
    simpa [prefixWord, tailWord_258821, baseEnd_258821] using wordTrace_append hprefix tailTrace_258821
  have hstable : (prefixWord ++ tailWord_258821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258821).length < 2 ^ (prefixWord ++ tailWord_258821).sum := by decide
  have hdescent : baseEnd_258821 < baseStart_258821 := by decide
  rcases family_descends (prefixWord ++ tailWord_258821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258928 : List Nat := [2, 1, 1, 1, 4, 1, 2, 4, 6]
def baseStart_258928 : Nat := 118140960795 + 258928 * 2 ^ 59
def prefixEnd_258928 : Nat := 4983230072969 + 3 ^ 40 * 258928 * 2
def baseEnd_258928 : Nat := 29545448646104039268715

theorem tailTrace_258928 : CollatzResearch.WordTrace tailWord_258928 prefixEnd_258928 29545448646104039268715 := by
  unfold tailWord_258928
  simp only [CollatzResearch.WordTrace]
  refine ⟨4721940002977776113432719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6295920003970368151243625 4721940002977776113432719)
  ·
    refine ⟨7082910004466664170149079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4721940002977776113432719 7082910004466664170149079)
    ·
      refine ⟨10624365006699996255223619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7082910004466664170149079 10624365006699996255223619)
      ·
        refine ⟨15936547510049994382835429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10624365006699996255223619 15936547510049994382835429)
        ·
          refine ⟨2988102658134373946781643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 15936547510049994382835429 2988102658134373946781643)
          ·
            refine ⟨4482153987201560920172465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2988102658134373946781643 4482153987201560920172465)
            ·
              refine ⟨3361615490401170690129349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4482153987201560920172465 3361615490401170690129349)
              ·
                refine ⟨630302904450219504399253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 3361615490401170690129349 630302904450219504399253)
                ·
                  refine ⟨29545448646104039268715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 630302904450219504399253 29545448646104039268715)
                  ·
                    rfl

theorem cell22_258928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 6].length) (baseStart_258928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258928 prefixEnd_258928 := by exact prefixLift 258928
  have htrace : WordTrace (prefixWord ++ tailWord_258928) baseStart_258928 baseEnd_258928 := by
    simpa [prefixWord, tailWord_258928, baseEnd_258928] using wordTrace_append hprefix tailTrace_258928
  have hstable : (prefixWord ++ tailWord_258928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258928).length < 2 ^ (prefixWord ++ tailWord_258928).sum := by decide
  have hdescent : baseEnd_258928 < baseStart_258928 := by decide
  rcases family_descends (prefixWord ++ tailWord_258928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258943 : List Nat := [1, 1, 2, 2, 1, 1, 5, 1, 3, 5]
def baseStart_258943 : Nat := 118140960795 + 258943 * 2 ^ 59
def prefixEnd_258943 : Nat := 4983230072969 + 3 ^ 40 * 258943 * 2
def baseEnd_258943 : Nat := 88641480744857078681099

theorem tailTrace_258943 : CollatzResearch.WordTrace tailWord_258943 prefixEnd_258943 88641480744857078681099 := by
  unfold tailWord_258943
  simp only [CollatzResearch.WordTrace]
  refine ⟨9444427100901209788661483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6296284733934139859107655 9444427100901209788661483)
  ·
    refine ⟨14166640651351814682992225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9444427100901209788661483 14166640651351814682992225)
    ·
      refine ⟨10624980488513861012244169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14166640651351814682992225 10624980488513861012244169)
      ·
        refine ⟨7968735366385395759183127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10624980488513861012244169 7968735366385395759183127)
        ·
          refine ⟨11953103049578093638774691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7968735366385395759183127 11953103049578093638774691)
          ·
            refine ⟨17929654574367140458162037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11953103049578093638774691 17929654574367140458162037)
            ·
              refine ⟨1680905116346919417952691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 17929654574367140458162037 1680905116346919417952691)
              ·
                refine ⟨2521357674520379126929037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1680905116346919417952691 2521357674520379126929037)
                ·
                  refine ⟨945509127945142172598389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2521357674520379126929037 945509127945142172598389)
                  ·
                    refine ⟨88641480744857078681099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 945509127945142172598389 88641480744857078681099)
                    ·
                      rfl

theorem cell22_258943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 1, 3, 5].length) (baseStart_258943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258943 prefixEnd_258943 := by exact prefixLift 258943
  have htrace : WordTrace (prefixWord ++ tailWord_258943) baseStart_258943 baseEnd_258943 := by
    simpa [prefixWord, tailWord_258943, baseEnd_258943] using wordTrace_append hprefix tailTrace_258943
  have hstable : (prefixWord ++ tailWord_258943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258943).length < 2 ^ (prefixWord ++ tailWord_258943).sum := by decide
  have hdescent : baseEnd_258943 < baseStart_258943 := by decide
  rcases family_descends (prefixWord ++ tailWord_258943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258947 : List Nat := [1, 1, 1, 3, 4, 1, 5, 1, 1, 4]
def baseStart_258947 : Nat := 118140960795 + 258947 * 2 ^ 59
def prefixEnd_258947 : Nat := 4983230072969 + 3 ^ 40 * 258947 * 2
def baseEnd_258947 : Nat := 88642850026602401581087

theorem tailTrace_258947 : CollatzResearch.WordTrace tailWord_258947 prefixEnd_258947 88642850026602401581087 := by
  unfold tailWord_258947
  simp only [CollatzResearch.WordTrace]
  refine ⟨9444572992886718471807095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6296381995257812314538063 9444572992886718471807095)
  ·
    refine ⟨14166859489330077707710643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9444572992886718471807095 14166859489330077707710643)
    ·
      refine ⟨21250289233995116561565965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14166859489330077707710643 21250289233995116561565965)
      ·
        refine ⟨7968858462748168710587237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21250289233995116561565965 7968858462748168710587237)
        ·
          refine ⟨1494160961765281633235107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7968858462748168710587237 1494160961765281633235107)
          ·
            refine ⟨2241241442647922449852661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1494160961765281633235107 2241241442647922449852661)
            ·
              refine ⟨210116385248242729673687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2241241442647922449852661 210116385248242729673687)
              ·
                refine ⟨315174577872364094510531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210116385248242729673687 315174577872364094510531)
                ·
                  refine ⟨472761866808546141765797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315174577872364094510531 472761866808546141765797)
                  ·
                    refine ⟨88642850026602401581087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 472761866808546141765797 88642850026602401581087)
                    ·
                      rfl

theorem cell22_258947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 5, 1, 1, 4].length) (baseStart_258947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258947 prefixEnd_258947 := by exact prefixLift 258947
  have htrace : WordTrace (prefixWord ++ tailWord_258947) baseStart_258947 baseEnd_258947 := by
    simpa [prefixWord, tailWord_258947, baseEnd_258947] using wordTrace_append hprefix tailTrace_258947
  have hstable : (prefixWord ++ tailWord_258947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258947).length < 2 ^ (prefixWord ++ tailWord_258947).sum := by decide
  have hdescent : baseEnd_258947 < baseStart_258947 := by decide
  rcases family_descends (prefixWord ++ tailWord_258947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258977 : List Nat := [1, 2, 3, 4, 1, 2, 2, 1, 1, 5]
def baseStart_258977 : Nat := 118140960795 + 258977 * 2 ^ 59
def prefixEnd_258977 : Nat := 4983230072969 + 3 ^ 40 * 258977 * 2
def baseEnd_258977 : Nat := 88653119639692323330995

theorem tailTrace_258977 : CollatzResearch.WordTrace tailWord_258977 prefixEnd_258977 88653119639692323330995 := by
  unfold tailWord_258977
  simp only [CollatzResearch.WordTrace]
  refine ⟨9445667182778033595399185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6297111455185355730266123 9445667182778033595399185)
  ·
    refine ⟨7084250387083525196549389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9445667182778033595399185 7084250387083525196549389)
    ·
      refine ⟨2656593895156321948706021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7084250387083525196549389 2656593895156321948706021)
      ·
        refine ⟨498111355341810365382379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2656593895156321948706021 498111355341810365382379)
        ·
          refine ⟨747167033012715548073569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498111355341810365382379 747167033012715548073569)
          ·
            refine ⟨560375274759536661055177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 747167033012715548073569 560375274759536661055177)
            ·
              refine ⟨420281456069652495791383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 560375274759536661055177 420281456069652495791383)
              ·
                refine ⟨630422184104478743687075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420281456069652495791383 630422184104478743687075)
                ·
                  refine ⟨945633276156718115530613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 630422184104478743687075 945633276156718115530613)
                  ·
                    refine ⟨88653119639692323330995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 945633276156718115530613 88653119639692323330995)
                    ·
                      rfl

theorem cell22_258977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_258977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258977 prefixEnd_258977 := by exact prefixLift 258977
  have htrace : WordTrace (prefixWord ++ tailWord_258977) baseStart_258977 baseEnd_258977 := by
    simpa [prefixWord, tailWord_258977, baseEnd_258977] using wordTrace_append hprefix tailTrace_258977
  have hstable : (prefixWord ++ tailWord_258977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258977).length < 2 ^ (prefixWord ++ tailWord_258977).sum := by decide
  have hdescent : baseEnd_258977 < baseStart_258977 := by decide
  rcases family_descends (prefixWord ++ tailWord_258977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258988 : List Nat := [2, 2, 1, 1, 1, 1, 2, 3, 2, 7]
def baseStart_258988 : Nat := 118140960795 + 258988 * 2 ^ 59
def prefixEnd_258988 : Nat := 4983230072969 + 3 ^ 40 * 258988 * 2
def baseEnd_258988 : Nat := 88656885164491961305961

theorem tailTrace_258988 : CollatzResearch.WordTrace tailWord_258988 prefixEnd_258988 88656885164491961305961 := by
  unfold tailWord_258988
  simp only [CollatzResearch.WordTrace]
  refine ⟨4723034192869091237024809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6297378923825454982699745 4723034192869091237024809)
  ·
    refine ⟨3542275644651818427768607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4723034192869091237024809 3542275644651818427768607)
    ·
      refine ⟨5313413466977727641652911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3542275644651818427768607 5313413466977727641652911)
      ·
        refine ⟨7970120200466591462479367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5313413466977727641652911 7970120200466591462479367)
        ·
          refine ⟨11955180300699887193719051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 7970120200466591462479367 11955180300699887193719051)
          ·
            refine ⟨17932770451049830790578577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 11955180300699887193719051 17932770451049830790578577)
            ·
              refine ⟨13449577838287373092933933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17932770451049830790578577 13449577838287373092933933)
              ·
                refine ⟨5043591689357764909850225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13449577838287373092933933 5043591689357764909850225)
                ·
                  refine ⟨3782693767018323682387669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5043591689357764909850225 3782693767018323682387669)
                  ·
                    refine ⟨88656885164491961305961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3782693767018323682387669 88656885164491961305961)
                    ·
                      rfl

theorem cell22_258988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 7].length) (baseStart_258988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258988 prefixEnd_258988 := by exact prefixLift 258988
  have htrace : WordTrace (prefixWord ++ tailWord_258988) baseStart_258988 baseEnd_258988 := by
    simpa [prefixWord, tailWord_258988, baseEnd_258988] using wordTrace_append hprefix tailTrace_258988
  have hstable : (prefixWord ++ tailWord_258988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258988).length < 2 ^ (prefixWord ++ tailWord_258988).sum := by decide
  have hdescent : baseEnd_258988 < baseStart_258988 := by decide
  rcases family_descends (prefixWord ++ tailWord_258988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258996 : List Nat := [2, 5, 2, 1, 1, 2, 2, 3, 4]
def baseStart_258996 : Nat := 118140960795 + 258996 * 2 ^ 59
def prefixEnd_258996 : Nat := 4983230072969 + 3 ^ 40 * 258996 * 2
def baseEnd_258996 : Nat := 29553207909327535701979

theorem tailTrace_258996 : CollatzResearch.WordTrace tailWord_258996 prefixEnd_258996 29553207909327535701979 := by
  unfold tailWord_258996
  simp only [CollatzResearch.WordTrace]
  refine ⟨4723180084854599920170421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6297573446472799893560561 4723180084854599920170421)
  ·
    refine ⟨442798132955118742515977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 4723180084854599920170421 442798132955118742515977)
    ·
      refine ⟨332098599716339056886983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 442798132955118742515977 332098599716339056886983)
      ·
        refine ⟨498147899574508585330475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 332098599716339056886983 498147899574508585330475)
        ·
          refine ⟨747221849361762877995713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498147899574508585330475 747221849361762877995713)
          ·
            refine ⟨560416387021322158496785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 747221849361762877995713 560416387021322158496785)
            ·
              refine ⟨420312290265991618872589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 560416387021322158496785 420312290265991618872589)
              ·
                refine ⟨157617108849746857077221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 420312290265991618872589 157617108849746857077221)
                ·
                  refine ⟨29553207909327535701979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157617108849746857077221 29553207909327535701979)
                  ·
                    rfl

theorem cell22_258996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_258996 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258996 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258996 prefixEnd_258996 := by exact prefixLift 258996
  have htrace : WordTrace (prefixWord ++ tailWord_258996) baseStart_258996 baseEnd_258996 := by
    simpa [prefixWord, tailWord_258996, baseEnd_258996] using wordTrace_append hprefix tailTrace_258996
  have hstable : (prefixWord ++ tailWord_258996).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258996).length < 2 ^ (prefixWord ++ tailWord_258996).sum := by decide
  have hdescent : baseEnd_258996 < baseStart_258996 := by decide
  rcases family_descends (prefixWord ++ tailWord_258996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_258998 : List Nat := [5, 1, 4, 1, 1, 1, 1, 3, 1, 4]
def baseStart_258998 : Nat := 118140960795 + 258998 * 2 ^ 59
def prefixEnd_258998 : Nat := 4983230072969 + 3 ^ 40 * 258998 * 2
def baseEnd_258998 : Nat := 88660308368855268555931

theorem tailTrace_258998 : CollatzResearch.WordTrace tailWord_258998 prefixEnd_258998 88660308368855268555931 := by
  unfold tailWord_258998
  simp only [CollatzResearch.WordTrace]
  refine ⟨590402069731372136369603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 6297622077134636121275765 590402069731372136369603)
  ·
    refine ⟨885603104597058204554405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 590402069731372136369603 885603104597058204554405)
    ·
      refine ⟨166050582111948413353951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 885603104597058204554405 166050582111948413353951)
      ·
        refine ⟨249075873167922620030927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 166050582111948413353951 249075873167922620030927)
        ·
          refine ⟨373613809751883930046391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 249075873167922620030927 373613809751883930046391)
          ·
            refine ⟨560420714627825895069587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 373613809751883930046391 560420714627825895069587)
            ·
              refine ⟨840631071941738842604381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 560420714627825895069587 840631071941738842604381)
              ·
                refine ⟨315236651978152065976643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 840631071941738842604381 315236651978152065976643)
                ·
                  refine ⟨472854977967228098964965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315236651978152065976643 472854977967228098964965)
                  ·
                    refine ⟨88660308368855268555931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 472854977967228098964965 88660308368855268555931)
                    ·
                      rfl

theorem cell22_258998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_258998 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_258998 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_258998 prefixEnd_258998 := by exact prefixLift 258998
  have htrace : WordTrace (prefixWord ++ tailWord_258998) baseStart_258998 baseEnd_258998 := by
    simpa [prefixWord, tailWord_258998, baseEnd_258998] using wordTrace_append hprefix tailTrace_258998
  have hstable : (prefixWord ++ tailWord_258998).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_258998).length < 2 ^ (prefixWord ++ tailWord_258998).sum := by decide
  have hdescent : baseEnd_258998 < baseStart_258998 := by decide
  rcases family_descends (prefixWord ++ tailWord_258998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259022 : List Nat := [4, 1, 1, 1, 2, 3, 1, 3, 3, 3]
def baseStart_259022 : Nat := 118140960795 + 259022 * 2 ^ 59
def prefixEnd_259022 : Nat := 4983230072969 + 3 ^ 40 * 259022 * 2
def baseEnd_259022 : Nat := 88668524059327205955857

theorem tailTrace_259022 : CollatzResearch.WordTrace tailWord_259022 prefixEnd_259022 88668524059327205955857 := by
  unfold tailWord_259022
  simp only [CollatzResearch.WordTrace]
  refine ⟨1180913558451875785098415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6298205645076670853858213 1180913558451875785098415)
  ·
    refine ⟨1771370337677813677647623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1180913558451875785098415 1771370337677813677647623)
    ·
      refine ⟨2657055506516720516471435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1771370337677813677647623 2657055506516720516471435)
      ·
        refine ⟨3985583259775080774707153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2657055506516720516471435 3985583259775080774707153)
        ·
          refine ⟨2989187444831310581030365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3985583259775080774707153 2989187444831310581030365)
          ·
            refine ⟨1120945291811741467886387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2989187444831310581030365 1120945291811741467886387)
            ·
              refine ⟨1681417937717612201829581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1120945291811741467886387 1681417937717612201829581)
              ·
                refine ⟨630531726644104575686093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1681417937717612201829581 630531726644104575686093)
                ·
                  refine ⟨236449397491539215882285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 630531726644104575686093 236449397491539215882285)
                  ·
                    refine ⟨88668524059327205955857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 236449397491539215882285 88668524059327205955857)
                    ·
                      rfl

theorem cell22_259022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_259022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259022 prefixEnd_259022 := by exact prefixLift 259022
  have htrace : WordTrace (prefixWord ++ tailWord_259022) baseStart_259022 baseEnd_259022 := by
    simpa [prefixWord, tailWord_259022, baseEnd_259022] using wordTrace_append hprefix tailTrace_259022
  have hstable : (prefixWord ++ tailWord_259022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259022).length < 2 ^ (prefixWord ++ tailWord_259022).sum := by decide
  have hdescent : baseEnd_259022 < baseStart_259022 := by decide
  rcases family_descends (prefixWord ++ tailWord_259022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259129 : List Nat := [1, 2, 1, 5, 2, 1, 1, 4, 2, 3]
def baseStart_259129 : Nat := 118140960795 + 259129 * 2 ^ 59
def prefixEnd_259129 : Nat := 4983230072969 + 3 ^ 40 * 259129 * 2
def baseEnd_259129 : Nat := 88705152346014593530529

theorem tailTrace_259129 : CollatzResearch.WordTrace tailWord_259129 prefixEnd_259129 88705152346014593530529 := by
  unfold tailWord_259129
  simp only [CollatzResearch.WordTrace]
  refine ⟨9451211078227363554932441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6300807385484909036621627 9451211078227363554932441)
  ·
    refine ⟨7088408308670522666199331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9451211078227363554932441 7088408308670522666199331)
    ·
      refine ⟨10632612463005783999298997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7088408308670522666199331 10632612463005783999298997)
      ·
        refine ⟨996807418406792249934281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 10632612463005783999298997 996807418406792249934281)
        ·
          refine ⟨747605563805094187450711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 996807418406792249934281 747605563805094187450711)
          ·
            refine ⟨1121408345707641281176067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747605563805094187450711 1121408345707641281176067)
            ·
              refine ⟨1682112518561461921764101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1121408345707641281176067 1682112518561461921764101)
              ·
                refine ⟨315396097230274110330769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1682112518561461921764101 315396097230274110330769)
                ·
                  refine ⟨236547072922705582748077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 315396097230274110330769 236547072922705582748077)
                  ·
                    refine ⟨88705152346014593530529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 236547072922705582748077 88705152346014593530529)
                    ·
                      rfl

theorem cell22_259129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 4, 2, 3].length) (baseStart_259129 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259129 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259129 prefixEnd_259129 := by exact prefixLift 259129
  have htrace : WordTrace (prefixWord ++ tailWord_259129) baseStart_259129 baseEnd_259129 := by
    simpa [prefixWord, tailWord_259129, baseEnd_259129] using wordTrace_append hprefix tailTrace_259129
  have hstable : (prefixWord ++ tailWord_259129).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259129).length < 2 ^ (prefixWord ++ tailWord_259129).sum := by decide
  have hdescent : baseEnd_259129 < baseStart_259129 := by decide
  rcases family_descends (prefixWord ++ tailWord_259129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259215 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 12]
def baseStart_259215 : Nat := 118140960795 + 259215 * 2 ^ 59
def prefixEnd_259215 : Nat := 4983230072969 + 3 ^ 40 * 259215 * 2
def baseEnd_259215 : Nat := 29578197301179678626755

theorem tailTrace_259215 : CollatzResearch.WordTrace tailWord_259215 prefixEnd_259215 29578197301179678626755 := by
  unfold tailWord_259215
  simp only [CollatzResearch.WordTrace]
  refine ⟨9454347755915800242563099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6302898503943866828375399 9454347755915800242563099)
  ·
    refine ⟨14181521633873700363844649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9454347755915800242563099 14181521633873700363844649)
    ·
      refine ⟨10636141225405275272883487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14181521633873700363844649 10636141225405275272883487)
      ·
        refine ⟨15954211838107912909325231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10636141225405275272883487 15954211838107912909325231)
        ·
          refine ⟨23931317757161869363987847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 15954211838107912909325231 23931317757161869363987847)
          ·
            refine ⟨35896976635742804045981771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 23931317757161869363987847 35896976635742804045981771)
            ·
              refine ⟨53845464953614206068972657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 35896976635742804045981771 53845464953614206068972657)
              ·
                refine ⟨40384098715210654551729493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 53845464953614206068972657 40384098715210654551729493)
                ·
                  refine ⟨29578197301179678626755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 12 40384098715210654551729493 29578197301179678626755)
                  ·
                    rfl

theorem cell22_259215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 12].length) (baseStart_259215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259215 prefixEnd_259215 := by exact prefixLift 259215
  have htrace : WordTrace (prefixWord ++ tailWord_259215) baseStart_259215 baseEnd_259215 := by
    simpa [prefixWord, tailWord_259215, baseEnd_259215] using wordTrace_append hprefix tailTrace_259215
  have hstable : (prefixWord ++ tailWord_259215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259215).length < 2 ^ (prefixWord ++ tailWord_259215).sum := by decide
  have hdescent : baseEnd_259215 < baseStart_259215 := by decide
  rcases family_descends (prefixWord ++ tailWord_259215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259249 : List Nat := [1, 2, 2, 5, 1, 1, 3, 1, 6]
def baseStart_259249 : Nat := 118140960795 + 259249 * 2 ^ 59
def prefixEnd_259249 : Nat := 4983230072969 + 3 ^ 40 * 259249 * 2
def baseEnd_259249 : Nat := 29582076932791426843387

theorem tailTrace_259249 : CollatzResearch.WordTrace tailWord_259249 prefixEnd_259249 29582076932791426843387 := by
  unfold tailWord_259249
  simp only [CollatzResearch.WordTrace]
  refine ⟨9455587837792624049300801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6303725225195082699533867 9455587837792624049300801)
  ·
    refine ⟨7091690878344468036975601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9455587837792624049300801 7091690878344468036975601)
    ·
      refine ⟨5318768158758351027731701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7091690878344468036975601 5318768158758351027731701)
      ·
        refine ⟨498634514883595408849847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 5318768158758351027731701 498634514883595408849847)
        ·
          refine ⟨747951772325393113274771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 498634514883595408849847 747951772325393113274771)
          ·
            refine ⟨1121927658488089669912157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 747951772325393113274771 1121927658488089669912157)
            ·
              refine ⟨420722871933033626217059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1121927658488089669912157 420722871933033626217059)
              ·
                refine ⟨631084307899550439325589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420722871933033626217059 631084307899550439325589)
                ·
                  refine ⟨29582076932791426843387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 631084307899550439325589 29582076932791426843387)
                  ·
                    rfl

theorem cell22_259249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 6].length) (baseStart_259249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259249 prefixEnd_259249 := by exact prefixLift 259249
  have htrace : WordTrace (prefixWord ++ tailWord_259249) baseStart_259249 baseEnd_259249 := by
    simpa [prefixWord, tailWord_259249, baseEnd_259249] using wordTrace_append hprefix tailTrace_259249
  have hstable : (prefixWord ++ tailWord_259249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259249).length < 2 ^ (prefixWord ++ tailWord_259249).sum := by decide
  have hdescent : baseEnd_259249 < baseStart_259249 := by decide
  rcases family_descends (prefixWord ++ tailWord_259249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259268 : List Nat := [2, 3, 3, 1, 3, 2, 1, 2, 1, 4]
def baseStart_259268 : Nat := 118140960795 + 259268 * 2 ^ 59
def prefixEnd_259268 : Nat := 4983230072969 + 3 ^ 40 * 259268 * 2
def baseEnd_259268 : Nat := 88752734886664564305103

theorem tailTrace_259268 : CollatzResearch.WordTrace tailWord_259268 prefixEnd_259268 88752734886664564305103 := by
  unfold tailWord_259268
  simp only [CollatzResearch.WordTrace]
  refine ⟨4728140412361895147121229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6304187216482526862828305 4728140412361895147121229)
  ·
    refine ⟨1773052654635710680170461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 4728140412361895147121229 1773052654635710680170461)
    ·
      refine ⟨664894745488391505063923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1773052654635710680170461 664894745488391505063923)
      ·
        refine ⟨997342118232587257595885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 664894745488391505063923 997342118232587257595885)
        ·
          refine ⟨374003294337220221598457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 997342118232587257595885 374003294337220221598457)
          ·
            refine ⟨280502470752915166198843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 374003294337220221598457 280502470752915166198843)
            ·
              refine ⟨420753706129372749298265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280502470752915166198843 420753706129372749298265)
              ·
                refine ⟨315565279597029561973699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420753706129372749298265 315565279597029561973699)
                ·
                  refine ⟨473347919395544342960549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315565279597029561973699 473347919395544342960549)
                  ·
                    refine ⟨88752734886664564305103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 473347919395544342960549 88752734886664564305103)
                    ·
                      rfl

theorem cell22_259268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_259268 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259268 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259268 prefixEnd_259268 := by exact prefixLift 259268
  have htrace : WordTrace (prefixWord ++ tailWord_259268) baseStart_259268 baseEnd_259268 := by
    simpa [prefixWord, tailWord_259268, baseEnd_259268] using wordTrace_append hprefix tailTrace_259268
  have hstable : (prefixWord ++ tailWord_259268).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259268).length < 2 ^ (prefixWord ++ tailWord_259268).sum := by decide
  have hdescent : baseEnd_259268 < baseStart_259268 := by decide
  rcases family_descends (prefixWord ++ tailWord_259268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259307 : List Nat := [1, 1, 1, 1, 2, 6, 1, 1, 2, 6]
def baseStart_259307 : Nat := 118140960795 + 259307 * 2 ^ 59
def prefixEnd_259307 : Nat := 4983230072969 + 3 ^ 40 * 259307 * 2
def baseEnd_259307 : Nat := 88766085383681462579983

theorem tailTrace_259307 : CollatzResearch.WordTrace tailWord_259307 prefixEnd_259307 88766085383681462579983 := by
  unfold tailWord_259307
  simp only [CollatzResearch.WordTrace]
  refine ⟨9457703271582499954912175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6305135514388333303274783 9457703271582499954912175)
  ·
    refine ⟨14186554907373749932368263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9457703271582499954912175 14186554907373749932368263)
    ·
      refine ⟨21279832361060624898552395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14186554907373749932368263 21279832361060624898552395)
      ·
        refine ⟨31919748541590937347828593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21279832361060624898552395 31919748541590937347828593)
        ·
          refine ⟨23939811406193203010871445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 31919748541590937347828593 23939811406193203010871445)
          ·
            refine ⟨1122178659665306391134599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 23939811406193203010871445 1122178659665306391134599)
            ·
              refine ⟨1683267989497959586701899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1122178659665306391134599 1683267989497959586701899)
              ·
                refine ⟨2524901984246939380052849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1683267989497959586701899 2524901984246939380052849)
                ·
                  refine ⟨1893676488185204535039637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2524901984246939380052849 1893676488185204535039637)
                  ·
                    refine ⟨88766085383681462579983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1893676488185204535039637 88766085383681462579983)
                    ·
                      rfl

theorem cell22_259307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 6].length) (baseStart_259307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259307 prefixEnd_259307 := by exact prefixLift 259307
  have htrace : WordTrace (prefixWord ++ tailWord_259307) baseStart_259307 baseEnd_259307 := by
    simpa [prefixWord, tailWord_259307, baseEnd_259307] using wordTrace_append hprefix tailTrace_259307
  have hstable : (prefixWord ++ tailWord_259307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259307).length < 2 ^ (prefixWord ++ tailWord_259307).sum := by decide
  have hdescent : baseEnd_259307 < baseStart_259307 := by decide
  rcases family_descends (prefixWord ++ tailWord_259307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259311 : List Nat := [1, 1, 2, 1, 8, 1, 1, 7]
def baseStart_259311 : Nat := 118140960795 + 259311 * 2 ^ 59
def prefixEnd_259311 : Nat := 4983230072969 + 3 ^ 40 * 259311 * 2
def baseEnd_259311 : Nat := 9863050518380753942219

theorem tailTrace_259311 : CollatzResearch.WordTrace tailWord_259311 prefixEnd_259311 9863050518380753942219 := by
  unfold tailWord_259311
  simp only [CollatzResearch.WordTrace]
  refine ⟨9457849163568008638057787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6305232775712005758705191 9457849163568008638057787)
  ·
    refine ⟨14186773745352012957086681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9457849163568008638057787 14186773745352012957086681)
    ·
      refine ⟨10640080309014009717815011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14186773745352012957086681 10640080309014009717815011)
      ·
        refine ⟨15960120463521014576722517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10640080309014009717815011 15960120463521014576722517)
        ·
          refine ⟨187032661681886889570967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 15960120463521014576722517 187032661681886889570967)
          ·
            refine ⟨280548992522830334356451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187032661681886889570967 280548992522830334356451)
            ·
              refine ⟨420823488784245501534677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280548992522830334356451 420823488784245501534677)
              ·
                refine ⟨9863050518380753942219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 420823488784245501534677 9863050518380753942219)
                ·
                  rfl

theorem cell22_259311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 1, 1, 7].length) (baseStart_259311 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259311 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259311 prefixEnd_259311 := by exact prefixLift 259311
  have htrace : WordTrace (prefixWord ++ tailWord_259311) baseStart_259311 baseEnd_259311 := by
    simpa [prefixWord, tailWord_259311, baseEnd_259311] using wordTrace_append hprefix tailTrace_259311
  have hstable : (prefixWord ++ tailWord_259311).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259311).length < 2 ^ (prefixWord ++ tailWord_259311).sum := by decide
  have hdescent : baseEnd_259311 < baseStart_259311 := by decide
  rcases family_descends (prefixWord ++ tailWord_259311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259326 : List Nat := [4, 2, 2, 1, 1, 2, 1, 1, 5, 3]
def baseStart_259326 : Nat := 118140960795 + 259326 * 2 ^ 59
def prefixEnd_259326 : Nat := 4983230072969 + 3 ^ 40 * 259326 * 2
def baseEnd_259326 : Nat := 88772589471971746354925

theorem tailTrace_259326 : CollatzResearch.WordTrace tailWord_259326 prefixEnd_259326 88772589471971746354925 := by
  unfold tailWord_259326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1182299532314208274981729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6305597505675777466569221 1182299532314208274981729)
  ·
    refine ⟨886724649235656206236297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1182299532314208274981729 886724649235656206236297)
    ·
      refine ⟨665043486926742154677223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 886724649235656206236297 665043486926742154677223)
      ·
        refine ⟨997565230390113232015835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665043486926742154677223 997565230390113232015835)
        ·
          refine ⟨1496347845585169848023753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 997565230390113232015835 1496347845585169848023753)
          ·
            refine ⟨1122260884188877386017815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1496347845585169848023753 1122260884188877386017815)
            ·
              refine ⟨1683391326283316079026723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1122260884188877386017815 1683391326283316079026723)
              ·
                refine ⟨2525086989424974118540085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1683391326283316079026723 2525086989424974118540085)
                ·
                  refine ⟨236726905258591323613133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2525086989424974118540085 236726905258591323613133)
                  ·
                    refine ⟨88772589471971746354925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 236726905258591323613133 88772589471971746354925)
                    ·
                      rfl

theorem cell22_259326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_259326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259326 prefixEnd_259326 := by exact prefixLift 259326
  have htrace : WordTrace (prefixWord ++ tailWord_259326) baseStart_259326 baseEnd_259326 := by
    simpa [prefixWord, tailWord_259326, baseEnd_259326] using wordTrace_append hprefix tailTrace_259326
  have hstable : (prefixWord ++ tailWord_259326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259326).length < 2 ^ (prefixWord ++ tailWord_259326).sum := by decide
  have hdescent : baseEnd_259326 < baseStart_259326 := by decide
  rcases family_descends (prefixWord ++ tailWord_259326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259330 : List Nat := [3, 4, 1, 1, 4, 1, 1, 1, 2, 4]
def baseStart_259330 : Nat := 118140960795 + 259330 * 2 ^ 59
def prefixEnd_259330 : Nat := 4983230072969 + 3 ^ 40 * 259330 * 2
def baseEnd_259330 : Nat := 88773958753717069254913

theorem tailTrace_259330 : CollatzResearch.WordTrace tailWord_259330 prefixEnd_259330 88773958753717069254913 := by
  unfold tailWord_259330
  simp only [CollatzResearch.WordTrace]
  refine ⟨2364635537624793720749861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6305694766999449921999629 2364635537624793720749861)
  ·
    refine ⟨443369163304648822640599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2364635537624793720749861 443369163304648822640599)
    ·
      refine ⟨665053744956973233960899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 443369163304648822640599 665053744956973233960899)
      ·
        refine ⟨997580617435459850941349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665053744956973233960899 997580617435459850941349)
        ·
          refine ⟨187046365769148722051503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 997580617435459850941349 187046365769148722051503)
          ·
            refine ⟨280569548653723083077255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 187046365769148722051503 280569548653723083077255)
            ·
              refine ⟨420854322980584624615883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 280569548653723083077255 420854322980584624615883)
              ·
                refine ⟨631281484470876936923825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 420854322980584624615883 631281484470876936923825)
                ·
                  refine ⟨473461113353157702692869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 631281484470876936923825 473461113353157702692869)
                  ·
                    refine ⟨88773958753717069254913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 473461113353157702692869 88773958753717069254913)
                    ·
                      rfl

theorem cell22_259330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 4, 1, 1, 1, 2, 4].length) (baseStart_259330 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259330 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259330 prefixEnd_259330 := by exact prefixLift 259330
  have htrace : WordTrace (prefixWord ++ tailWord_259330) baseStart_259330 baseEnd_259330 := by
    simpa [prefixWord, tailWord_259330, baseEnd_259330] using wordTrace_append hprefix tailTrace_259330
  have hstable : (prefixWord ++ tailWord_259330).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259330).length < 2 ^ (prefixWord ++ tailWord_259330).sum := by decide
  have hdescent : baseEnd_259330 < baseStart_259330 := by decide
  rcases family_descends (prefixWord ++ tailWord_259330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259337 : List Nat := [1, 2, 1, 1, 3, 3, 1, 2, 1, 7]
def baseStart_259337 : Nat := 118140960795 + 259337 * 2 ^ 59
def prefixEnd_259337 : Nat := 4983230072969 + 3 ^ 40 * 259337 * 2
def baseEnd_259337 : Nat := 88776354996771384329891

theorem tailTrace_259337 : CollatzResearch.WordTrace tailWord_259337 prefixEnd_259337 88776354996771384329891 := by
  unfold tailWord_259337
  simp only [CollatzResearch.WordTrace]
  refine ⟨9458797461473815078504265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6305864974315876719002843 9458797461473815078504265)
  ·
    refine ⟨7094098096105361308878199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9458797461473815078504265 7094098096105361308878199)
    ·
      refine ⟨10641147144158041963317299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7094098096105361308878199 10641147144158041963317299)
      ·
        refine ⟨15961720716237062944975949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10641147144158041963317299 15961720716237062944975949)
        ·
          refine ⟨5985645268588898604365981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 15961720716237062944975949 5985645268588898604365981)
          ·
            refine ⟨2244616975720836976637243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 5985645268588898604365981 2244616975720836976637243)
            ·
              refine ⟨3366925463581255464955865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2244616975720836976637243 3366925463581255464955865)
              ·
                refine ⟨2525194097685941598716899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3366925463581255464955865 2525194097685941598716899)
                ·
                  refine ⟨3787791146528912398075349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2525194097685941598716899 3787791146528912398075349)
                  ·
                    refine ⟨88776354996771384329891, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 3787791146528912398075349 88776354996771384329891)
                    ·
                      rfl

theorem cell22_259337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 1, 2, 1, 7].length) (baseStart_259337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259337 prefixEnd_259337 := by exact prefixLift 259337
  have htrace : WordTrace (prefixWord ++ tailWord_259337) baseStart_259337 baseEnd_259337 := by
    simpa [prefixWord, tailWord_259337, baseEnd_259337] using wordTrace_append hprefix tailTrace_259337
  have hstable : (prefixWord ++ tailWord_259337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259337).length < 2 ^ (prefixWord ++ tailWord_259337).sum := by decide
  have hdescent : baseEnd_259337 < baseStart_259337 := by decide
  rcases family_descends (prefixWord ++ tailWord_259337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259354 : List Nat := [3, 1, 1, 3, 3, 1, 1, 2, 2, 5]
def baseStart_259354 : Nat := 118140960795 + 259354 * 2 ^ 59
def prefixEnd_259354 : Nat := 4983230072969 + 3 ^ 40 * 259354 * 2
def baseEnd_259354 : Nat := 88782174444189006654839

theorem tailTrace_259354 : CollatzResearch.WordTrace tailWord_259354 prefixEnd_259354 88782174444189006654839 := by
  unfold tailWord_259354
  simp only [CollatzResearch.WordTrace]
  refine ⟨2364854375603056745468279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6306278334941484654582077 2364854375603056745468279)
  ·
    refine ⟨3547281563404585118202419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2364854375603056745468279 3547281563404585118202419)
    ·
      refine ⟨5320922345106877677303629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3547281563404585118202419 5320922345106877677303629)
      ·
        refine ⟨1995345879415079128988861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5320922345106877677303629 1995345879415079128988861)
        ·
          refine ⟨748254704780654673370823, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1995345879415079128988861 748254704780654673370823)
          ·
            refine ⟨1122382057170982010056235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748254704780654673370823 1122382057170982010056235)
            ·
              refine ⟨1683573085756473015084353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1122382057170982010056235 1683573085756473015084353)
              ·
                refine ⟨1262679814317354761313265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1683573085756473015084353 1262679814317354761313265)
                ·
                  refine ⟨947009860738016070984949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1262679814317354761313265 947009860738016070984949)
                  ·
                    refine ⟨88782174444189006654839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 947009860738016070984949 88782174444189006654839)
                    ·
                      rfl

theorem cell22_259354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 2, 2, 5].length) (baseStart_259354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259354 prefixEnd_259354 := by exact prefixLift 259354
  have htrace : WordTrace (prefixWord ++ tailWord_259354) baseStart_259354 baseEnd_259354 := by
    simpa [prefixWord, tailWord_259354, baseEnd_259354] using wordTrace_append hprefix tailTrace_259354
  have hstable : (prefixWord ++ tailWord_259354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259354).length < 2 ^ (prefixWord ++ tailWord_259354).sum := by decide
  have hdescent : baseEnd_259354 < baseStart_259354 := by decide
  rcases family_descends (prefixWord ++ tailWord_259354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259386 : List Nat := [3, 1, 1, 1, 4, 1, 4, 2, 1, 4]
def baseStart_259386 : Nat := 118140960795 + 259386 * 2 ^ 59
def prefixEnd_259386 : Nat := 4983230072969 + 3 ^ 40 * 259386 * 2
def baseEnd_259386 : Nat := 88793128698151589854741

theorem tailTrace_259386 : CollatzResearch.WordTrace tailWord_259386 prefixEnd_259386 88793128698151589854741 := by
  unfold tailWord_259386
  simp only [CollatzResearch.WordTrace]
  refine ⟨2365146159574074111759503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6307056425530864298025341 2365146159574074111759503)
  ·
    refine ⟨3547719239361111167639255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2365146159574074111759503 3547719239361111167639255)
    ·
      refine ⟨5321578859041666751458883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3547719239361111167639255 5321578859041666751458883)
      ·
        refine ⟨7982368288562500127188325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5321578859041666751458883 7982368288562500127188325)
        ·
          refine ⟨1496694054105468773847811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 7982368288562500127188325 1496694054105468773847811)
          ·
            refine ⟨2245041081158203160771717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1496694054105468773847811 2245041081158203160771717)
            ·
              refine ⟨420945202717163092644697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2245041081158203160771717 420945202717163092644697)
              ·
                refine ⟨315708902037872319483523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 420945202717163092644697 315708902037872319483523)
                ·
                  refine ⟨473563353056808479225285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 315708902037872319483523 473563353056808479225285)
                  ·
                    refine ⟨88793128698151589854741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 473563353056808479225285 88793128698151589854741)
                    ·
                      rfl

theorem cell22_259386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 2, 1, 4].length) (baseStart_259386 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259386 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259386 prefixEnd_259386 := by exact prefixLift 259386
  have htrace : WordTrace (prefixWord ++ tailWord_259386) baseStart_259386 baseEnd_259386 := by
    simpa [prefixWord, tailWord_259386, baseEnd_259386] using wordTrace_append hprefix tailTrace_259386
  have hstable : (prefixWord ++ tailWord_259386).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259386).length < 2 ^ (prefixWord ++ tailWord_259386).sum := by decide
  have hdescent : baseEnd_259386 < baseStart_259386 := by decide
  rcases family_descends (prefixWord ++ tailWord_259386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259401 : List Nat := [1, 2, 1, 1, 2, 3, 5, 3, 4]
def baseStart_259401 : Nat := 118140960795 + 259401 * 2 ^ 59
def prefixEnd_259401 : Nat := 4983230072969 + 3 ^ 40 * 259401 * 2
def baseEnd_259401 : Nat := 29599421168232183576565

theorem tailTrace_259401 : CollatzResearch.WordTrace tailWord_259401 prefixEnd_259401 29599421168232183576565 := by
  unfold tailWord_259401
  simp only [CollatzResearch.WordTrace]
  refine ⟨9461131733241954008834057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6307421155494636005889371 9461131733241954008834057)
  ·
    refine ⟨7095848799931465506625543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9461131733241954008834057 7095848799931465506625543)
    ·
      refine ⟨10643773199897198259938315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7095848799931465506625543 10643773199897198259938315)
      ·
        refine ⟨15965659799845797389907473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10643773199897198259938315 15965659799845797389907473)
        ·
          refine ⟨11974244849884348042430605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 15965659799845797389907473 11974244849884348042430605)
          ·
            refine ⟨4490341818706630515911477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 11974244849884348042430605 4490341818706630515911477)
            ·
              refine ⟨420969545503746610866701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 4490341818706630515911477 420969545503746610866701)
              ·
                refine ⟨157863579563904979075013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 420969545503746610866701 157863579563904979075013)
                ·
                  refine ⟨29599421168232183576565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157863579563904979075013 29599421168232183576565)
                  ·
                    rfl

theorem cell22_259401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 5, 3, 4].length) (baseStart_259401 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259401 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259401 prefixEnd_259401 := by exact prefixLift 259401
  have htrace : WordTrace (prefixWord ++ tailWord_259401) baseStart_259401 baseEnd_259401 := by
    simpa [prefixWord, tailWord_259401, baseEnd_259401] using wordTrace_append hprefix tailTrace_259401
  have hstable : (prefixWord ++ tailWord_259401).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259401).length < 2 ^ (prefixWord ++ tailWord_259401).sum := by decide
  have hdescent : baseEnd_259401 < baseStart_259401 := by decide
  rcases family_descends (prefixWord ++ tailWord_259401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259416 : List Nat := [2, 1, 2, 2, 1, 1, 4, 4, 2, 3]
def baseStart_259416 : Nat := 118140960795 + 259416 * 2 ^ 59
def prefixEnd_259416 : Nat := 4983230072969 + 3 ^ 40 * 259416 * 2
def baseEnd_259416 : Nat := 88803398311241511604649

theorem tailTrace_259416 : CollatzResearch.WordTrace tailWord_259416 prefixEnd_259416 88803398311241511604649 := by
  unfold tailWord_259416
  simp only [CollatzResearch.WordTrace]
  refine ⟨4730839414093805785315051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6307785885458407713753401 4730839414093805785315051)
  ·
    refine ⟨7096259121140708677972577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4730839414093805785315051 7096259121140708677972577)
    ·
      refine ⟨5322194340855531508479433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7096259121140708677972577 5322194340855531508479433)
      ·
        refine ⟨3991645755641648631359575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5322194340855531508479433 3991645755641648631359575)
        ·
          refine ⟨5987468633462472947039363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3991645755641648631359575 5987468633462472947039363)
          ·
            refine ⟨8981202950193709420559045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 5987468633462472947039363 8981202950193709420559045)
            ·
              refine ⟨1683975553161320516354821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 8981202950193709420559045 1683975553161320516354821)
              ·
                refine ⟨315745416217747596816529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1683975553161320516354821 315745416217747596816529)
                ·
                  refine ⟨236809062163310697612397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 315745416217747596816529 236809062163310697612397)
                  ·
                    refine ⟨88803398311241511604649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 236809062163310697612397 88803398311241511604649)
                    ·
                      rfl

theorem cell22_259416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 4, 2, 3].length) (baseStart_259416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259416 prefixEnd_259416 := by exact prefixLift 259416
  have htrace : WordTrace (prefixWord ++ tailWord_259416) baseStart_259416 baseEnd_259416 := by
    simpa [prefixWord, tailWord_259416, baseEnd_259416] using wordTrace_append hprefix tailTrace_259416
  have hstable : (prefixWord ++ tailWord_259416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259416).length < 2 ^ (prefixWord ++ tailWord_259416).sum := by decide
  have hdescent : baseEnd_259416 < baseStart_259416 := by decide
  rcases family_descends (prefixWord ++ tailWord_259416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259429 : List Nat := [1, 3, 1, 3, 1, 2, 4, 7]
def baseStart_259429 : Nat := 118140960795 + 259429 * 2 ^ 59
def prefixEnd_259429 : Nat := 4983230072969 + 3 ^ 40 * 259429 * 2
def baseEnd_259429 : Nat := 9867538719657090114401

theorem tailTrace_259429 : CollatzResearch.WordTrace tailWord_259429 prefixEnd_259429 9867538719657090114401 := by
  unfold tailWord_259429
  simp only [CollatzResearch.WordTrace]
  refine ⟨9462152977140514790853341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6308101984760343193902227 9462152977140514790853341)
  ·
    refine ⟨3548307366427693046570003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9462152977140514790853341 3548307366427693046570003)
    ·
      refine ⟨5322461049641539569855005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3548307366427693046570003 5322461049641539569855005)
      ·
        refine ⟨1995922893615577338695627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5322461049641539569855005 1995922893615577338695627)
        ·
          refine ⟨2993884340423366008043441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1995922893615577338695627 2993884340423366008043441)
          ·
            refine ⟨2245413255317524506032581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2993884340423366008043441 2245413255317524506032581)
            ·
              refine ⟨421014985372035844881109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2245413255317524506032581 421014985372035844881109)
              ·
                refine ⟨9867538719657090114401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 421014985372035844881109 9867538719657090114401)
                ·
                  rfl

theorem cell22_259429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 4, 7].length) (baseStart_259429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259429 prefixEnd_259429 := by exact prefixLift 259429
  have htrace : WordTrace (prefixWord ++ tailWord_259429) baseStart_259429 baseEnd_259429 := by
    simpa [prefixWord, tailWord_259429, baseEnd_259429] using wordTrace_append hprefix tailTrace_259429
  have hstable : (prefixWord ++ tailWord_259429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259429).length < 2 ^ (prefixWord ++ tailWord_259429).sum := by decide
  have hdescent : baseEnd_259429 < baseStart_259429 := by decide
  rcases family_descends (prefixWord ++ tailWord_259429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259476 : List Nat := [2, 4, 2, 1, 2, 1, 1, 1, 2, 6]
def baseStart_259476 : Nat := 118140960795 + 259476 * 2 ^ 59
def prefixEnd_259476 : Nat := 4983230072969 + 3 ^ 40 * 259476 * 2
def baseEnd_259476 : Nat := 88823937537421355104465

theorem tailTrace_259476 : CollatzResearch.WordTrace tailWord_259476 prefixEnd_259476 88823937537421355104465 := by
  unfold tailWord_259476
  simp only [CollatzResearch.WordTrace]
  refine ⟨4731933603985120908907141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6309244805313494545209521 4731933603985120908907141)
  ·
    refine ⟨887237550747210170420089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 4731933603985120908907141 887237550747210170420089)
    ·
      refine ⟨665428163060407627815067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 887237550747210170420089 665428163060407627815067)
      ·
        refine ⟨998142244590611441722601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 665428163060407627815067 998142244590611441722601)
        ·
          refine ⟨748606683442958581291951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 998142244590611441722601 748606683442958581291951)
          ·
            refine ⟨1122910025164437871937927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748606683442958581291951 1122910025164437871937927)
            ·
              refine ⟨1684365037746656807906891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1122910025164437871937927 1684365037746656807906891)
              ·
                refine ⟨2526547556619985211860337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1684365037746656807906891 2526547556619985211860337)
                ·
                  refine ⟨1894910667464988908895253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2526547556619985211860337 1894910667464988908895253)
                  ·
                    refine ⟨88823937537421355104465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1894910667464988908895253 88823937537421355104465)
                    ·
                      rfl

theorem cell22_259476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 1, 2, 6].length) (baseStart_259476 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259476 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259476 prefixEnd_259476 := by exact prefixLift 259476
  have htrace : WordTrace (prefixWord ++ tailWord_259476) baseStart_259476 baseEnd_259476 := by
    simpa [prefixWord, tailWord_259476, baseEnd_259476] using wordTrace_append hprefix tailTrace_259476
  have hstable : (prefixWord ++ tailWord_259476).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259476).length < 2 ^ (prefixWord ++ tailWord_259476).sum := by decide
  have hdescent : baseEnd_259476 < baseStart_259476 := by decide
  rcases family_descends (prefixWord ++ tailWord_259476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259566 : List Nat := [4, 1, 2, 1, 2, 1, 1, 3, 1, 6]
def baseStart_259566 : Nat := 118140960795 + 259566 * 2 ^ 59
def prefixEnd_259566 : Nat := 4983230072969 + 3 ^ 40 * 259566 * 2
def baseEnd_259566 : Nat := 88854746376691120354189

theorem tailTrace_259566 : CollatzResearch.WordTrace tailWord_259566 prefixEnd_259566 88854746376691120354189 := by
  unfold tailWord_259566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1183393722205523398573819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6311433185096124792393701 1183393722205523398573819)
  ·
    refine ⟨1775090583308285097860729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1183393722205523398573819 1775090583308285097860729)
    ·
      refine ⟨1331317937481213823395547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1775090583308285097860729 1331317937481213823395547)
      ·
        refine ⟨1996976906221820735093321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1331317937481213823395547 1996976906221820735093321)
        ·
          refine ⟨1497732679666365551319991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1996976906221820735093321 1497732679666365551319991)
          ·
            refine ⟨2246599019499548326979987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1497732679666365551319991 2246599019499548326979987)
            ·
              refine ⟨3369898529249322490469981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2246599019499548326979987 3369898529249322490469981)
              ·
                refine ⟨1263711948468495933926243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3369898529249322490469981 1263711948468495933926243)
                ·
                  refine ⟨1895567922702743900889365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1263711948468495933926243 1895567922702743900889365)
                  ·
                    refine ⟨88854746376691120354189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 1895567922702743900889365 88854746376691120354189)
                    ·
                      rfl

theorem cell22_259566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_259566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259566 prefixEnd_259566 := by exact prefixLift 259566
  have htrace : WordTrace (prefixWord ++ tailWord_259566) baseStart_259566 baseEnd_259566 := by
    simpa [prefixWord, tailWord_259566, baseEnd_259566] using wordTrace_append hprefix tailTrace_259566
  have hstable : (prefixWord ++ tailWord_259566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259566).length < 2 ^ (prefixWord ++ tailWord_259566).sum := by decide
  have hdescent : baseEnd_259566 < baseStart_259566 := by decide
  rcases family_descends (prefixWord ++ tailWord_259566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259570 : List Nat := [3, 2, 1, 4, 1, 1, 3, 3, 4]
def baseStart_259570 : Nat := 118140960795 + 259570 * 2 ^ 59
def prefixEnd_259570 : Nat := 4983230072969 + 3 ^ 40 * 259570 * 2
def baseEnd_259570 : Nat := 29618705219478814418059

theorem tailTrace_259570 : CollatzResearch.WordTrace tailWord_259570 prefixEnd_259570 29618705219478814418059 := by
  unfold tailWord_259570
  simp only [CollatzResearch.WordTrace]
  refine ⟨2366823917407423967934041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6311530446419797247824109 2366823917407423967934041)
  ·
    refine ⟨1775117938055567975950531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2366823917407423967934041 1775117938055567975950531)
    ·
      refine ⟨2662676907083351963925797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1775117938055567975950531 2662676907083351963925797)
      ·
        refine ⟨499251920078128493236087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2662676907083351963925797 499251920078128493236087)
        ·
          refine ⟨748877880117192739854131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 499251920078128493236087 748877880117192739854131)
          ·
            refine ⟨1123316820175789109781197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 748877880117192739854131 1123316820175789109781197)
            ·
              refine ⟨421243807565920916167949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1123316820175789109781197 421243807565920916167949)
              ·
                refine ⟨157966427837220343562981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 421243807565920916167949 157966427837220343562981)
                ·
                  refine ⟨29618705219478814418059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 157966427837220343562981 29618705219478814418059)
                  ·
                    rfl

theorem cell22_259570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3, 4].length) (baseStart_259570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259570 prefixEnd_259570 := by exact prefixLift 259570
  have htrace : WordTrace (prefixWord ++ tailWord_259570) baseStart_259570 baseEnd_259570 := by
    simpa [prefixWord, tailWord_259570, baseEnd_259570] using wordTrace_append hprefix tailTrace_259570
  have hstable : (prefixWord ++ tailWord_259570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259570).length < 2 ^ (prefixWord ++ tailWord_259570).sum := by decide
  have hdescent : baseEnd_259570 < baseStart_259570 := by decide
  rcases family_descends (prefixWord ++ tailWord_259570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259579 : List Nat := [1, 1, 1, 1, 1, 3, 2, 2, 1, 9]
def baseStart_259579 : Nat := 118140960795 + 259579 * 2 ^ 59
def prefixEnd_259579 : Nat := 4983230072969 + 3 ^ 40 * 259579 * 2
def baseEnd_259579 : Nat := 88859196542363419779149

theorem tailTrace_259579 : CollatzResearch.WordTrace tailWord_259579 prefixEnd_259579 88859196542363419779149 := by
  unfold tailWord_259579
  simp only [CollatzResearch.WordTrace]
  refine ⟨9467623926597090408813791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6311749284398060272542527 9467623926597090408813791)
  ·
    refine ⟨14201435889895635613220687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9467623926597090408813791 14201435889895635613220687)
    ·
      refine ⟨21302153834843453419831031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14201435889895635613220687 21302153834843453419831031)
      ·
        refine ⟨31953230752265180129746547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21302153834843453419831031 31953230752265180129746547)
        ·
          refine ⟨47929846128397770194619821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 31953230752265180129746547 47929846128397770194619821)
          ·
            refine ⟨17973692298149163822982433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 47929846128397770194619821 17973692298149163822982433)
            ·
              refine ⟨13480269223611872867236825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 17973692298149163822982433 13480269223611872867236825)
              ·
                refine ⟨10110201917708904650427619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13480269223611872867236825 10110201917708904650427619)
                ·
                  refine ⟨15165302876563356975641429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10110201917708904650427619 15165302876563356975641429)
                  ·
                    refine ⟨88859196542363419779149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 15165302876563356975641429 88859196542363419779149)
                    ·
                      rfl

theorem cell22_259579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 9].length) (baseStart_259579 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259579 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259579 prefixEnd_259579 := by exact prefixLift 259579
  have htrace : WordTrace (prefixWord ++ tailWord_259579) baseStart_259579 baseEnd_259579 := by
    simpa [prefixWord, tailWord_259579, baseEnd_259579] using wordTrace_append hprefix tailTrace_259579
  have hstable : (prefixWord ++ tailWord_259579).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259579).length < 2 ^ (prefixWord ++ tailWord_259579).sum := by decide
  have hdescent : baseEnd_259579 < baseStart_259579 := by decide
  rcases family_descends (prefixWord ++ tailWord_259579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259581 : List Nat := [1, 4, 1, 1, 1, 6, 8]
def baseStart_259581 : Nat := 118140960795 + 259581 * 2 ^ 59
def prefixEnd_259581 : Nat := 4983230072969 + 3 ^ 40 * 259581 * 2
def baseEnd_259581 : Nat := 3291106710490225230709

theorem tailTrace_259581 : CollatzResearch.WordTrace tailWord_259581 prefixEnd_259581 3291106710490225230709 := by
  unfold tailWord_259581
  simp only [CollatzResearch.WordTrace]
  refine ⟨9467696872589844750386597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6311797915059896500257731 9467696872589844750386597)
  ·
    refine ⟨1775193163610595890697487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9467696872589844750386597 1775193163610595890697487)
    ·
      refine ⟨2662789745415893836046231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1775193163610595890697487 2662789745415893836046231)
      ·
        refine ⟨3994184618123840754069347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2662789745415893836046231 3994184618123840754069347)
        ·
          refine ⟨5991276927185761131104021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3994184618123840754069347 5991276927185761131104021)
          ·
            refine ⟨280841105961832553020501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 5991276927185761131104021 280841105961832553020501)
            ·
              refine ⟨3291106710490225230709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 280841105961832553020501 3291106710490225230709)
              ·
                rfl

theorem cell22_259581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 8].length) (baseStart_259581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259581 prefixEnd_259581 := by exact prefixLift 259581
  have htrace : WordTrace (prefixWord ++ tailWord_259581) baseStart_259581 baseEnd_259581 := by
    simpa [prefixWord, tailWord_259581, baseEnd_259581] using wordTrace_append hprefix tailTrace_259581
  have hstable : (prefixWord ++ tailWord_259581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259581).length < 2 ^ (prefixWord ++ tailWord_259581).sum := by decide
  have hdescent : baseEnd_259581 < baseStart_259581 := by decide
  rcases family_descends (prefixWord ++ tailWord_259581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259598 : List Nat := [4, 1, 1, 2, 4, 1, 2, 7]
def baseStart_259598 : Nat := 118140960795 + 259598 * 2 ^ 59
def prefixEnd_259598 : Nat := 4983230072969 + 3 ^ 40 * 259598 * 2
def baseEnd_259598 : Nat := 9873966736739300394899

theorem tailTrace_259598 : CollatzResearch.WordTrace tailWord_259598 prefixEnd_259598 9873966736739300394899 := by
  unfold tailWord_259598
  simp only [CollatzResearch.WordTrace]
  refine ⟨1183539614191032081719431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6312211275685504435836965 1183539614191032081719431)
  ·
    refine ⟨1775309421286548122579147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1183539614191032081719431 1775309421286548122579147)
    ·
      refine ⟨2662964131929822183868721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1775309421286548122579147 2662964131929822183868721)
      ·
        refine ⟨1997223098947366637901541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2662964131929822183868721 1997223098947366637901541)
        ·
          refine ⟨374479331052631244606539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1997223098947366637901541 374479331052631244606539)
          ·
            refine ⟨561718996578946866909809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 374479331052631244606539 561718996578946866909809)
            ·
              refine ⟨421289247434210150182357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 561718996578946866909809 421289247434210150182357)
              ·
                refine ⟨9873966736739300394899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 421289247434210150182357 9873966736739300394899)
                ·
                  rfl

theorem cell22_259598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 4, 1, 2, 7].length) (baseStart_259598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259598 prefixEnd_259598 := by exact prefixLift 259598
  have htrace : WordTrace (prefixWord ++ tailWord_259598) baseStart_259598 baseEnd_259598 := by
    simpa [prefixWord, tailWord_259598, baseEnd_259598] using wordTrace_append hprefix tailTrace_259598
  have hstable : (prefixWord ++ tailWord_259598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259598).length < 2 ^ (prefixWord ++ tailWord_259598).sum := by decide
  have hdescent : baseEnd_259598 < baseStart_259598 := by decide
  rcases family_descends (prefixWord ++ tailWord_259598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259613 : List Nat := [1, 4, 2, 2, 1, 1, 2, 1, 5, 3]
def baseStart_259613 : Nat := 118140960795 + 259613 * 2 ^ 59
def prefixEnd_259613 : Nat := 4983230072969 + 3 ^ 40 * 259613 * 2
def baseEnd_259613 : Nat := 88870835437198664429045

theorem tailTrace_259613 : CollatzResearch.WordTrace tailWord_259613 prefixEnd_259613 88870835437198664429045 := by
  unfold tailWord_259613
  simp only [CollatzResearch.WordTrace]
  refine ⟨9468864008473914215551493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6312576005649276143700995 9468864008473914215551493)
  ·
    refine ⟨1775412001588858915415905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 9468864008473914215551493 1775412001588858915415905)
    ·
      refine ⟨1331559001191644186561929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1775412001588858915415905 1331559001191644186561929)
      ·
        refine ⟨998669250893733139921447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1331559001191644186561929 998669250893733139921447)
        ·
          refine ⟨1498003876340599709882171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 998669250893733139921447 1498003876340599709882171)
          ·
            refine ⟨2247005814510899564823257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1498003876340599709882171 2247005814510899564823257)
            ·
              refine ⟨1685254360883174673617443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2247005814510899564823257 1685254360883174673617443)
              ·
                refine ⟨2527881541324762010426165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1685254360883174673617443 2527881541324762010426165)
                ·
                  refine ⟨236988894499196438477453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2527881541324762010426165 236988894499196438477453)
                  ·
                    refine ⟨88870835437198664429045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 236988894499196438477453 88870835437198664429045)
                    ·
                      rfl

theorem cell22_259613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 1, 5, 3].length) (baseStart_259613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259613 prefixEnd_259613 := by exact prefixLift 259613
  have htrace : WordTrace (prefixWord ++ tailWord_259613) baseStart_259613 baseEnd_259613 := by
    simpa [prefixWord, tailWord_259613, baseEnd_259613] using wordTrace_append hprefix tailTrace_259613
  have hstable : (prefixWord ++ tailWord_259613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259613).length < 2 ^ (prefixWord ++ tailWord_259613).sum := by decide
  have hdescent : baseEnd_259613 < baseStart_259613 := by decide
  rcases family_descends (prefixWord ++ tailWord_259613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259647 : List Nat := [1, 1, 2, 2, 3, 3, 4, 2, 1, 3]
def baseStart_259647 : Nat := 118140960795 + 259647 * 2 ^ 59
def prefixEnd_259647 : Nat := 4983230072969 + 3 ^ 40 * 259647 * 2
def baseEnd_259647 : Nat := 88882474332033909078941

theorem tailTrace_259647 : CollatzResearch.WordTrace tailWord_259647 prefixEnd_259647 88882474332033909078941 := by
  unfold tailWord_259647
  simp only [CollatzResearch.WordTrace]
  refine ⟨9470104090350738022289195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6313402726900492014859463 9470104090350738022289195)
  ·
    refine ⟨14205156135526107033433793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9470104090350738022289195 14205156135526107033433793)
    ·
      refine ⟨10653867101644580275075345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14205156135526107033433793 10653867101644580275075345)
      ·
        refine ⟨7990400326233435206306509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10653867101644580275075345 7990400326233435206306509)
        ·
          refine ⟨2996400122337538202364941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 7990400326233435206306509 2996400122337538202364941)
          ·
            refine ⟨1123650045876576825886853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2996400122337538202364941 1123650045876576825886853)
            ·
              refine ⟨210684383601858154853785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1123650045876576825886853 210684383601858154853785)
              ·
                refine ⟨158013287701393616140339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210684383601858154853785 158013287701393616140339)
                ·
                  refine ⟨237019931552090424210509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158013287701393616140339 237019931552090424210509)
                  ·
                    refine ⟨88882474332033909078941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 237019931552090424210509 88882474332033909078941)
                    ·
                      rfl

theorem cell22_259647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 3, 4, 2, 1, 3].length) (baseStart_259647 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259647 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259647 prefixEnd_259647 := by exact prefixLift 259647
  have htrace : WordTrace (prefixWord ++ tailWord_259647) baseStart_259647 baseEnd_259647 := by
    simpa [prefixWord, tailWord_259647, baseEnd_259647] using wordTrace_append hprefix tailTrace_259647
  have hstable : (prefixWord ++ tailWord_259647).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259647).length < 2 ^ (prefixWord ++ tailWord_259647).sum := by decide
  have hdescent : baseEnd_259647 < baseStart_259647 := by decide
  rcases family_descends (prefixWord ++ tailWord_259647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259671 : List Nat := [1, 1, 3, 2, 2, 3, 1, 1, 8]
def baseStart_259671 : Nat := 118140960795 + 259671 * 2 ^ 59
def prefixEnd_259671 : Nat := 4983230072969 + 3 ^ 40 * 259671 * 2
def baseEnd_259671 : Nat := 29630230007501948826289

theorem tailTrace_259671 : CollatzResearch.WordTrace tailWord_259671 prefixEnd_259671 29630230007501948826289 := by
  unfold tailWord_259671
  simp only [CollatzResearch.WordTrace]
  refine ⟨9470979442263790121162867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6313986294842526747441911 9470979442263790121162867)
  ·
    refine ⟨14206469163395685181744301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9470979442263790121162867 14206469163395685181744301)
    ·
      refine ⟨5327425936273381943154113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 14206469163395685181744301 5327425936273381943154113)
      ·
        refine ⟨3995569452205036457365585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5327425936273381943154113 3995569452205036457365585)
        ·
          refine ⟨2996677089153777343024189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3995569452205036457365585 2996677089153777343024189)
          ·
            refine ⟨1123753908432666503634071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2996677089153777343024189 1123753908432666503634071)
            ·
              refine ⟨1685630862648999755451107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1123753908432666503634071 1685630862648999755451107)
              ·
                refine ⟨2528446293973499633176661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1685630862648999755451107 2528446293973499633176661)
                ·
                  refine ⟨29630230007501948826289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 2528446293973499633176661 29630230007501948826289)
                  ·
                    rfl

theorem cell22_259671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 8].length) (baseStart_259671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259671 prefixEnd_259671 := by exact prefixLift 259671
  have htrace : WordTrace (prefixWord ++ tailWord_259671) baseStart_259671 baseEnd_259671 := by
    simpa [prefixWord, tailWord_259671, baseEnd_259671] using wordTrace_append hprefix tailTrace_259671
  have hstable : (prefixWord ++ tailWord_259671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259671).length < 2 ^ (prefixWord ++ tailWord_259671).sum := by decide
  have hdescent : baseEnd_259671 < baseStart_259671 := by decide
  rcases family_descends (prefixWord ++ tailWord_259671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259690 : List Nat := [3, 1, 3, 2, 1, 3, 1, 3, 1, 4]
def baseStart_259690 : Nat := 118140960795 + 259690 * 2 ^ 59
def prefixEnd_259690 : Nat := 4983230072969 + 3 ^ 40 * 259690 * 2
def baseEnd_259690 : Nat := 88897194110796130253809

theorem tailTrace_259690 : CollatzResearch.WordTrace tailWord_259690 prefixEnd_259690 88897194110796130253809 := by
  unfold tailWord_259690
  simp only [CollatzResearch.WordTrace]
  refine ⟨2367918107298739091526131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6314448286129970910736349 2367918107298739091526131)
  ·
    refine ⟨3551877160948108637289197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2367918107298739091526131 3551877160948108637289197)
    ·
      refine ⟨1331953935355540738983449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3551877160948108637289197 1331953935355540738983449)
      ·
        refine ⟨998965451516655554237587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1331953935355540738983449 998965451516655554237587)
        ·
          refine ⟨1498448177274983331356381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 998965451516655554237587 1498448177274983331356381)
          ·
            refine ⟨561918066478118749258643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1498448177274983331356381 561918066478118749258643)
            ·
              refine ⟨842877099717178123887965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 561918066478118749258643 842877099717178123887965)
              ·
                refine ⟨316078912393941796457987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 842877099717178123887965 316078912393941796457987)
                ·
                  refine ⟨474118368590912694686981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316078912393941796457987 474118368590912694686981)
                  ·
                    refine ⟨88897194110796130253809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 474118368590912694686981 88897194110796130253809)
                    ·
                      rfl

theorem cell22_259690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 3, 1, 4].length) (baseStart_259690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259690 prefixEnd_259690 := by exact prefixLift 259690
  have htrace : WordTrace (prefixWord ++ tailWord_259690) baseStart_259690 baseEnd_259690 := by
    simpa [prefixWord, tailWord_259690, baseEnd_259690] using wordTrace_append hprefix tailTrace_259690
  have hstable : (prefixWord ++ tailWord_259690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259690).length < 2 ^ (prefixWord ++ tailWord_259690).sum := by decide
  have hdescent : baseEnd_259690 < baseStart_259690 := by decide
  rcases family_descends (prefixWord ++ tailWord_259690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259816 : List Nat := [2, 1, 4, 1, 3, 3, 2, 2, 1, 3]
def baseStart_259816 : Nat := 118140960795 + 259816 * 2 ^ 59
def prefixEnd_259816 : Nat := 4983230072969 + 3 ^ 40 * 259816 * 2
def baseEnd_259816 : Nat := 88940326485773801603423

theorem tailTrace_259816 : CollatzResearch.WordTrace tailWord_259816 prefixEnd_259816 88940326485773801603423 := by
  unfold tailWord_259816
  simp only [CollatzResearch.WordTrace]
  refine ⟨4738134013369239942595651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6317512017825653256794201 4738134013369239942595651)
  ·
    refine ⟨7107201020053859913893477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4738134013369239942595651 7107201020053859913893477)
    ·
      refine ⟨1332600191260098733855027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7107201020053859913893477 1332600191260098733855027)
      ·
        refine ⟨1998900286890148100782541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1332600191260098733855027 1998900286890148100782541)
        ·
          refine ⟨749587607583805537793453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1998900286890148100782541 749587607583805537793453)
          ·
            refine ⟨281095352843927076672545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 749587607583805537793453 281095352843927076672545)
            ·
              refine ⟨210821514632945307504409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 281095352843927076672545 210821514632945307504409)
              ·
                refine ⟨158116135974708980628307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 210821514632945307504409 158116135974708980628307)
                ·
                  refine ⟨237174203962063470942461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 158116135974708980628307 237174203962063470942461)
                  ·
                    refine ⟨88940326485773801603423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 237174203962063470942461 88940326485773801603423)
                    ·
                      rfl

theorem cell22_259816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 3, 2, 2, 1, 3].length) (baseStart_259816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259816 prefixEnd_259816 := by exact prefixLift 259816
  have htrace : WordTrace (prefixWord ++ tailWord_259816) baseStart_259816 baseEnd_259816 := by
    simpa [prefixWord, tailWord_259816, baseEnd_259816] using wordTrace_append hprefix tailTrace_259816
  have hstable : (prefixWord ++ tailWord_259816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259816).length < 2 ^ (prefixWord ++ tailWord_259816).sum := by decide
  have hdescent : baseEnd_259816 < baseStart_259816 := by decide
  rcases family_descends (prefixWord ++ tailWord_259816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259823 : List Nat := [1, 1, 2, 1, 5, 1, 2, 3, 6]
def baseStart_259823 : Nat := 118140960795 + 259823 * 2 ^ 59
def prefixEnd_259823 : Nat := 4983230072969 + 3 ^ 40 * 259823 * 2
def baseEnd_259823 : Nat := 29647574242942705559467

theorem tailTrace_259823 : CollatzResearch.WordTrace tailWord_259823 prefixEnd_259823 29647574242942705559467 := by
  unfold tailWord_259823
  simp only [CollatzResearch.WordTrace]
  refine ⟨9476523337713120080696123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6317682225142080053797415 9476523337713120080696123)
  ·
    refine ⟨14214785006569680121044185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9476523337713120080696123 14214785006569680121044185)
    ·
      refine ⟨10661088754927260090783139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14214785006569680121044185 10661088754927260090783139)
      ·
        refine ⟨15991633132390890136174709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10661088754927260090783139 15991633132390890136174709)
        ·
          refine ⟨1499215606161645950266379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 15991633132390890136174709 1499215606161645950266379)
          ·
            refine ⟨2248823409242468925399569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1499215606161645950266379 2248823409242468925399569)
            ·
              refine ⟨1686617556931851694049677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2248823409242468925399569 1686617556931851694049677)
              ·
                refine ⟨632481583849444385268629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1686617556931851694049677 632481583849444385268629)
                ·
                  refine ⟨29647574242942705559467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 632481583849444385268629 29647574242942705559467)
                  ·
                    rfl

theorem cell22_259823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 6].length) (baseStart_259823 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259823 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259823 prefixEnd_259823 := by exact prefixLift 259823
  have htrace : WordTrace (prefixWord ++ tailWord_259823) baseStart_259823 baseEnd_259823 := by
    simpa [prefixWord, tailWord_259823, baseEnd_259823] using wordTrace_append hprefix tailTrace_259823
  have hstable : (prefixWord ++ tailWord_259823).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259823).length < 2 ^ (prefixWord ++ tailWord_259823).sum := by decide
  have hdescent : baseEnd_259823 < baseStart_259823 := by decide
  rcases family_descends (prefixWord ++ tailWord_259823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259842 : List Nat := [3, 4, 1, 1, 1, 1, 2, 4, 1, 4]
def baseStart_259842 : Nat := 118140960795 + 259842 * 2 ^ 59
def prefixEnd_259842 : Nat := 4983230072969 + 3 ^ 40 * 259842 * 2
def baseEnd_259842 : Nat := 88949226817118400453343

theorem tailTrace_259842 : CollatzResearch.WordTrace tailWord_259842 prefixEnd_259842 88949226817118400453343 := by
  unfold tailWord_259842
  simp only [CollatzResearch.WordTrace]
  refine ⟨2369304081161071581409445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 6318144216429524217091853 2369304081161071581409445)
  ·
    refine ⟨444244515217700921514271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 2369304081161071581409445 444244515217700921514271)
    ·
      refine ⟨666366772826551382271407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 444244515217700921514271 666366772826551382271407)
      ·
        refine ⟨999550159239827073407111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 666366772826551382271407 999550159239827073407111)
        ·
          refine ⟨1499325238859740610110667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 999550159239827073407111 1499325238859740610110667)
          ·
            refine ⟨2248987858289610915166001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1499325238859740610110667 2248987858289610915166001)
            ·
              refine ⟨1686740893717208186374501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2248987858289610915166001 1686740893717208186374501)
              ·
                refine ⟨316263917571976534945219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1686740893717208186374501 316263917571976534945219)
                ·
                  refine ⟨474395876357964802417829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 316263917571976534945219 474395876357964802417829)
                  ·
                    refine ⟨88949226817118400453343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 474395876357964802417829 88949226817118400453343)
                    ·
                      rfl

theorem cell22_259842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_259842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259842 prefixEnd_259842 := by exact prefixLift 259842
  have htrace : WordTrace (prefixWord ++ tailWord_259842) baseStart_259842 baseEnd_259842 := by
    simpa [prefixWord, tailWord_259842, baseEnd_259842] using wordTrace_append hprefix tailTrace_259842
  have hstable : (prefixWord ++ tailWord_259842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259842).length < 2 ^ (prefixWord ++ tailWord_259842).sum := by decide
  have hdescent : baseEnd_259842 < baseStart_259842 := by decide
  rcases family_descends (prefixWord ++ tailWord_259842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259868 : List Nat := [2, 2, 3, 1, 1, 2, 11]
def baseStart_259868 : Nat := 118140960795 + 259868 * 2 ^ 59
def prefixEnd_259868 : Nat := 4983230072969 + 3 ^ 40 * 259868 * 2
def baseEnd_259868 : Nat := 3294745449943074048269

theorem tailTrace_259868 : CollatzResearch.WordTrace tailWord_259868 prefixEnd_259868 3294745449943074048269 := by
  unfold tailWord_259868
  simp only [CollatzResearch.WordTrace]
  refine ⟨4739082311275046383042129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 6318776415033395177389505 4739082311275046383042129)
  ·
    refine ⟨3554311733456284787281597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4739082311275046383042129 3554311733456284787281597)
    ·
      refine ⟨1332866900046106795230599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 3554311733456284787281597 1332866900046106795230599)
      ·
        refine ⟨1999300350069160192845899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1332866900046106795230599 1999300350069160192845899)
        ·
          refine ⟨2998950525103740289268849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1999300350069160192845899 2998950525103740289268849)
          ·
            refine ⟨2249212893827805216951637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2998950525103740289268849 2249212893827805216951637)
            ·
              refine ⟨3294745449943074048269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 2249212893827805216951637 3294745449943074048269)
              ·
                rfl

theorem cell22_259868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 11].length) (baseStart_259868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259868 prefixEnd_259868 := by exact prefixLift 259868
  have htrace : WordTrace (prefixWord ++ tailWord_259868) baseStart_259868 baseEnd_259868 := by
    simpa [prefixWord, tailWord_259868, baseEnd_259868] using wordTrace_append hprefix tailTrace_259868
  have hstable : (prefixWord ++ tailWord_259868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259868).length < 2 ^ (prefixWord ++ tailWord_259868).sum := by decide
  have hdescent : baseEnd_259868 < baseStart_259868 := by decide
  rcases family_descends (prefixWord ++ tailWord_259868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259889 : List Nat := [1, 2, 2, 3, 2, 3, 3, 1, 2, 3]
def baseStart_259889 : Nat := 118140960795 + 259889 * 2 ^ 59
def prefixEnd_259889 : Nat := 4983230072969 + 3 ^ 40 * 259889 * 2
def baseEnd_259889 : Nat := 88965315877625944528199

theorem tailTrace_259889 : CollatzResearch.WordTrace tailWord_259889 prefixEnd_259889 88965315877625944528199 := by
  unfold tailWord_259889
  simp only [CollatzResearch.WordTrace]
  refine ⟨9478930555474013352598721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 6319287036982675568399147 9478930555474013352598721)
  ·
    refine ⟨7109197916605510014449041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 9478930555474013352598721 7109197916605510014449041)
    ·
      refine ⟨5331898437454132510836781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7109197916605510014449041 5331898437454132510836781)
      ·
        refine ⟨1999461914045299691563793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5331898437454132510836781 1999461914045299691563793)
        ·
          refine ⟨1499596435533974768672845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1999461914045299691563793 1499596435533974768672845)
          ·
            refine ⟨562348663325240538252317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1499596435533974768672845 562348663325240538252317)
            ·
              refine ⟨210880748746965201844619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 562348663325240538252317 210880748746965201844619)
              ·
                refine ⟨316321123120447802766929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 210880748746965201844619 316321123120447802766929)
                ·
                  refine ⟨237240842340335852075197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 316321123120447802766929 237240842340335852075197)
                  ·
                    refine ⟨88965315877625944528199, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 237240842340335852075197 88965315877625944528199)
                    ·
                      rfl

theorem cell22_259889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 3, 1, 2, 3].length) (baseStart_259889 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259889 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259889 prefixEnd_259889 := by exact prefixLift 259889
  have htrace : WordTrace (prefixWord ++ tailWord_259889) baseStart_259889 baseEnd_259889 := by
    simpa [prefixWord, tailWord_259889, baseEnd_259889] using wordTrace_append hprefix tailTrace_259889
  have hstable : (prefixWord ++ tailWord_259889).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259889).length < 2 ^ (prefixWord ++ tailWord_259889).sum := by decide
  have hdescent : baseEnd_259889 < baseStart_259889 := by decide
  rcases family_descends (prefixWord ++ tailWord_259889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_259902 : List Nat := [4, 2, 1, 2, 2, 1, 4, 6]
def baseStart_259902 : Nat := 118140960795 + 259902 * 2 ^ 59
def prefixEnd_259902 : Nat := 4983230072969 + 3 ^ 40 * 259902 * 2
def baseEnd_259902 : Nat := 9885529560366471550351

theorem tailTrace_259902 : CollatzResearch.WordTrace tailWord_259902 prefixEnd_259902 9885529560366471550351 := by
  unfold tailWord_259902
  simp only [CollatzResearch.WordTrace]
  refine ⟨1184925588053364571602745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 6319603136284611048547973 1184925588053364571602745)
  ·
    refine ⟨888694191040023428702059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1184925588053364571602745 888694191040023428702059)
    ·
      refine ⟨1333041286560035143053089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 888694191040023428702059 1333041286560035143053089)
      ·
        refine ⟨999780964920026357289817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1333041286560035143053089 999780964920026357289817)
        ·
          refine ⟨749835723690019767967363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 999780964920026357289817 749835723690019767967363)
          ·
            refine ⟨1124753585535029651951045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 749835723690019767967363 1124753585535029651951045)
            ·
              refine ⟨210891297287818059740821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1124753585535029651951045 210891297287818059740821)
              ·
                refine ⟨9885529560366471550351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 210891297287818059740821 9885529560366471550351)
                ·
                  rfl

theorem cell22_259902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 4, 6].length) (baseStart_259902 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_259902 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_259902 prefixEnd_259902 := by exact prefixLift 259902
  have htrace : WordTrace (prefixWord ++ tailWord_259902) baseStart_259902 baseEnd_259902 := by
    simpa [prefixWord, tailWord_259902, baseEnd_259902] using wordTrace_append hprefix tailTrace_259902
  have hstable : (prefixWord ++ tailWord_259902).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_259902).length < 2 ^ (prefixWord ++ tailWord_259902).sum := by decide
  have hdescent : baseEnd_259902 < baseStart_259902 := by decide
  rcases family_descends (prefixWord ++ tailWord_259902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
