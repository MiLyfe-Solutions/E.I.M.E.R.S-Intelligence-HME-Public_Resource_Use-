import V185TrunkScan23Chunk0847

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5018580 : List Nat := [2, 4, 1, 2, 1, 4, 1, 2, 2, 4]
def baseStart_5018580 : Nat := 118140960795 + 5018580 * 2 ^ 59
def prefixEnd_5018580 : Nat := 4983230072969 + 3 ^ 40 * 5018580 * 2
def baseEnd_5018580 : Nat := 858981247680360005456659

theorem tailTrace_5018580 : CollatzResearch.WordTrace tailWord_5018580 prefixEnd_5018580 858981247680360005456659 := by
  unfold tailWord_5018580
  simp only [CollatzResearch.WordTrace]
  refine ⟨91521325079274620035738597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122028433439032826714318129 91521325079274620035738597)
  ·
    refine ⟨17160248452363991256700987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91521325079274620035738597 17160248452363991256700987)
    ·
      refine ⟨25740372678545986885051481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17160248452363991256700987 25740372678545986885051481)
      ·
        refine ⟨19305279508909490163788611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25740372678545986885051481 19305279508909490163788611)
        ·
          refine ⟨28957919263364235245682917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19305279508909490163788611 28957919263364235245682917)
          ·
            refine ⟨5429609861880794108565547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28957919263364235245682917 5429609861880794108565547)
            ·
              refine ⟨8144414792821191162848321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5429609861880794108565547 8144414792821191162848321)
              ·
                refine ⟨6108311094615893372136241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8144414792821191162848321 6108311094615893372136241)
                ·
                  refine ⟨4581233320961920029102181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6108311094615893372136241 4581233320961920029102181)
                  ·
                    refine ⟨858981247680360005456659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4581233320961920029102181 858981247680360005456659)
                    ·
                      rfl

theorem cell23_5018580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 1, 2, 2, 4].length) (baseStart_5018580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018580 prefixEnd_5018580 := by exact prefixLift 5018580
  have htrace : WordTrace (prefixWord ++ tailWord_5018580) baseStart_5018580 baseEnd_5018580 := by
    simpa [prefixWord, tailWord_5018580, baseEnd_5018580] using wordTrace_append hprefix tailTrace_5018580
  have hstable : (prefixWord ++ tailWord_5018580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018580).length < 2 ^ (prefixWord ++ tailWord_5018580).sum := by decide
  have hdescent : baseEnd_5018580 < baseStart_5018580 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018596 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 2, 7, 2]
def baseStart_5018596 : Nat := 118140960795 + 5018596 * 2 ^ 59
def prefixEnd_5018596 : Nat := 4983230072969 + 3 ^ 40 * 5018596 * 2
def baseEnd_5018596 : Nat := 2576951958731551953769903

theorem tailTrace_5018596 : CollatzResearch.WordTrace tailWord_5018596 prefixEnd_5018596 2576951958731551953769903 := by
  unfold tailWord_5018596
  simp only [CollatzResearch.WordTrace]
  refine ⟨91521616863245637402029821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122028822484327516536039761 91521616863245637402029821)
  ·
    refine ⟨34320606323717114025761183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91521616863245637402029821 34320606323717114025761183)
    ·
      refine ⟨51480909485575671038641775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34320606323717114025761183 51480909485575671038641775)
      ·
        refine ⟨77221364228363506557962663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51480909485575671038641775 77221364228363506557962663)
        ·
          refine ⟨115832046342545259836943995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77221364228363506557962663 115832046342545259836943995)
          ·
            refine ⟨173748069513817889755415993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115832046342545259836943995 173748069513817889755415993)
            ·
              refine ⟨130311052135363417316561995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173748069513817889755415993 130311052135363417316561995)
              ·
                refine ⟨195466578203045125974842993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130311052135363417316561995 195466578203045125974842993)
                ·
                  refine ⟨146599933652283844481132245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195466578203045125974842993 146599933652283844481132245)
                  ·
                    refine ⟨3435935944975402605026537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 146599933652283844481132245 3435935944975402605026537)
                    ·
                      refine ⟨2576951958731551953769903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3435935944975402605026537 2576951958731551953769903)
                      ·
                        rfl

theorem cell23_5018596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 2, 7, 2].length) (baseStart_5018596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018596 prefixEnd_5018596 := by exact prefixLift 5018596
  have htrace : WordTrace (prefixWord ++ tailWord_5018596) baseStart_5018596 baseEnd_5018596 := by
    simpa [prefixWord, tailWord_5018596, baseEnd_5018596] using wordTrace_append hprefix tailTrace_5018596
  have hstable : (prefixWord ++ tailWord_5018596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018596).length < 2 ^ (prefixWord ++ tailWord_5018596).sum := by decide
  have hdescent : baseEnd_5018596 < baseStart_5018596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018597 : List Nat := [1, 3, 1, 6, 1, 1, 3, 1, 2, 4]
def baseStart_5018597 : Nat := 118140960795 + 5018597 * 2 ^ 59
def prefixEnd_5018597 : Nat := 4983230072969 + 3 ^ 40 * 5018597 * 2
def baseEnd_5018597 : Nat := 858984157404068816619133

theorem tailTrace_5018597 : CollatzResearch.WordTrace tailWord_5018597 prefixEnd_5018597 858984157404068816619133 := by
  unfold tailWord_5018597
  simp only [CollatzResearch.WordTrace]
  refine ⟨183043270199487651974846045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122028846799658434649897363 183043270199487651974846045)
  ·
    refine ⟨68641226324807869490567267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183043270199487651974846045 68641226324807869490567267)
    ·
      refine ⟨102961839487211804235850901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68641226324807869490567267 102961839487211804235850901)
      ·
        refine ⟨4826336225963053323555511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 102961839487211804235850901 4826336225963053323555511)
        ·
          refine ⟨7239504338944579985333267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4826336225963053323555511 7239504338944579985333267)
          ·
            refine ⟨10859256508416869977999901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7239504338944579985333267 10859256508416869977999901)
            ·
              refine ⟨4072221190656326241749963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10859256508416869977999901 4072221190656326241749963)
              ·
                refine ⟨6108331785984489362624945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4072221190656326241749963 6108331785984489362624945)
                ·
                  refine ⟨4581248839488367021968709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6108331785984489362624945 4581248839488367021968709)
                  ·
                    refine ⟨858984157404068816619133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4581248839488367021968709 858984157404068816619133)
                    ·
                      rfl

theorem cell23_5018597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 1, 1, 3, 1, 2, 4].length) (baseStart_5018597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018597 prefixEnd_5018597 := by exact prefixLift 5018597
  have htrace : WordTrace (prefixWord ++ tailWord_5018597) baseStart_5018597 baseEnd_5018597 := by
    simpa [prefixWord, tailWord_5018597, baseEnd_5018597] using wordTrace_append hprefix tailTrace_5018597
  have hstable : (prefixWord ++ tailWord_5018597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018597).length < 2 ^ (prefixWord ++ tailWord_5018597).sum := by decide
  have hdescent : baseEnd_5018597 < baseStart_5018597 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018610 : List Nat := [3, 2, 1, 5, 1, 2, 2, 7]
def baseStart_5018610 : Nat := 118140960795 + 5018610 * 2 ^ 59
def prefixEnd_5018610 : Nat := 4983230072969 + 3 ^ 40 * 5018610 * 2
def baseEnd_5018610 : Nat := 95442931387433885147957

theorem tailTrace_5018610 : CollatzResearch.WordTrace tailWord_5018610 prefixEnd_5018610 95442931387433885147957 := by
  unfold tailWord_5018610
  simp only [CollatzResearch.WordTrace]
  refine ⟨45760936087110138798767321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122029162898960370130046189 45760936087110138798767321)
  ·
    refine ⟨34320702065332604099075491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45760936087110138798767321 34320702065332604099075491)
    ·
      refine ⟨51481053097998906148613237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34320702065332604099075491 51481053097998906148613237)
      ·
        refine ⟨4826348727937397451432491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51481053097998906148613237 4826348727937397451432491)
        ·
          refine ⟨7239523091906096177148737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4826348727937397451432491 7239523091906096177148737)
          ·
            refine ⟨5429642318929572132861553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7239523091906096177148737 5429642318929572132861553)
            ·
              refine ⟨4072231739197179099646165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5429642318929572132861553 4072231739197179099646165)
              ·
                refine ⟨95442931387433885147957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4072231739197179099646165 95442931387433885147957)
                ·
                  rfl

theorem cell23_5018610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 2, 7].length) (baseStart_5018610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018610 prefixEnd_5018610 := by exact prefixLift 5018610
  have htrace : WordTrace (prefixWord ++ tailWord_5018610) baseStart_5018610 baseEnd_5018610 := by
    simpa [prefixWord, tailWord_5018610, baseEnd_5018610] using wordTrace_append hprefix tailTrace_5018610
  have hstable : (prefixWord ++ tailWord_5018610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018610).length < 2 ^ (prefixWord ++ tailWord_5018610).sum := by decide
  have hdescent : baseEnd_5018610 < baseStart_5018610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018639 : List Nat := [1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 4]
def baseStart_5018639 : Nat := 118140960795 + 5018639 * 2 ^ 59
def prefixEnd_5018639 : Nat := 4983230072969 + 3 ^ 40 * 5018639 * 2
def baseEnd_5018639 : Nat := 2576974038399695285532205

theorem tailTrace_5018639 : CollatzResearch.WordTrace tailWord_5018639 prefixEnd_5018639 2576974038399695285532205 := by
  unfold tailWord_5018639
  simp only [CollatzResearch.WordTrace]
  refine ⟨183044802065335493147874971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122029868043556995431916647 183044802065335493147874971)
  ·
    refine ⟨274567203098003239721812457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183044802065335493147874971 274567203098003239721812457)
    ·
      refine ⟨205925402323502429791359343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274567203098003239721812457 205925402323502429791359343)
      ·
        refine ⟨308888103485253644687039015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205925402323502429791359343 308888103485253644687039015)
        ·
          refine ⟨463332155227880467030558523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308888103485253644687039015 463332155227880467030558523)
          ·
            refine ⟨694998232841820700545837785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463332155227880467030558523 694998232841820700545837785)
            ·
              refine ⟨521248674631365525409378339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 694998232841820700545837785 521248674631365525409378339)
              ·
                refine ⟨781873011947048288114067509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 521248674631365525409378339 781873011947048288114067509)
                ·
                  refine ⟨73300594870035777010693829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 781873011947048288114067509 73300594870035777010693829)
                  ·
                    refine ⟨13743861538131708189505093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73300594870035777010693829 13743861538131708189505093)
                    ·
                      refine ⟨2576974038399695285532205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13743861538131708189505093 2576974038399695285532205)
                      ·
                        rfl

theorem cell23_5018639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 1, 5, 4, 4].length) (baseStart_5018639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018639 prefixEnd_5018639 := by exact prefixLift 5018639
  have htrace : WordTrace (prefixWord ++ tailWord_5018639) baseStart_5018639 baseEnd_5018639 := by
    simpa [prefixWord, tailWord_5018639, baseEnd_5018639] using wordTrace_append hprefix tailTrace_5018639
  have hstable : (prefixWord ++ tailWord_5018639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018639).length < 2 ^ (prefixWord ++ tailWord_5018639).sum := by decide
  have hdescent : baseEnd_5018639 < baseStart_5018639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018663 : List Nat := [1, 1, 7, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_5018663 : Nat := 118140960795 + 5018663 * 2 ^ 59
def prefixEnd_5018663 : Nat := 4983230072969 + 3 ^ 40 * 5018663 * 2
def baseEnd_5018663 : Nat := 2576986361935403191632095

theorem tailTrace_5018663 : CollatzResearch.WordTrace tailWord_5018663 prefixEnd_5018663 2576986361935403191632095 := by
  unfold tailWord_5018663
  simp only [CollatzResearch.WordTrace]
  refine ⟨183045677417248545246748643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122030451611499030164499095 183045677417248545246748643)
  ·
    refine ⟨274568516125872817870122965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183045677417248545246748643 274568516125872817870122965)
    ·
      refine ⟨6435199596700144168831007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 274568516125872817870122965 6435199596700144168831007)
      ·
        refine ⟨9652799395050216253246511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6435199596700144168831007 9652799395050216253246511)
        ·
          refine ⟨14479199092575324379869767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9652799395050216253246511 14479199092575324379869767)
          ·
            refine ⟨21718798638862986569804651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14479199092575324379869767 21718798638862986569804651)
            ·
              refine ⟨32578197958294479854706977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21718798638862986569804651 32578197958294479854706977)
              ·
                refine ⟨24433648468720859891030233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32578197958294479854706977 24433648468720859891030233)
                ·
                  refine ⟨18325236351540644918272675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24433648468720859891030233 18325236351540644918272675)
                  ·
                    refine ⟨27487854527310967377409013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18325236351540644918272675 27487854527310967377409013)
                    ·
                      refine ⟨2576986361935403191632095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27487854527310967377409013 2576986361935403191632095)
                      ·
                        rfl

theorem cell23_5018663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_5018663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018663 prefixEnd_5018663 := by exact prefixLift 5018663
  have htrace : WordTrace (prefixWord ++ tailWord_5018663) baseStart_5018663 baseEnd_5018663 := by
    simpa [prefixWord, tailWord_5018663, baseEnd_5018663] using wordTrace_append hprefix tailTrace_5018663
  have hstable : (prefixWord ++ tailWord_5018663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018663).length < 2 ^ (prefixWord ++ tailWord_5018663).sum := by decide
  have hdescent : baseEnd_5018663 < baseStart_5018663 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018694 : List Nat := [6, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2]
def baseStart_5018694 : Nat := 118140960795 + 5018694 * 2 ^ 59
def prefixEnd_5018694 : Nat := 4983230072969 + 3 ^ 40 * 5018694 * 2
def baseEnd_5018694 : Nat := 2577002279835692570344453

theorem tailTrace_5018694 : CollatzResearch.WordTrace tailWord_5018694 prefixEnd_5018694 2577002279835692570344453 := by
  unfold tailWord_5018694
  simp only [CollatzResearch.WordTrace]
  refine ⟨5720212752504257423160223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 122031205386757491694084757 5720212752504257423160223)
  ·
    refine ⟨8580319128756386134740335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5720212752504257423160223 8580319128756386134740335)
    ·
      refine ⟨12870478693134579202110503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8580319128756386134740335 12870478693134579202110503)
      ·
        refine ⟨19305718039701868803165755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12870478693134579202110503 19305718039701868803165755)
        ·
          refine ⟨28958577059552803204748633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19305718039701868803165755 28958577059552803204748633)
          ·
            refine ⟨21718932794664602403561475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28958577059552803204748633 21718932794664602403561475)
            ·
              refine ⟨32578399191996903605342213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21718932794664602403561475 32578399191996903605342213)
              ·
                refine ⟨6108449848499419426001665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32578399191996903605342213 6108449848499419426001665)
                ·
                  refine ⟨4581337386374564569501249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6108449848499419426001665 4581337386374564569501249)
                  ·
                    refine ⟨3436003039780923427125937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4581337386374564569501249 3436003039780923427125937)
                    ·
                      refine ⟨2577002279835692570344453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3436003039780923427125937 2577002279835692570344453)
                      ·
                        rfl

theorem cell23_5018694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 4, 2, 2, 2].length) (baseStart_5018694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018694 prefixEnd_5018694 := by exact prefixLift 5018694
  have htrace : WordTrace (prefixWord ++ tailWord_5018694) baseStart_5018694 baseEnd_5018694 := by
    simpa [prefixWord, tailWord_5018694, baseEnd_5018694] using wordTrace_append hprefix tailTrace_5018694
  have hstable : (prefixWord ++ tailWord_5018694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018694).length < 2 ^ (prefixWord ++ tailWord_5018694).sum := by decide
  have hdescent : baseEnd_5018694 < baseStart_5018694 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018696 : List Nat := [2, 1, 3, 1, 1, 1, 3, 4, 2, 5]
def baseStart_5018696 : Nat := 118140960795 + 5018696 * 2 ^ 59
def prefixEnd_5018696 : Nat := 4983230072969 + 3 ^ 40 * 5018696 * 2
def baseEnd_5018696 : Nat := 859001102265667187506481

theorem tailTrace_5018696 : CollatzResearch.WordTrace tailWord_5018696 prefixEnd_5018696 859001102265667187506481 := by
  unfold tailWord_5018696
  simp only [CollatzResearch.WordTrace]
  refine ⟨91523440513064495941349971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122031254017419327921799961 91523440513064495941349971)
  ·
    refine ⟨137285160769596743912024957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91523440513064495941349971 137285160769596743912024957)
    ·
      refine ⟨51481935288598778967009359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137285160769596743912024957 51481935288598778967009359)
      ·
        refine ⟨77222902932898168450514039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51481935288598778967009359 77222902932898168450514039)
        ·
          refine ⟨115834354399347252675771059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77222902932898168450514039 115834354399347252675771059)
          ·
            refine ⟨173751531599020879013656589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115834354399347252675771059 173751531599020879013656589)
            ·
              refine ⟨65156824349632829630121221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173751531599020879013656589 65156824349632829630121221)
              ·
                refine ⟨12216904565556155555647729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65156824349632829630121221 12216904565556155555647729)
                ·
                  refine ⟨9162678424167116666735797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12216904565556155555647729 9162678424167116666735797)
                  ·
                    refine ⟨859001102265667187506481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9162678424167116666735797 859001102265667187506481)
                    ·
                      rfl

theorem cell23_5018696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 3, 4, 2, 5].length) (baseStart_5018696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018696 prefixEnd_5018696 := by exact prefixLift 5018696
  have htrace : WordTrace (prefixWord ++ tailWord_5018696) baseStart_5018696 baseEnd_5018696 := by
    simpa [prefixWord, tailWord_5018696, baseEnd_5018696] using wordTrace_append hprefix tailTrace_5018696
  have hstable : (prefixWord ++ tailWord_5018696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018696).length < 2 ^ (prefixWord ++ tailWord_5018696).sum := by decide
  have hdescent : baseEnd_5018696 < baseStart_5018696 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018699 : List Nat := [1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 8]
def baseStart_5018699 : Nat := 118140960795 + 5018699 * 2 ^ 59
def prefixEnd_5018699 : Nat := 4983230072969 + 3 ^ 40 * 5018699 * 2
def baseEnd_5018699 : Nat := 2577004847238965050781929

theorem tailTrace_5018699 : CollatzResearch.WordTrace tailWord_5018699 prefixEnd_5018699 2577004847238965050781929 := by
  unfold tailWord_5018699
  simp only [CollatzResearch.WordTrace]
  refine ⟨183046990445118123395059151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122031326963412082263372767 183046990445118123395059151)
  ·
    refine ⟨274570485667677185092588727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183046990445118123395059151 274570485667677185092588727)
    ·
      refine ⟨411855728501515777638883091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274570485667677185092588727 411855728501515777638883091)
      ·
        refine ⟨617783592752273666458324637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 411855728501515777638883091 617783592752273666458324637)
        ·
          refine ⟨231668847282102624921871739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 617783592752273666458324637 231668847282102624921871739)
          ·
            refine ⟨347503270923153937382807609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231668847282102624921871739 347503270923153937382807609)
            ·
              refine ⟨260627453192365453037105707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 347503270923153937382807609 260627453192365453037105707)
              ·
                refine ⟨390941179788548179555658561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260627453192365453037105707 390941179788548179555658561)
                ·
                  refine ⟨293205884841411134666743921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 390941179788548179555658561 293205884841411134666743921)
                  ·
                    refine ⟨219904413631058351000057941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 293205884841411134666743921 219904413631058351000057941)
                    ·
                      refine ⟨2577004847238965050781929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 219904413631058351000057941 2577004847238965050781929)
                      ·
                        rfl

theorem cell23_5018699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 2, 2, 8].length) (baseStart_5018699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018699 prefixEnd_5018699 := by exact prefixLift 5018699
  have htrace : WordTrace (prefixWord ++ tailWord_5018699) baseStart_5018699 baseEnd_5018699 := by
    simpa [prefixWord, tailWord_5018699, baseEnd_5018699] using wordTrace_append hprefix tailTrace_5018699
  have hstable : (prefixWord ++ tailWord_5018699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018699).length < 2 ^ (prefixWord ++ tailWord_5018699).sum := by decide
  have hdescent : baseEnd_5018699 < baseStart_5018699 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018730 : List Nat := [3, 1, 3, 2, 2, 3, 1, 1, 2, 5]
def baseStart_5018730 : Nat := 118140960795 + 5018730 * 2 ^ 59
def prefixEnd_5018730 : Nat := 4983230072969 + 3 ^ 40 * 5018730 * 2
def baseEnd_5018730 : Nat := 859006921713084809831429

theorem tailTrace_5018730 : CollatzResearch.WordTrace tailWord_5018730 prefixEnd_5018730 859006921713084809831429 := by
  unfold tailWord_5018730
  simp only [CollatzResearch.WordTrace]
  refine ⟨45762030277001453922359411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122032080738670543792958429 45762030277001453922359411)
  ·
    refine ⟨68643045415502180883539117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45762030277001453922359411 68643045415502180883539117)
    ·
      refine ⟨25741142030813317831327169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68643045415502180883539117 25741142030813317831327169)
      ·
        refine ⟨19305856523109988373495377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25741142030813317831327169 19305856523109988373495377)
        ·
          refine ⟨14479392392332491280121533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19305856523109988373495377 14479392392332491280121533)
          ·
            refine ⟨5429772147124684230045575, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14479392392332491280121533 5429772147124684230045575)
            ·
              refine ⟨8144658220687026345068363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5429772147124684230045575 8144658220687026345068363)
              ·
                refine ⟨12216987331030539517602545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8144658220687026345068363 12216987331030539517602545)
                ·
                  refine ⟨9162740498272904638201909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12216987331030539517602545 9162740498272904638201909)
                  ·
                    refine ⟨859006921713084809831429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9162740498272904638201909 859006921713084809831429)
                    ·
                      rfl

theorem cell23_5018730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 3, 1, 1, 2, 5].length) (baseStart_5018730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018730 prefixEnd_5018730 := by exact prefixLift 5018730
  have htrace : WordTrace (prefixWord ++ tailWord_5018730) baseStart_5018730 baseEnd_5018730 := by
    simpa [prefixWord, tailWord_5018730, baseEnd_5018730] using wordTrace_append hprefix tailTrace_5018730
  have hstable : (prefixWord ++ tailWord_5018730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018730).length < 2 ^ (prefixWord ++ tailWord_5018730).sum := by decide
  have hdescent : baseEnd_5018730 < baseStart_5018730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018733 : List Nat := [1, 5, 1, 1, 2, 3, 1, 1, 1, 3, 4]
def baseStart_5018733 : Nat := 118140960795 + 5018733 * 2 ^ 59
def prefixEnd_5018733 : Nat := 4983230072969 + 3 ^ 40 * 5018733 * 2
def baseEnd_5018733 : Nat := 2577022305581217917756773

theorem tailTrace_5018733 : CollatzResearch.WordTrace tailWord_5018733 prefixEnd_5018733 2577022305581217917756773 := by
  unfold tailWord_5018733
  simp only [CollatzResearch.WordTrace]
  refine ⟨183048230526994947201796853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122032153684663298134531235 183048230526994947201796853)
  ·
    refine ⟨17160771611905776300168455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 183048230526994947201796853 17160771611905776300168455)
    ·
      refine ⟨25741157417858664450252683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17160771611905776300168455 25741157417858664450252683)
      ·
        refine ⟨38611736126787996675379025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25741157417858664450252683 38611736126787996675379025)
        ·
          refine ⟨28958802095090997506534269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38611736126787996675379025 28958802095090997506534269)
          ·
            refine ⟨10859550785659124064950351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28958802095090997506534269 10859550785659124064950351)
            ·
              refine ⟨16289326178488686097425527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10859550785659124064950351 16289326178488686097425527)
              ·
                refine ⟨24433989267733029146138291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16289326178488686097425527 24433989267733029146138291)
                ·
                  refine ⟨36650983901599543719207437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24433989267733029146138291 36650983901599543719207437)
                  ·
                    refine ⟨13744118963099828894702789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36650983901599543719207437 13744118963099828894702789)
                    ·
                      refine ⟨2577022305581217917756773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13744118963099828894702789 2577022305581217917756773)
                      ·
                        rfl

theorem cell23_5018733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_5018733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018733 prefixEnd_5018733 := by exact prefixLift 5018733
  have htrace : WordTrace (prefixWord ++ tailWord_5018733) baseStart_5018733 baseEnd_5018733 := by
    simpa [prefixWord, tailWord_5018733, baseEnd_5018733] using wordTrace_append hprefix tailTrace_5018733
  have hstable : (prefixWord ++ tailWord_5018733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018733).length < 2 ^ (prefixWord ++ tailWord_5018733).sum := by decide
  have hdescent : baseEnd_5018733 < baseStart_5018733 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018794 : List Nat := [3, 1, 5, 1, 1, 1, 3, 3, 1, 4]
def baseStart_5018794 : Nat := 118140960795 + 5018794 * 2 ^ 59
def prefixEnd_5018794 : Nat := 4983230072969 + 3 ^ 40 * 5018794 * 2
def baseEnd_5018794 : Nat := 859017875967047393031331

theorem tailTrace_5018794 : CollatzResearch.WordTrace tailWord_5018794 prefixEnd_5018794 859017875967047393031331 := by
  unfold tailWord_5018794
  simp only [CollatzResearch.WordTrace]
  refine ⟨45762613844943488654941859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122033636919849303079844957 45762613844943488654941859)
  ·
    refine ⟨68643920767415232982412789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45762613844943488654941859 68643920767415232982412789)
    ·
      refine ⟨6435367571945178092101199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68643920767415232982412789 6435367571945178092101199)
      ·
        refine ⟨9653051357917767138151799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6435367571945178092101199 9653051357917767138151799)
        ·
          refine ⟨14479577036876650707227699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9653051357917767138151799 14479577036876650707227699)
          ·
            refine ⟨21719365555314976060841549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14479577036876650707227699 21719365555314976060841549)
            ·
              refine ⟨8144762083243116022815581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21719365555314976060841549 8144762083243116022815581)
              ·
                refine ⟨3054285781216168508555843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8144762083243116022815581 3054285781216168508555843)
                ·
                  refine ⟨4581428671824252762833765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3054285781216168508555843 4581428671824252762833765)
                  ·
                    refine ⟨859017875967047393031331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4581428671824252762833765 859017875967047393031331)
                    ·
                      rfl

theorem cell23_5018794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 3, 1, 4].length) (baseStart_5018794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018794 prefixEnd_5018794 := by exact prefixLift 5018794
  have htrace : WordTrace (prefixWord ++ tailWord_5018794) baseStart_5018794 baseEnd_5018794 := by
    simpa [prefixWord, tailWord_5018794, baseEnd_5018794] using wordTrace_append hprefix tailTrace_5018794
  have hstable : (prefixWord ++ tailWord_5018794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018794).length < 2 ^ (prefixWord ++ tailWord_5018794).sum := by decide
  have hdescent : baseEnd_5018794 < baseStart_5018794 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018803 : List Nat := [1, 1, 1, 2, 3, 2, 4, 3, 1, 5]
def baseStart_5018803 : Nat := 118140960795 + 5018803 * 2 ^ 59
def prefixEnd_5018803 : Nat := 4983230072969 + 3 ^ 40 * 5018803 * 2
def baseEnd_5018803 : Nat := 859019416409010881293817

theorem tailTrace_5018803 : CollatzResearch.WordTrace tailWord_5018803 prefixEnd_5018803 859019416409010881293817 := by
  unfold tailWord_5018803
  simp only [CollatzResearch.WordTrace]
  refine ⟨183050783636741349156845063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122033855757827566104563375 183050783636741349156845063)
  ·
    refine ⟨274576175455112023735267595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183050783636741349156845063 274576175455112023735267595)
    ·
      refine ⟨411864263182668035602901393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274576175455112023735267595 411864263182668035602901393)
      ·
        refine ⟨308898197387001026702176045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 411864263182668035602901393 308898197387001026702176045)
        ·
          refine ⟨115836824020125385013316017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 308898197387001026702176045 115836824020125385013316017)
          ·
            refine ⟨86877618015094038759987013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115836824020125385013316017 86877618015094038759987013)
            ·
              refine ⟨16289553377830132267497565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86877618015094038759987013 16289553377830132267497565)
              ·
                refine ⟨6108582516686299600311587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16289553377830132267497565 6108582516686299600311587)
                ·
                  refine ⟨9162873775029449400467381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6108582516686299600311587 9162873775029449400467381)
                  ·
                    refine ⟨859019416409010881293817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9162873775029449400467381 859019416409010881293817)
                    ·
                      rfl

theorem cell23_5018803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 4, 3, 1, 5].length) (baseStart_5018803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018803 prefixEnd_5018803 := by exact prefixLift 5018803
  have htrace : WordTrace (prefixWord ++ tailWord_5018803) baseStart_5018803 baseEnd_5018803 := by
    simpa [prefixWord, tailWord_5018803, baseEnd_5018803] using wordTrace_append hprefix tailTrace_5018803
  have hstable : (prefixWord ++ tailWord_5018803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018803).length < 2 ^ (prefixWord ++ tailWord_5018803).sum := by decide
  have hdescent : baseEnd_5018803 < baseStart_5018803 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018837 : List Nat := [1, 3, 2, 4, 1, 3, 1, 2, 1, 5]
def baseStart_5018837 : Nat := 118140960795 + 5018837 * 2 ^ 59
def prefixEnd_5018837 : Nat := 4983230072969 + 3 ^ 40 * 5018837 * 2
def baseEnd_5018837 : Nat := 859025235856428503618765

theorem tailTrace_5018837 : CollatzResearch.WordTrace tailWord_5018837 prefixEnd_5018837 859025235856428503618765 := by
  unfold tailWord_5018837
  simp only [CollatzResearch.WordTrace]
  refine ⟨183052023718618172963582765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122034682479078781975721843 183052023718618172963582765)
  ·
    refine ⟨68644508894481814861343537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183052023718618172963582765 68644508894481814861343537)
    ·
      refine ⟨51483381670861361146007653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68644508894481814861343537 51483381670861361146007653)
      ·
        refine ⟨9653134063286505214876435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51483381670861361146007653 9653134063286505214876435)
        ·
          refine ⟨14479701094929757822314653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9653134063286505214876435 14479701094929757822314653)
          ·
            refine ⟨5429887910598659183367995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14479701094929757822314653 5429887910598659183367995)
            ·
              refine ⟨8144831865897988775051993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5429887910598659183367995 8144831865897988775051993)
              ·
                refine ⟨6108623899423491581288995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8144831865897988775051993 6108623899423491581288995)
                ·
                  refine ⟨9162935849135237371933493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6108623899423491581288995 9162935849135237371933493)
                  ·
                    refine ⟨859025235856428503618765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9162935849135237371933493 859025235856428503618765)
                    ·
                      rfl

theorem cell23_5018837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 1, 2, 1, 5].length) (baseStart_5018837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018837 prefixEnd_5018837 := by exact prefixLift 5018837
  have htrace : WordTrace (prefixWord ++ tailWord_5018837) baseStart_5018837 baseEnd_5018837 := by
    simpa [prefixWord, tailWord_5018837, baseEnd_5018837] using wordTrace_append hprefix tailTrace_5018837
  have hstable : (prefixWord ++ tailWord_5018837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018837).length < 2 ^ (prefixWord ++ tailWord_5018837).sum := by decide
  have hdescent : baseEnd_5018837 < baseStart_5018837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018840 : List Nat := [2, 1, 2, 2, 5, 1, 1, 1, 3, 1, 4]
def baseStart_5018840 : Nat := 118140960795 + 5018840 * 2 ^ 59
def prefixEnd_5018840 : Nat := 4983230072969 + 3 ^ 40 * 5018840 * 2
def baseEnd_5018840 : Nat := 2577077248011248999118781

theorem tailTrace_5018840 : CollatzResearch.WordTrace tailWord_5018840 prefixEnd_5018840 2577077248011248999118781 := by
  unfold tailWord_5018840
  simp only [CollatzResearch.WordTrace]
  refine ⟨91526066568803652237970987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122034755425071536317294649 91526066568803652237970987)
  ·
    refine ⟨137289099853205478356956481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91526066568803652237970987 137289099853205478356956481)
    ·
      refine ⟨102966824889904108767717361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137289099853205478356956481 102966824889904108767717361)
      ·
        refine ⟨77225118667428081575788021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102966824889904108767717361 77225118667428081575788021)
        ·
          refine ⟨7239854875071382647730127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77225118667428081575788021 7239854875071382647730127)
          ·
            refine ⟨10859782312607073971595191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7239854875071382647730127 10859782312607073971595191)
            ·
              refine ⟨16289673468910610957392787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10859782312607073971595191 16289673468910610957392787)
              ·
                refine ⟨24434510203365916436089181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16289673468910610957392787 24434510203365916436089181)
                ·
                  refine ⟨9162941326262218663533443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24434510203365916436089181 9162941326262218663533443)
                  ·
                    refine ⟨13744411989393327995300165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9162941326262218663533443 13744411989393327995300165)
                    ·
                      refine ⟨2577077248011248999118781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13744411989393327995300165 2577077248011248999118781)
                      ·
                        rfl

theorem cell23_5018840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 1, 1, 1, 3, 1, 4].length) (baseStart_5018840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018840 prefixEnd_5018840 := by exact prefixLift 5018840
  have htrace : WordTrace (prefixWord ++ tailWord_5018840) baseStart_5018840 baseEnd_5018840 := by
    simpa [prefixWord, tailWord_5018840, baseEnd_5018840] using wordTrace_append hprefix tailTrace_5018840
  have hstable : (prefixWord ++ tailWord_5018840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018840).length < 2 ^ (prefixWord ++ tailWord_5018840).sum := by decide
  have hdescent : baseEnd_5018840 < baseStart_5018840 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018860 : List Nat := [2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 5]
def baseStart_5018860 : Nat := 118140960795 + 5018860 * 2 ^ 59
def prefixEnd_5018860 : Nat := 4983230072969 + 3 ^ 40 * 5018860 * 2
def baseEnd_5018860 : Nat := 2577087517624338920868689

theorem tailTrace_5018860 : CollatzResearch.WordTrace tailWord_5018860 prefixEnd_5018860 2577087517624338920868689 := by
  unfold tailWord_5018860
  simp only [CollatzResearch.WordTrace]
  refine ⟨91526431298767423945835017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122035241731689898594446689 91526431298767423945835017)
  ·
    refine ⟨68644823474075567959376263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91526431298767423945835017 68644823474075567959376263)
    ·
      refine ⟨102967235211113351939064395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68644823474075567959376263 102967235211113351939064395)
      ·
        refine ⟨154450852816670027908596593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102967235211113351939064395 154450852816670027908596593)
        ·
          refine ⟨115838139612502520931447445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154450852816670027908596593 115838139612502520931447445)
          ·
            refine ⟨5429912794336055668661599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 115838139612502520931447445 5429912794336055668661599)
            ·
              refine ⟨8144869191504083502992399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5429912794336055668661599 8144869191504083502992399)
              ·
                refine ⟨12217303787256125254488599, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8144869191504083502992399 12217303787256125254488599)
                ·
                  refine ⟨18325955680884187881732899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12217303787256125254488599 18325955680884187881732899)
                  ·
                    refine ⟨27488933521326281822599349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18325955680884187881732899 27488933521326281822599349)
                    ·
                      refine ⟨2577087517624338920868689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27488933521326281822599349 2577087517624338920868689)
                      ·
                        rfl

theorem cell23_5018860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 5].length) (baseStart_5018860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018860 prefixEnd_5018860 := by exact prefixLift 5018860
  have htrace : WordTrace (prefixWord ++ tailWord_5018860) baseStart_5018860 baseEnd_5018860 := by
    simpa [prefixWord, tailWord_5018860, baseEnd_5018860] using wordTrace_append hprefix tailTrace_5018860
  have hstable : (prefixWord ++ tailWord_5018860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018860).length < 2 ^ (prefixWord ++ tailWord_5018860).sum := by decide
  have hdescent : baseEnd_5018860 < baseStart_5018860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018863 : List Nat := [1, 1, 2, 1, 8, 10]
def baseStart_5018863 : Nat := 118140960795 + 5018863 * 2 ^ 59
def prefixEnd_5018863 : Nat := 4983230072969 + 3 ^ 40 * 5018863 * 2
def baseEnd_5018863 : Nat := 10605304765704948185725

theorem tailTrace_5018863 : CollatzResearch.WordTrace tailWord_5018863 prefixEnd_5018863 10605304765704948185725 := by
  unfold tailWord_5018863
  simp only [CollatzResearch.WordTrace]
  refine ⟨183052972016523979404029243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122035314677682652936019495 183052972016523979404029243)
  ·
    refine ⟨274579458024785969106043865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183052972016523979404029243 274579458024785969106043865)
    ·
      refine ⟨205934593518589476829532899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274579458024785969106043865 205934593518589476829532899)
      ·
        refine ⟨308901890277884215244299349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205934593518589476829532899 308901890277884215244299349)
        ·
          refine ⟨3619944026693955647394133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 308901890277884215244299349 3619944026693955647394133)
          ·
            refine ⟨10605304765704948185725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3619944026693955647394133 10605304765704948185725)
            ·
              rfl

theorem cell23_5018863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 8, 10].length) (baseStart_5018863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018863 prefixEnd_5018863 := by exact prefixLift 5018863
  have htrace : WordTrace (prefixWord ++ tailWord_5018863) baseStart_5018863 baseEnd_5018863 := by
    simpa [prefixWord, tailWord_5018863, baseEnd_5018863] using wordTrace_append hprefix tailTrace_5018863
  have hstable : (prefixWord ++ tailWord_5018863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018863).length < 2 ^ (prefixWord ++ tailWord_5018863).sum := by decide
  have hdescent : baseEnd_5018863 < baseStart_5018863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018873 : List Nat := [1, 2, 1, 3, 1, 1, 3, 2, 3, 3, 3]
def baseStart_5018873 : Nat := 118140960795 + 5018873 * 2 ^ 59
def prefixEnd_5018873 : Nat := 4983230072969 + 3 ^ 40 * 5018873 * 2
def baseEnd_5018873 : Nat := 2577094192872847370006129

theorem tailTrace_5018873 : CollatzResearch.WordTrace tailWord_5018873 prefixEnd_5018873 2577094192872847370006129 := by
  unfold tailWord_5018873
  simp only [CollatzResearch.WordTrace]
  refine ⟨183053336746487751111893273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122035557830991834074595515 183053336746487751111893273)
  ·
    refine ⟨137290002559865813333919955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183053336746487751111893273 137290002559865813333919955)
    ·
      refine ⟨205935003839798720000879933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137290002559865813333919955 205935003839798720000879933)
      ·
        refine ⟨77225626439924520000329975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205935003839798720000879933 77225626439924520000329975)
        ·
          refine ⟨115838439659886780000494963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77225626439924520000329975 115838439659886780000494963)
          ·
            refine ⟨173757659489830170000742445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115838439659886780000494963 173757659489830170000742445)
            ·
              refine ⟨65159122308686313750278417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173757659489830170000742445 65159122308686313750278417)
              ·
                refine ⟨48869341731514735312708813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65159122308686313750278417 48869341731514735312708813)
                ·
                  refine ⟨18326003149318025742265805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48869341731514735312708813 18326003149318025742265805)
                  ·
                    refine ⟨6872251180994259653349677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18326003149318025742265805 6872251180994259653349677)
                    ·
                      refine ⟨2577094192872847370006129, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6872251180994259653349677 2577094192872847370006129)
                      ·
                        rfl

theorem cell23_5018873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 3, 2, 3, 3, 3].length) (baseStart_5018873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018873 prefixEnd_5018873 := by exact prefixLift 5018873
  have htrace : WordTrace (prefixWord ++ tailWord_5018873) baseStart_5018873 baseEnd_5018873 := by
    simpa [prefixWord, tailWord_5018873, baseEnd_5018873] using wordTrace_append hprefix tailTrace_5018873
  have hstable : (prefixWord ++ tailWord_5018873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018873).length < 2 ^ (prefixWord ++ tailWord_5018873).sum := by decide
  have hdescent : baseEnd_5018873 < baseStart_5018873 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018874 : List Nat := [3, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2]
def baseStart_5018874 : Nat := 118140960795 + 5018874 * 2 ^ 59
def prefixEnd_5018874 : Nat := 4983230072969 + 3 ^ 40 * 5018874 * 2
def baseEnd_5018874 : Nat := 2577094706353501866093625

theorem tailTrace_5018874 : CollatzResearch.WordTrace tailWord_5018874 prefixEnd_5018874 2577094706353501866093625 := by
  unfold tailWord_5018874
  simp only [CollatzResearch.WordTrace]
  refine ⟨45763343304871032070669919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122035582146322752188453117 45763343304871032070669919)
  ·
    refine ⟨68645014957306548106004879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45763343304871032070669919 68645014957306548106004879)
    ·
      refine ⟨102967522435959822159007319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68645014957306548106004879 102967522435959822159007319)
      ·
        refine ⟨154451283653939733238510979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102967522435959822159007319 154451283653939733238510979)
        ·
          refine ⟨231676925480909599857766469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154451283653939733238510979 231676925480909599857766469)
          ·
            refine ⟨43439423527670549973331213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 231676925480909599857766469 43439423527670549973331213)
            ·
              refine ⟨16289783822876456239999205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43439423527670549973331213 16289783822876456239999205)
              ·
                refine ⟨3054334466789335544999851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16289783822876456239999205 3054334466789335544999851)
                ·
                  refine ⟨4581501700184003317499777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3054334466789335544999851 4581501700184003317499777)
                  ·
                    refine ⟨3436126275138002488124833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4581501700184003317499777 3436126275138002488124833)
                    ·
                      refine ⟨2577094706353501866093625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3436126275138002488124833 2577094706353501866093625)
                      ·
                        rfl

theorem cell23_5018874_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 3, 4, 1, 2, 2].length) (baseStart_5018874 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018874 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018874 prefixEnd_5018874 := by exact prefixLift 5018874
  have htrace : WordTrace (prefixWord ++ tailWord_5018874) baseStart_5018874 baseEnd_5018874 := by
    simpa [prefixWord, tailWord_5018874, baseEnd_5018874] using wordTrace_append hprefix tailTrace_5018874
  have hstable : (prefixWord ++ tailWord_5018874).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018874).length < 2 ^ (prefixWord ++ tailWord_5018874).sum := by decide
  have hdescent : baseEnd_5018874 < baseStart_5018874 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018874) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018890 : List Nat := [3, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3]
def baseStart_5018890 : Nat := 118140960795 + 5018890 * 2 ^ 59
def prefixEnd_5018890 : Nat := 4983230072969 + 3 ^ 40 * 5018890 * 2
def baseEnd_5018890 : Nat := 2577102922043973803493551

theorem tailTrace_5018890 : CollatzResearch.WordTrace tailWord_5018890 prefixEnd_5018890 2577102922043973803493551 := by
  unfold tailWord_5018890
  simp only [CollatzResearch.WordTrace]
  refine ⟨45763489196856540753815531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122035971191617442010174749 45763489196856540753815531)
  ·
    refine ⟨68645233795284811130723297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45763489196856540753815531 68645233795284811130723297)
    ·
      refine ⟨51483925346463608348042473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68645233795284811130723297 51483925346463608348042473)
      ·
        refine ⟨38612944009847706261031855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51483925346463608348042473 38612944009847706261031855)
        ·
          refine ⟨57919416014771559391547783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38612944009847706261031855 57919416014771559391547783)
          ·
            refine ⟨86879124022157339087321675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57919416014771559391547783 86879124022157339087321675)
            ·
              refine ⟨130318686033236008630982513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86879124022157339087321675 130318686033236008630982513)
              ·
                refine ⟨97739014524927006473236885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130318686033236008630982513 97739014524927006473236885)
                ·
                  refine ⟨4581516305855953428432979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 97739014524927006473236885 4581516305855953428432979)
                  ·
                    refine ⟨6872274458783930142649469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4581516305855953428432979 6872274458783930142649469)
                    ·
                      refine ⟨2577102922043973803493551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6872274458783930142649469 2577102922043973803493551)
                      ·
                        rfl

theorem cell23_5018890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_5018890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018890 prefixEnd_5018890 := by exact prefixLift 5018890
  have htrace : WordTrace (prefixWord ++ tailWord_5018890) baseStart_5018890 baseEnd_5018890 := by
    simpa [prefixWord, tailWord_5018890, baseEnd_5018890] using wordTrace_append hprefix tailTrace_5018890
  have hstable : (prefixWord ++ tailWord_5018890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018890).length < 2 ^ (prefixWord ++ tailWord_5018890).sum := by decide
  have hdescent : baseEnd_5018890 < baseStart_5018890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018903 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 5]
def baseStart_5018903 : Nat := 118140960795 + 5018903 * 2 ^ 59
def prefixEnd_5018903 : Nat := 4983230072969 + 3 ^ 40 * 5018903 * 2
def baseEnd_5018903 : Nat := 2577109597292482252630991

theorem tailTrace_5018903 : CollatzResearch.WordTrace tailWord_5018903 prefixEnd_5018903 2577109597292482252630991 := by
  unfold tailWord_5018903
  simp only [CollatzResearch.WordTrace]
  refine ⟨183054430936379066235485363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122036287290919377490323575 183054430936379066235485363)
  ·
    refine ⟨274581646404568599353228045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183054430936379066235485363 274581646404568599353228045)
    ·
      refine ⟨102968117401713224757460517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 274581646404568599353228045 102968117401713224757460517)
      ·
        refine ⟨19306522012821229642023847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 102968117401713224757460517 19306522012821229642023847)
        ·
          refine ⟨28959783019231844463035771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19306522012821229642023847 28959783019231844463035771)
          ·
            refine ⟨43439674528847766694553657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28959783019231844463035771 43439674528847766694553657)
            ·
              refine ⟨32579755896635825020915243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43439674528847766694553657 32579755896635825020915243)
              ·
                refine ⟨48869633844953737531372865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32579755896635825020915243 48869633844953737531372865)
                ·
                  refine ⟨36652225383715303148529649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48869633844953737531372865 36652225383715303148529649)
                  ·
                    refine ⟨27489169037786477361397237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36652225383715303148529649 27489169037786477361397237)
                    ·
                      refine ⟨2577109597292482252630991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27489169037786477361397237 2577109597292482252630991)
                      ·
                        rfl

theorem cell23_5018903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 2, 5].length) (baseStart_5018903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018903 prefixEnd_5018903 := by exact prefixLift 5018903
  have htrace : WordTrace (prefixWord ++ tailWord_5018903) baseStart_5018903 baseEnd_5018903 := by
    simpa [prefixWord, tailWord_5018903, baseEnd_5018903] using wordTrace_append hprefix tailTrace_5018903
  have hstable : (prefixWord ++ tailWord_5018903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018903).length < 2 ^ (prefixWord ++ tailWord_5018903).sum := by decide
  have hdescent : baseEnd_5018903 < baseStart_5018903 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018911 : List Nat := [1, 1, 2, 4, 5, 1, 2, 1, 1, 2, 3]
def baseStart_5018911 : Nat := 118140960795 + 5018911 * 2 ^ 59
def prefixEnd_5018911 : Nat := 4983230072969 + 3 ^ 40 * 5018911 * 2
def baseEnd_5018911 : Nat := 2577113705137718221330955

theorem tailTrace_5018911 : CollatzResearch.WordTrace tailWord_5018911 prefixEnd_5018911 2577113705137718221330955 := by
  unfold tailWord_5018911
  simp only [CollatzResearch.WordTrace]
  refine ⟨183054722720350083601776587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122036481813566722401184391 183054722720350083601776587)
  ·
    refine ⟨274582084080525125402664881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183054722720350083601776587 274582084080525125402664881)
    ·
      refine ⟨205936563060393844051998661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274582084080525125402664881 205936563060393844051998661)
      ·
        refine ⟨38613105573823845759749749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 205936563060393844051998661 38613105573823845759749749)
        ·
          refine ⟨3619978647545985539976539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38613105573823845759749749 3619978647545985539976539)
          ·
            refine ⟨5429967971318978309964809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3619978647545985539976539 5429967971318978309964809)
            ·
              refine ⟨4072475978489233732473607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5429967971318978309964809 4072475978489233732473607)
              ·
                refine ⟨6108713967733850598710411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4072475978489233732473607 6108713967733850598710411)
                ·
                  refine ⟨9163070951600775898065617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6108713967733850598710411 9163070951600775898065617)
                  ·
                    refine ⟨6872303213700581923549213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9163070951600775898065617 6872303213700581923549213)
                    ·
                      refine ⟨2577113705137718221330955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6872303213700581923549213 2577113705137718221330955)
                      ·
                        rfl

theorem cell23_5018911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 2, 1, 1, 2, 3].length) (baseStart_5018911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018911 prefixEnd_5018911 := by exact prefixLift 5018911
  have htrace : WordTrace (prefixWord ++ tailWord_5018911) baseStart_5018911 baseEnd_5018911 := by
    simpa [prefixWord, tailWord_5018911, baseEnd_5018911] using wordTrace_append hprefix tailTrace_5018911
  have hstable : (prefixWord ++ tailWord_5018911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018911).length < 2 ^ (prefixWord ++ tailWord_5018911).sum := by decide
  have hdescent : baseEnd_5018911 < baseStart_5018911 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018941 : List Nat := [1, 4, 1, 5, 2, 1, 1, 1, 1, 3, 3]
def baseStart_5018941 : Nat := 118140960795 + 5018941 * 2 ^ 59
def prefixEnd_5018941 : Nat := 4983230072969 + 3 ^ 40 * 5018941 * 2
def baseEnd_5018941 : Nat := 2577129109557353103955817

theorem tailTrace_5018941 : CollatzResearch.WordTrace tailWord_5018941 prefixEnd_5018941 2577129109557353103955817 := by
  unfold tailWord_5018941
  simp only [CollatzResearch.WordTrace]
  refine ⟨183055816910241398725368677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122037211273494265816912451 183055816910241398725368677)
  ·
    refine ⟨34322965670670262261006627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183055816910241398725368677 34322965670670262261006627)
    ·
      refine ⟨51484448506005393391509941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34322965670670262261006627 51484448506005393391509941)
      ·
        refine ⟨4826667047438005630454057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51484448506005393391509941 4826667047438005630454057)
        ·
          refine ⟨3620000285578504222840543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4826667047438005630454057 3620000285578504222840543)
          ·
            refine ⟨5430000428367756334260815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3620000285578504222840543 5430000428367756334260815)
            ·
              refine ⟨8145000642551634501391223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5430000428367756334260815 8145000642551634501391223)
              ·
                refine ⟨12217500963827451752086835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8145000642551634501391223 12217500963827451752086835)
                ·
                  refine ⟨18326251445741177628130253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12217500963827451752086835 18326251445741177628130253)
                  ·
                    refine ⟨6872344292152941610548845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18326251445741177628130253 6872344292152941610548845)
                    ·
                      refine ⟨2577129109557353103955817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6872344292152941610548845 2577129109557353103955817)
                      ·
                        rfl

theorem cell23_5018941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 1, 1, 3, 3].length) (baseStart_5018941 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018941 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018941 prefixEnd_5018941 := by exact prefixLift 5018941
  have htrace : WordTrace (prefixWord ++ tailWord_5018941) baseStart_5018941 baseEnd_5018941 := by
    simpa [prefixWord, tailWord_5018941, baseEnd_5018941] using wordTrace_append hprefix tailTrace_5018941
  have hstable : (prefixWord ++ tailWord_5018941).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018941).length < 2 ^ (prefixWord ++ tailWord_5018941).sum := by decide
  have hdescent : baseEnd_5018941 < baseStart_5018941 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018953 : List Nat := [1, 2, 1, 1, 2, 3, 4, 2, 7]
def baseStart_5018953 : Nat := 118140960795 + 5018953 * 2 ^ 59
def prefixEnd_5018953 : Nat := 4983230072969 + 3 ^ 40 * 5018953 * 2
def baseEnd_5018953 : Nat := 286348363480578561889529

theorem tailTrace_5018953 : CollatzResearch.WordTrace tailWord_5018953 prefixEnd_5018953 286348363480578561889529 := by
  unfold tailWord_5018953
  simp only [CollatzResearch.WordTrace]
  refine ⟨183056254586197924774805513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122037503057465283183203675 183056254586197924774805513)
  ·
    refine ⟨137292190939648443581104135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183056254586197924774805513 137292190939648443581104135)
    ·
      refine ⟨205938286409472665371656203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137292190939648443581104135 205938286409472665371656203)
      ·
        refine ⟨308907429614208998057484305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205938286409472665371656203 308907429614208998057484305)
        ·
          refine ⟨231680572210656748543113229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 308907429614208998057484305 231680572210656748543113229)
          ·
            refine ⟨86880214578996280703667461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231680572210656748543113229 86880214578996280703667461)
            ·
              refine ⟨16290040233561802631937649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86880214578996280703667461 16290040233561802631937649)
              ·
                refine ⟨12217530175171351973953237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16290040233561802631937649 12217530175171351973953237)
                ·
                  refine ⟨286348363480578561889529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12217530175171351973953237 286348363480578561889529)
                  ·
                    rfl

theorem cell23_5018953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 2, 7].length) (baseStart_5018953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018953 prefixEnd_5018953 := by exact prefixLift 5018953
  have htrace : WordTrace (prefixWord ++ tailWord_5018953) baseStart_5018953 baseEnd_5018953 := by
    simpa [prefixWord, tailWord_5018953, baseEnd_5018953] using wordTrace_append hprefix tailTrace_5018953
  have hstable : (prefixWord ++ tailWord_5018953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018953).length < 2 ^ (prefixWord ++ tailWord_5018953).sum := by decide
  have hdescent : baseEnd_5018953 < baseStart_5018953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5018993 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 1, 1, 7]
def baseStart_5018993 : Nat := 118140960795 + 5018993 * 2 ^ 59
def prefixEnd_5018993 : Nat := 4983230072969 + 3 ^ 40 * 5018993 * 2
def baseEnd_5018993 : Nat := 2577155810551386900505577

theorem tailTrace_5018993 : CollatzResearch.WordTrace tailWord_5018993 prefixEnd_5018993 2577155810551386900505577 := by
  unfold tailWord_5018993
  simp only [CollatzResearch.WordTrace]
  refine ⟨183057713506053011606261633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122038475670702007737507755 183057713506053011606261633)
  ·
    refine ⟨137293285129539758704696225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183057713506053011606261633 137293285129539758704696225)
    ·
      refine ⟨102969963847154819028522169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137293285129539758704696225 102969963847154819028522169)
      ·
        refine ⟨77227472885366114271391627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102969963847154819028522169 77227472885366114271391627)
        ·
          refine ⟨115841209328049171407087441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77227472885366114271391627 115841209328049171407087441)
          ·
            refine ⟨86880906996036878555315581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115841209328049171407087441 86880906996036878555315581)
            ·
              refine ⟨32580340123513829458243343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86880906996036878555315581 32580340123513829458243343)
              ·
                refine ⟨48870510185270744187365015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32580340123513829458243343 48870510185270744187365015)
                ·
                  refine ⟨73305765277906116281047523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48870510185270744187365015 73305765277906116281047523)
                  ·
                    refine ⟨109958647916859174421571285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 73305765277906116281047523 109958647916859174421571285)
                    ·
                      refine ⟨2577155810551386900505577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 109958647916859174421571285 2577155810551386900505577)
                      ·
                        rfl

theorem cell23_5018993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 1, 1, 7].length) (baseStart_5018993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5018993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5018993 prefixEnd_5018993 := by exact prefixLift 5018993
  have htrace : WordTrace (prefixWord ++ tailWord_5018993) baseStart_5018993 baseEnd_5018993 := by
    simpa [prefixWord, tailWord_5018993, baseEnd_5018993] using wordTrace_append hprefix tailTrace_5018993
  have hstable : (prefixWord ++ tailWord_5018993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5018993).length < 2 ^ (prefixWord ++ tailWord_5018993).sum := by decide
  have hdescent : baseEnd_5018993 < baseStart_5018993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5018993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019013 : List Nat := [1, 3, 1, 1, 3, 1, 2, 1, 2, 8]
def baseStart_5019013 : Nat := 118140960795 + 5019013 * 2 ^ 59
def prefixEnd_5019013 : Nat := 4983230072969 + 3 ^ 40 * 5019013 * 2
def baseEnd_5019013 : Nat := 859055360054825607418495

theorem tailTrace_5019013 : CollatzResearch.WordTrace tailWord_5019013 prefixEnd_5019013 859055360054825607418495 := by
  unfold tailWord_5019013
  simp only [CollatzResearch.WordTrace]
  refine ⟨183058442965980555021989693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122038961977320370014659795 183058442965980555021989693)
  ·
    refine ⟨68646916112242708133246135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183058442965980555021989693 68646916112242708133246135)
    ·
      refine ⟨102970374168364062199869203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68646916112242708133246135 102970374168364062199869203)
      ·
        refine ⟨154455561252546093299803805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102970374168364062199869203 154455561252546093299803805)
        ·
          refine ⟨57920835469704784987426427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154455561252546093299803805 57920835469704784987426427)
          ·
            refine ⟨86881253204557177481139641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57920835469704784987426427 86881253204557177481139641)
            ·
              refine ⟨65160939903417883110854731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86881253204557177481139641 65160939903417883110854731)
              ·
                refine ⟨97741409855126824666282097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65160939903417883110854731 97741409855126824666282097)
                ·
                  refine ⟨73306057391345118499711573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97741409855126824666282097 73306057391345118499711573)
                  ·
                    refine ⟨859055360054825607418495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73306057391345118499711573 859055360054825607418495)
                    ·
                      rfl

theorem cell23_5019013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 2, 1, 2, 8].length) (baseStart_5019013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019013 prefixEnd_5019013 := by exact prefixLift 5019013
  have htrace : WordTrace (prefixWord ++ tailWord_5019013) baseStart_5019013 baseEnd_5019013 := by
    simpa [prefixWord, tailWord_5019013, baseEnd_5019013] using wordTrace_append hprefix tailTrace_5019013
  have hstable : (prefixWord ++ tailWord_5019013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019013).length < 2 ^ (prefixWord ++ tailWord_5019013).sum := by decide
  have hdescent : baseEnd_5019013 < baseStart_5019013 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019017 : List Nat := [1, 2, 1, 1, 7, 1, 2, 1, 2, 5]
def baseStart_5019017 : Nat := 118140960795 + 5019017 * 2 ^ 59
def prefixEnd_5019017 : Nat := 4983230072969 + 3 ^ 40 * 5019017 * 2
def baseEnd_5019017 : Nat := 859056044695698268868489

theorem tailTrace_5019017 : CollatzResearch.WordTrace tailWord_5019017 prefixEnd_5019017 859056044695698268868489 := by
  unfold tailWord_5019017
  simp only [CollatzResearch.WordTrace]
  refine ⟨183058588857966063705135305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122039059238644042470090203 183058588857966063705135305)
  ·
    refine ⟨137293941643474547778851479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183058588857966063705135305 137293941643474547778851479)
    ·
      refine ⟨205940912465211821668277219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137293941643474547778851479 205940912465211821668277219)
      ·
        refine ⟨308911368697817732502415829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205940912465211821668277219 308911368697817732502415829)
        ·
          refine ⟨7240110203855103105525371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 308911368697817732502415829 7240110203855103105525371)
          ·
            refine ⟨10860165305782654658288057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7240110203855103105525371 10860165305782654658288057)
            ·
              refine ⟨8145123979336990993716043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10860165305782654658288057 8145123979336990993716043)
              ·
                refine ⟨12217685969005486490574065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8145123979336990993716043 12217685969005486490574065)
                ·
                  refine ⟨9163264476754114867930549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12217685969005486490574065 9163264476754114867930549)
                  ·
                    refine ⟨859056044695698268868489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9163264476754114867930549 859056044695698268868489)
                    ·
                      rfl

theorem cell23_5019017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 7, 1, 2, 1, 2, 5].length) (baseStart_5019017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019017 prefixEnd_5019017 := by exact prefixLift 5019017
  have htrace : WordTrace (prefixWord ++ tailWord_5019017) baseStart_5019017 baseEnd_5019017 := by
    simpa [prefixWord, tailWord_5019017, baseEnd_5019017] using wordTrace_append hprefix tailTrace_5019017
  have hstable : (prefixWord ++ tailWord_5019017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019017).length < 2 ^ (prefixWord ++ tailWord_5019017).sum := by decide
  have hdescent : baseEnd_5019017 < baseStart_5019017 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019037 : List Nat := [1, 4, 2, 1, 3, 1, 2, 2, 2, 1, 4]
def baseStart_5019037 : Nat := 118140960795 + 5019037 * 2 ^ 59
def prefixEnd_5019037 : Nat := 4983230072969 + 3 ^ 40 * 5019037 * 2
def baseEnd_5019037 : Nat := 2577178403700184728355375

theorem tailTrace_5019037 : CollatzResearch.WordTrace tailWord_5019037 prefixEnd_5019037 2577178403700184728355375 := by
  unfold tailWord_5019037
  simp only [CollatzResearch.WordTrace]
  refine ⟨183059318317893607120863365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122039545545262404747242243 183059318317893607120863365)
  ·
    refine ⟨34323622184605051335161881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183059318317893607120863365 34323622184605051335161881)
    ·
      refine ⟨25742716638453788501371411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34323622184605051335161881 25742716638453788501371411)
      ·
        refine ⟨38614074957680682752057117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25742716638453788501371411 38614074957680682752057117)
        ·
          refine ⟨14480278109130256032021419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38614074957680682752057117 14480278109130256032021419)
          ·
            refine ⟨21720417163695384048032129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14480278109130256032021419 21720417163695384048032129)
            ·
              refine ⟨16290312872771538036024097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21720417163695384048032129 16290312872771538036024097)
              ·
                refine ⟨12217734654578653527018073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16290312872771538036024097 12217734654578653527018073)
                ·
                  refine ⟨9163300990933990145263555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12217734654578653527018073 9163300990933990145263555)
                  ·
                    refine ⟨13744951486400985217895333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9163300990933990145263555 13744951486400985217895333)
                    ·
                      refine ⟨2577178403700184728355375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13744951486400985217895333 2577178403700184728355375)
                      ·
                        rfl

theorem cell23_5019037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 2, 2, 1, 4].length) (baseStart_5019037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019037 prefixEnd_5019037 := by exact prefixLift 5019037
  have htrace : WordTrace (prefixWord ++ tailWord_5019037) baseStart_5019037 baseEnd_5019037 := by
    simpa [prefixWord, tailWord_5019037, baseEnd_5019037] using wordTrace_append hprefix tailTrace_5019037
  have hstable : (prefixWord ++ tailWord_5019037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019037).length < 2 ^ (prefixWord ++ tailWord_5019037).sum := by decide
  have hdescent : baseEnd_5019037 < baseStart_5019037 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019038 : List Nat := [4, 3, 1, 2, 2, 2, 2, 2, 5]
def baseStart_5019038 : Nat := 118140960795 + 5019038 * 2 ^ 59
def prefixEnd_5019038 : Nat := 4983230072969 + 3 ^ 40 * 5019038 * 2
def baseEnd_5019038 : Nat := 286353213020093247160319

theorem tailTrace_5019038 : CollatzResearch.WordTrace tailWord_5019038 prefixEnd_5019038 286353213020093247160319 := by
  unfold tailWord_5019038
  simp only [CollatzResearch.WordTrace]
  refine ⟨22882419348861248036456221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122039569860593322861099845 22882419348861248036456221)
  ·
    refine ⟨8580907255822968013671083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22882419348861248036456221 8580907255822968013671083)
    ·
      refine ⟨12871360883734452020506625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8580907255822968013671083 12871360883734452020506625)
      ·
        refine ⟨9653520662800839015379969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12871360883734452020506625 9653520662800839015379969)
        ·
          refine ⟨7240140497100629261534977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9653520662800839015379969 7240140497100629261534977)
          ·
            refine ⟨5430105372825471946151233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7240140497100629261534977 5430105372825471946151233)
            ·
              refine ⟨4072579029619103959613425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5430105372825471946151233 4072579029619103959613425)
              ·
                refine ⟨3054434272214327969710069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4072579029619103959613425 3054434272214327969710069)
                ·
                  refine ⟨286353213020093247160319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3054434272214327969710069 286353213020093247160319)
                  ·
                    rfl

theorem cell23_5019038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_5019038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019038 prefixEnd_5019038 := by exact prefixLift 5019038
  have htrace : WordTrace (prefixWord ++ tailWord_5019038) baseStart_5019038 baseEnd_5019038 := by
    simpa [prefixWord, tailWord_5019038, baseEnd_5019038] using wordTrace_append hprefix tailTrace_5019038
  have hstable : (prefixWord ++ tailWord_5019038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019038).length < 2 ^ (prefixWord ++ tailWord_5019038).sum := by decide
  have hdescent : baseEnd_5019038 < baseStart_5019038 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019047 : List Nat := [1, 1, 6, 1, 1, 1, 2, 3, 3, 4]
def baseStart_5019047 : Nat := 118140960795 + 5019047 * 2 ^ 59
def prefixEnd_5019047 : Nat := 4983230072969 + 3 ^ 40 * 5019047 * 2
def baseEnd_5019047 : Nat := 859061179502243229743443

theorem tailTrace_5019047 : CollatzResearch.WordTrace tailWord_5019047 prefixEnd_5019047 859061179502243229743443 := by
  unfold tailWord_5019047
  simp only [CollatzResearch.WordTrace]
  refine ⟨183059683047857378828727395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122039788698571585885818263 183059683047857378828727395)
  ·
    refine ⟨274589524571786068243091093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183059683047857378828727395 274589524571786068243091093)
    ·
      refine ⟨12871383964302471948894895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 274589524571786068243091093 12871383964302471948894895)
      ·
        refine ⟨19307075946453707923342343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12871383964302471948894895 19307075946453707923342343)
        ·
          refine ⟨28960613919680561885013515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19307075946453707923342343 28960613919680561885013515)
          ·
            refine ⟨43440920879520842827520273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28960613919680561885013515 43440920879520842827520273)
            ·
              refine ⟨32580690659640632120640205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43440920879520842827520273 32580690659640632120640205)
              ·
                refine ⟨12217758997365237045240077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32580690659640632120640205 12217758997365237045240077)
                ·
                  refine ⟨4581659624011963891965029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12217758997365237045240077 4581659624011963891965029)
                  ·
                    refine ⟨859061179502243229743443, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4581659624011963891965029 859061179502243229743443)
                    ·
                      rfl

theorem cell23_5019047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_5019047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019047 prefixEnd_5019047 := by exact prefixLift 5019047
  have htrace : WordTrace (prefixWord ++ tailWord_5019047) baseStart_5019047 baseEnd_5019047 := by
    simpa [prefixWord, tailWord_5019047, baseEnd_5019047] using wordTrace_append hprefix tailTrace_5019047
  have hstable : (prefixWord ++ tailWord_5019047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019047).length < 2 ^ (prefixWord ++ tailWord_5019047).sum := by decide
  have hdescent : baseEnd_5019047 < baseStart_5019047 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019094 : List Nat := [5, 2, 1, 1, 1, 2, 3, 2, 6]
def baseStart_5019094 : Nat := 118140960795 + 5019094 * 2 ^ 59
def prefixEnd_5019094 : Nat := 4983230072969 + 3 ^ 40 * 5019094 * 2
def baseEnd_5019094 : Nat := 286356408010832333926957

theorem tailTrace_5019094 : CollatzResearch.WordTrace tailWord_5019094 prefixEnd_5019094 286356408010832333926957 := by
  unfold tailWord_5019094
  simp only [CollatzResearch.WordTrace]
  refine ⟨11441337329917944115980521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122040931519124737237125557 11441337329917944115980521)
  ·
    refine ⟨8581002997438458086985391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11441337329917944115980521 8581002997438458086985391)
    ·
      refine ⟨12871504496157687130478087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8581002997438458086985391 12871504496157687130478087)
      ·
        refine ⟨19307256744236530695717131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12871504496157687130478087 19307256744236530695717131)
        ·
          refine ⟨28960885116354796043575697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19307256744236530695717131 28960885116354796043575697)
          ·
            refine ⟨21720663837266097032681773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28960885116354796043575697 21720663837266097032681773)
            ·
              refine ⟨8145248938974786387255665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21720663837266097032681773 8145248938974786387255665)
              ·
                refine ⟨6108936704231089790441749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8145248938974786387255665 6108936704231089790441749)
                ·
                  refine ⟨286356408010832333926957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6108936704231089790441749 286356408010832333926957)
                  ·
                    rfl

theorem cell23_5019094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 2, 3, 2, 6].length) (baseStart_5019094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019094 prefixEnd_5019094 := by exact prefixLift 5019094
  have htrace : WordTrace (prefixWord ++ tailWord_5019094) baseStart_5019094 baseEnd_5019094 := by
    simpa [prefixWord, tailWord_5019094, baseEnd_5019094] using wordTrace_append hprefix tailTrace_5019094
  have hstable : (prefixWord ++ tailWord_5019094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019094).length < 2 ^ (prefixWord ++ tailWord_5019094).sum := by decide
  have hdescent : baseEnd_5019094 < baseStart_5019094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019130 : List Nat := [3, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5]
def baseStart_5019130 : Nat := 118140960795 + 5019130 * 2 ^ 59
def prefixEnd_5019130 : Nat := 4983230072969 + 3 ^ 40 * 5019130 * 2
def baseEnd_5019130 : Nat := 2577226157401052864492447

theorem tailTrace_5019130 : CollatzResearch.WordTrace tailWord_5019130 prefixEnd_5019130 2577226157401052864492447 := by
  unfold tailWord_5019130
  simp only [CollatzResearch.WordTrace]
  refine ⟨45765677576639171000999711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122041806871037789335999229 45765677576639171000999711)
  ·
    refine ⟨68648516364958756501499567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45765677576639171000999711 68648516364958756501499567)
    ·
      refine ⟨102972774547438134752249351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68648516364958756501499567 102972774547438134752249351)
      ·
        refine ⟨154459161821157202128374027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102972774547438134752249351 154459161821157202128374027)
        ·
          refine ⟨231688742731735803192561041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154459161821157202128374027 231688742731735803192561041)
          ·
            refine ⟨173766557048801852394420781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231688742731735803192561041 173766557048801852394420781)
            ·
              refine ⟨65162458893300694647907793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173766557048801852394420781 65162458893300694647907793)
              ·
                refine ⟨48871844169975520985930845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65162458893300694647907793 48871844169975520985930845)
                ·
                  refine ⟨18326941563740820369724067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48871844169975520985930845 18326941563740820369724067)
                  ·
                    refine ⟨27490412345611230554586101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18326941563740820369724067 27490412345611230554586101)
                    ·
                      refine ⟨2577226157401052864492447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27490412345611230554586101 2577226157401052864492447)
                      ·
                        rfl

theorem cell23_5019130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 2, 3, 1, 5].length) (baseStart_5019130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019130 prefixEnd_5019130 := by exact prefixLift 5019130
  have htrace : WordTrace (prefixWord ++ tailWord_5019130) baseStart_5019130 baseEnd_5019130 := by
    simpa [prefixWord, tailWord_5019130, baseEnd_5019130] using wordTrace_append hprefix tailTrace_5019130
  have hstable : (prefixWord ++ tailWord_5019130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019130).length < 2 ^ (prefixWord ++ tailWord_5019130).sum := by decide
  have hdescent : baseEnd_5019130 < baseStart_5019130 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019144 : List Nat := [2, 1, 3, 2, 1, 1, 2, 2, 5, 2, 2]
def baseStart_5019144 : Nat := 118140960795 + 5019144 * 2 ^ 59
def prefixEnd_5019144 : Nat := 4983230072969 + 3 ^ 40 * 5019144 * 2
def baseEnd_5019144 : Nat := 2577233346130215809717383

theorem tailTrace_5019144 : CollatzResearch.WordTrace tailWord_5019144 prefixEnd_5019144 2577233346130215809717383 := by
  unfold tailWord_5019144
  simp only [CollatzResearch.WordTrace]
  refine ⟨91531610464252982197504243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122042147285670642930005657 91531610464252982197504243)
  ·
    refine ⟨137297415696379473296256365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91531610464252982197504243 137297415696379473296256365)
    ·
      refine ⟨51486530886142302486096137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137297415696379473296256365 51486530886142302486096137)
      ·
        refine ⟨38614898164606726864572103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51486530886142302486096137 38614898164606726864572103)
        ·
          refine ⟨57922347246910090296858155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38614898164606726864572103 57922347246910090296858155)
          ·
            refine ⟨86883520870365135445287233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57922347246910090296858155 86883520870365135445287233)
            ·
              refine ⟨65162640652773851583965425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86883520870365135445287233 65162640652773851583965425)
              ·
                refine ⟨48871980489580388687974069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65162640652773851583965425 48871980489580388687974069)
                ·
                  refine ⟨4581748170898161439497569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48871980489580388687974069 4581748170898161439497569)
                  ·
                    refine ⟨3436311128173621079623177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4581748170898161439497569 3436311128173621079623177)
                    ·
                      refine ⟨2577233346130215809717383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3436311128173621079623177 2577233346130215809717383)
                      ·
                        rfl

theorem cell23_5019144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 2, 2, 5, 2, 2].length) (baseStart_5019144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019144 prefixEnd_5019144 := by exact prefixLift 5019144
  have htrace : WordTrace (prefixWord ++ tailWord_5019144) baseStart_5019144 baseEnd_5019144 := by
    simpa [prefixWord, tailWord_5019144, baseEnd_5019144] using wordTrace_append hprefix tailTrace_5019144
  have hstable : (prefixWord ++ tailWord_5019144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019144).length < 2 ^ (prefixWord ++ tailWord_5019144).sum := by decide
  have hdescent : baseEnd_5019144 < baseStart_5019144 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019268 : List Nat := [2, 3, 2, 1, 4, 1, 1, 1, 4, 2, 2]
def baseStart_5019268 : Nat := 118140960795 + 5019268 * 2 ^ 59
def prefixEnd_5019268 : Nat := 4983230072969 + 3 ^ 40 * 5019268 * 2
def baseEnd_5019268 : Nat := 2577297017731373324566813

theorem tailTrace_5019268 : CollatzResearch.WordTrace tailWord_5019268 prefixEnd_5019268 2577297017731373324566813 := by
  unfold tailWord_5019268
  simp only [CollatzResearch.WordTrace]
  refine ⟨91533871790028366786261229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122045162386704489048348305 91533871790028366786261229)
  ·
    refine ⟨34325201921260637544847961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91533871790028366786261229 34325201921260637544847961)
    ·
      refine ⟨25743901440945478158635971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34325201921260637544847961 25743901440945478158635971)
      ·
        refine ⟨38615852161418217237953957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25743901440945478158635971 38615852161418217237953957)
        ·
          refine ⟨7240472280265915732116367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38615852161418217237953957 7240472280265915732116367)
          ·
            refine ⟨10860708420398873598174551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7240472280265915732116367 10860708420398873598174551)
            ·
              refine ⟨16291062630598310397261827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10860708420398873598174551 16291062630598310397261827)
              ·
                refine ⟨24436593945897465595892741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16291062630598310397261827 24436593945897465595892741)
                ·
                  refine ⟨4581861364855774799229889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24436593945897465595892741 4581861364855774799229889)
                  ·
                    refine ⟨3436396023641831099422417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4581861364855774799229889 3436396023641831099422417)
                    ·
                      refine ⟨2577297017731373324566813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3436396023641831099422417 2577297017731373324566813)
                      ·
                        rfl

theorem cell23_5019268_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 4, 1, 1, 1, 4, 2, 2].length) (baseStart_5019268 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019268 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019268 prefixEnd_5019268 := by exact prefixLift 5019268
  have htrace : WordTrace (prefixWord ++ tailWord_5019268) baseStart_5019268 baseEnd_5019268 := by
    simpa [prefixWord, tailWord_5019268, baseEnd_5019268] using wordTrace_append hprefix tailTrace_5019268
  have hstable : (prefixWord ++ tailWord_5019268).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019268).length < 2 ^ (prefixWord ++ tailWord_5019268).sum := by decide
  have hdescent : baseEnd_5019268 < baseStart_5019268 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019268) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019274 : List Nat := [3, 1, 2, 3, 2, 2, 2, 1, 7]
def baseStart_5019274 : Nat := 118140960795 + 5019274 * 2 ^ 59
def prefixEnd_5019274 : Nat := 4983230072969 + 3 ^ 40 * 5019274 * 2
def baseEnd_5019274 : Nat := 286366677623922255676865

theorem tailTrace_5019274 : CollatzResearch.WordTrace tailWord_5019274 prefixEnd_5019274 286366677623922255676865 := by
  unfold tailWord_5019274
  simp only [CollatzResearch.WordTrace]
  refine ⟨45766990604508749149310219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122045308278689997731493917 45766990604508749149310219)
  ·
    refine ⟨68650485906763123723965329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45766990604508749149310219 68650485906763123723965329)
    ·
      refine ⟨51487864430072342792973997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68650485906763123723965329 51487864430072342792973997)
      ·
        refine ⟨19307949161277128547365249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51487864430072342792973997 19307949161277128547365249)
        ·
          refine ⟨14480961870957846410523937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19307949161277128547365249 14480961870957846410523937)
          ·
            refine ⟨10860721403218384807892953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14480961870957846410523937 10860721403218384807892953)
            ·
              refine ⟨8145541052413788605919715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10860721403218384807892953 8145541052413788605919715)
              ·
                refine ⟨12218311578620682908879573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8145541052413788605919715 12218311578620682908879573)
                ·
                  refine ⟨286366677623922255676865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12218311578620682908879573 286366677623922255676865)
                  ·
                    rfl

theorem cell23_5019274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 1, 7].length) (baseStart_5019274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019274 prefixEnd_5019274 := by exact prefixLift 5019274
  have htrace : WordTrace (prefixWord ++ tailWord_5019274) baseStart_5019274 baseEnd_5019274 := by
    simpa [prefixWord, tailWord_5019274, baseEnd_5019274] using wordTrace_append hprefix tailTrace_5019274
  have hstable : (prefixWord ++ tailWord_5019274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019274).length < 2 ^ (prefixWord ++ tailWord_5019274).sum := by decide
  have hdescent : baseEnd_5019274 < baseStart_5019274 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019287 : List Nat := [1, 1, 3, 3, 2, 2, 1, 2, 1, 7]
def baseStart_5019287 : Nat := 118140960795 + 5019287 * 2 ^ 59
def prefixEnd_5019287 : Nat := 4983230072969 + 3 ^ 40 * 5019287 * 2
def baseEnd_5019287 : Nat := 859102257954602916743075

theorem tailTrace_5019287 : CollatzResearch.WordTrace tailWord_5019287 prefixEnd_5019287 859102257954602916743075 := by
  unfold tailWord_5019287
  simp only [CollatzResearch.WordTrace]
  refine ⟨183068436566987899817464115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122045624377991933211642743 183068436566987899817464115)
  ·
    refine ⟨274602654850481849726196173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183068436566987899817464115 274602654850481849726196173)
    ·
      refine ⟨102975995568930693647323565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 274602654850481849726196173 102975995568930693647323565)
      ·
        refine ⟨38615998338349010117746337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102975995568930693647323565 38615998338349010117746337)
        ·
          refine ⟨28961998753761757588309753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38615998338349010117746337 28961998753761757588309753)
          ·
            refine ⟨21721499065321318191232315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28961998753761757588309753 21721499065321318191232315)
            ·
              refine ⟨32582248597981977286848473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21721499065321318191232315 32582248597981977286848473)
              ·
                refine ⟨24436686448486482965136355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32582248597981977286848473 24436686448486482965136355)
                ·
                  refine ⟨36655029672729724447704533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24436686448486482965136355 36655029672729724447704533)
                  ·
                    refine ⟨859102257954602916743075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36655029672729724447704533 859102257954602916743075)
                    ·
                      rfl

theorem cell23_5019287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 1, 2, 1, 7].length) (baseStart_5019287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019287 prefixEnd_5019287 := by exact prefixLift 5019287
  have htrace : WordTrace (prefixWord ++ tailWord_5019287) baseStart_5019287 baseEnd_5019287 := by
    simpa [prefixWord, tailWord_5019287, baseEnd_5019287] using wordTrace_append hprefix tailTrace_5019287
  have hstable : (prefixWord ++ tailWord_5019287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019287).length < 2 ^ (prefixWord ++ tailWord_5019287).sum := by decide
  have hdescent : baseEnd_5019287 < baseStart_5019287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019324 : List Nat := [2, 2, 2, 3, 1, 2, 1, 1, 4, 1, 4]
def baseStart_5019324 : Nat := 118140960795 + 5019324 * 2 ^ 59
def prefixEnd_5019324 : Nat := 4983230072969 + 3 ^ 40 * 5019324 * 2
def baseEnd_5019324 : Nat := 2577325772648025105466555

theorem tailTrace_5019324 : CollatzResearch.WordTrace tailWord_5019324 prefixEnd_5019324 2577325772648025105466555 := by
  unfold tailWord_5019324
  simp only [CollatzResearch.WordTrace]
  refine ⟨91534893033926927568280513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122046524045235903424374017 91534893033926927568280513)
  ·
    refine ⟨68651169775445195676210385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91534893033926927568280513 68651169775445195676210385)
    ·
      refine ⟨51488377331583896757157789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68651169775445195676210385 51488377331583896757157789)
      ·
        refine ⟨19308141499343961283934171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51488377331583896757157789 19308141499343961283934171)
        ·
          refine ⟨28962212249015941925901257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19308141499343961283934171 28962212249015941925901257)
          ·
            refine ⟨21721659186761956444425943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28962212249015941925901257 21721659186761956444425943)
            ·
              refine ⟨32582488780142934666638915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21721659186761956444425943 32582488780142934666638915)
              ·
                refine ⟨48873733170214401999958373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32582488780142934666638915 48873733170214401999958373)
                ·
                  refine ⟨9163824969415200374992195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48873733170214401999958373 9163824969415200374992195)
                  ·
                    refine ⟨13745737454122800562488293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9163824969415200374992195 13745737454122800562488293)
                    ·
                      refine ⟨2577325772648025105466555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13745737454122800562488293 2577325772648025105466555)
                      ·
                        rfl

theorem cell23_5019324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_5019324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019324 prefixEnd_5019324 := by exact prefixLift 5019324
  have htrace : WordTrace (prefixWord ++ tailWord_5019324) baseStart_5019324 baseEnd_5019324 := by
    simpa [prefixWord, tailWord_5019324, baseEnd_5019324] using wordTrace_append hprefix tailTrace_5019324
  have hstable : (prefixWord ++ tailWord_5019324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019324).length < 2 ^ (prefixWord ++ tailWord_5019324).sum := by decide
  have hdescent : baseEnd_5019324 < baseStart_5019324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019418 : List Nat := [3, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2]
def baseStart_5019418 : Nat := 118140960795 + 5019418 * 2 ^ 59
def prefixEnd_5019418 : Nat := 4983230072969 + 3 ^ 40 * 5019418 * 2
def baseEnd_5019418 : Nat := 2577374039829547737691123

theorem tailTrace_5019418 : CollatzResearch.WordTrace tailWord_5019418 prefixEnd_5019418 2577374039829547737691123 := by
  unfold tailWord_5019418
  simp only [CollatzResearch.WordTrace]
  refine ⟨45768303632378327297620727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122048809686342206126988605 45768303632378327297620727)
  ·
    refine ⟨68652455448567490946431091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45768303632378327297620727 68652455448567490946431091)
    ·
      refine ⟨102978683172851236419646637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68652455448567490946431091 102978683172851236419646637)
      ·
        refine ⟨38617006189819213657367489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102978683172851236419646637 38617006189819213657367489)
        ·
          refine ⟨28962754642364410243025617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38617006189819213657367489 28962754642364410243025617)
          ·
            refine ⟨21722065981773307682269213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28962754642364410243025617 21722065981773307682269213)
            ·
              refine ⟨8145774743164990380850955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21722065981773307682269213 8145774743164990380850955)
              ·
                refine ⟨12218662114747485571276433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8145774743164990380850955 12218662114747485571276433)
                ·
                  refine ⟨9163996586060614178457325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12218662114747485571276433 9163996586060614178457325)
                  ·
                    refine ⟨3436498719772730316921497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9163996586060614178457325 3436498719772730316921497)
                    ·
                      refine ⟨2577374039829547737691123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3436498719772730316921497 2577374039829547737691123)
                      ·
                        rfl

theorem cell23_5019418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 3, 1, 2, 3, 2].length) (baseStart_5019418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019418 prefixEnd_5019418 := by exact prefixLift 5019418
  have htrace : WordTrace (prefixWord ++ tailWord_5019418) baseStart_5019418 baseEnd_5019418 := by
    simpa [prefixWord, tailWord_5019418, baseEnd_5019418] using wordTrace_append hprefix tailTrace_5019418
  have hstable : (prefixWord ++ tailWord_5019418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019418).length < 2 ^ (prefixWord ++ tailWord_5019418).sum := by decide
  have hdescent : baseEnd_5019418 < baseStart_5019418 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019424 : List Nat := [2, 1, 1, 5, 1, 1, 1, 4, 1, 6]
def baseStart_5019424 : Nat := 118140960795 + 5019424 * 2 ^ 59
def prefixEnd_5019424 : Nat := 4983230072969 + 3 ^ 40 * 5019424 * 2
def baseEnd_5019424 : Nat := 859125706904491571405365

theorem tailTrace_5019424 : CollatzResearch.WordTrace tailWord_5019424 prefixEnd_5019424 859125706904491571405365 := by
  unfold tailWord_5019424
  simp only [CollatzResearch.WordTrace]
  refine ⟨91536716683745786107600663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122048955578327714810134217 91536716683745786107600663)
  ·
    refine ⟨137305075025618679161400995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91536716683745786107600663 137305075025618679161400995)
    ·
      refine ⟨205957612538428018742101493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137305075025618679161400995 205957612538428018742101493)
      ·
        refine ⟨19308526175477626757072015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 205957612538428018742101493 19308526175477626757072015)
        ·
          refine ⟨28962789263216440135608023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19308526175477626757072015 28962789263216440135608023)
          ·
            refine ⟨43444183894824660203412035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28962789263216440135608023 43444183894824660203412035)
            ·
              refine ⟨65166275842236990305118053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43444183894824660203412035 65166275842236990305118053)
              ·
                refine ⟨12218676720419435682209635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65166275842236990305118053 12218676720419435682209635)
                ·
                  refine ⟨18328015080629153523314453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12218676720419435682209635 18328015080629153523314453)
                  ·
                    refine ⟨859125706904491571405365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18328015080629153523314453 859125706904491571405365)
                    ·
                      rfl

theorem cell23_5019424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 1, 4, 1, 6].length) (baseStart_5019424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019424 prefixEnd_5019424 := by exact prefixLift 5019424
  have htrace : WordTrace (prefixWord ++ tailWord_5019424) baseStart_5019424 baseEnd_5019424 := by
    simpa [prefixWord, tailWord_5019424, baseEnd_5019424] using wordTrace_append hprefix tailTrace_5019424
  have hstable : (prefixWord ++ tailWord_5019424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019424).length < 2 ^ (prefixWord ++ tailWord_5019424).sum := by decide
  have hdescent : baseEnd_5019424 < baseStart_5019424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019425 : List Nat := [1, 2, 3, 2, 1, 4, 2, 3, 1, 1, 3]
def baseStart_5019425 : Nat := 118140960795 + 5019425 * 2 ^ 59
def prefixEnd_5019425 : Nat := 4983230072969 + 3 ^ 40 * 5019425 * 2
def baseEnd_5019425 : Nat := 2577377634194129210303591

theorem tailTrace_5019425 : CollatzResearch.WordTrace tailWord_5019425 prefixEnd_5019425 2577377634194129210303591 := by
  unfold tailWord_5019425
  simp only [CollatzResearch.WordTrace]
  refine ⟨183073469840487949385987729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122048979893658632923991819 183073469840487949385987729)
  ·
    refine ⟨137305102380365962039490797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183073469840487949385987729 137305102380365962039490797)
    ·
      refine ⟨51489413392637235764809049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137305102380365962039490797 51489413392637235764809049)
      ·
        refine ⟨38617060044477926823606787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51489413392637235764809049 38617060044477926823606787)
        ·
          refine ⟨57925590066716890235410181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38617060044477926823606787 57925590066716890235410181)
          ·
            refine ⟨10861048137509416919139409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57925590066716890235410181 10861048137509416919139409)
            ·
              refine ⟨8145786103132062689354557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10861048137509416919139409 8145786103132062689354557)
              ·
                refine ⟨3054669788674523508507959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8145786103132062689354557 3054669788674523508507959)
                ·
                  refine ⟨4582004683011785262761939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3054669788674523508507959 4582004683011785262761939)
                  ·
                    refine ⟨6873007024517677894142909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4582004683011785262761939 6873007024517677894142909)
                    ·
                      refine ⟨2577377634194129210303591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6873007024517677894142909 2577377634194129210303591)
                      ·
                        rfl

theorem cell23_5019425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_5019425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019425 prefixEnd_5019425 := by exact prefixLift 5019425
  have htrace : WordTrace (prefixWord ++ tailWord_5019425) baseStart_5019425 baseEnd_5019425 := by
    simpa [prefixWord, tailWord_5019425, baseEnd_5019425] using wordTrace_append hprefix tailTrace_5019425
  have hstable : (prefixWord ++ tailWord_5019425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019425).length < 2 ^ (prefixWord ++ tailWord_5019425).sum := by decide
  have hdescent : baseEnd_5019425 < baseStart_5019425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019428 : List Nat := [2, 3, 1, 3, 2, 1, 4, 1, 1, 5]
def baseStart_5019428 : Nat := 118140960795 + 5019428 * 2 ^ 59
def prefixEnd_5019428 : Nat := 4983230072969 + 3 ^ 40 * 5019428 * 2
def baseEnd_5019428 : Nat := 859126391545364232855359

theorem tailTrace_5019428 : CollatzResearch.WordTrace tailWord_5019428 prefixEnd_5019428 859126391545364232855359 := by
  unfold tailWord_5019428
  simp only [CollatzResearch.WordTrace]
  refine ⟨91536789629738540449173469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122049052839651387265564625 91536789629738540449173469)
  ·
    refine ⟨34326296111151952668440051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91536789629738540449173469 34326296111151952668440051)
    ·
      refine ⟨51489444166727929002660077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34326296111151952668440051 51489444166727929002660077)
      ·
        refine ⟨19308541562522973375997529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51489444166727929002660077 19308541562522973375997529)
        ·
          refine ⟨14481406171892230031998147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19308541562522973375997529 14481406171892230031998147)
          ·
            refine ⟨21722109257838345047997221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14481406171892230031998147 21722109257838345047997221)
            ·
              refine ⟨4072895485844689696499479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21722109257838345047997221 4072895485844689696499479)
              ·
                refine ⟨6109343228767034544749219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4072895485844689696499479 6109343228767034544749219)
                ·
                  refine ⟨9164014843150551817123829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6109343228767034544749219 9164014843150551817123829)
                  ·
                    refine ⟨859126391545364232855359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9164014843150551817123829 859126391545364232855359)
                    ·
                      rfl

theorem cell23_5019428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4, 1, 1, 5].length) (baseStart_5019428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019428 prefixEnd_5019428 := by exact prefixLift 5019428
  have htrace : WordTrace (prefixWord ++ tailWord_5019428) baseStart_5019428 baseEnd_5019428 := by
    simpa [prefixWord, tailWord_5019428, baseEnd_5019428] using wordTrace_append hprefix tailTrace_5019428
  have hstable : (prefixWord ++ tailWord_5019428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019428).length < 2 ^ (prefixWord ++ tailWord_5019428).sum := by decide
  have hdescent : baseEnd_5019428 < baseStart_5019428 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019441 : List Nat := [1, 2, 2, 3, 2, 3, 1, 1, 4, 4]
def baseStart_5019441 : Nat := 118140960795 + 5019441 * 2 ^ 59
def prefixEnd_5019441 : Nat := 4983230072969 + 3 ^ 40 * 5019441 * 2
def baseEnd_5019441 : Nat := 859128616628200382567839

theorem tailTrace_5019441 : CollatzResearch.WordTrace tailWord_5019441 prefixEnd_5019441 859128616628200382567839 := by
  unfold tailWord_5019441
  simp only [CollatzResearch.WordTrace]
  refine ⟨183074053408429984118570177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122049368938953322745713451 183074053408429984118570177)
  ·
    refine ⟨137305540056322488088927633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183074053408429984118570177 137305540056322488088927633)
    ·
      refine ⟨102979155042241866066695725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137305540056322488088927633 102979155042241866066695725)
      ·
        refine ⟨38617183140840699775010897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102979155042241866066695725 38617183140840699775010897)
        ·
          refine ⟨28962887355630524831258173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38617183140840699775010897 28962887355630524831258173)
          ·
            refine ⟨10861082758361446811721815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28962887355630524831258173 10861082758361446811721815)
            ·
              refine ⟨16291624137542170217582723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10861082758361446811721815 16291624137542170217582723)
              ·
                refine ⟨24437436206313255326374085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16291624137542170217582723 24437436206313255326374085)
                ·
                  refine ⟨4582019288683735373695141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24437436206313255326374085 4582019288683735373695141)
                  ·
                    refine ⟨859128616628200382567839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4582019288683735373695141 859128616628200382567839)
                    ·
                      rfl

theorem cell23_5019441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 1, 4, 4].length) (baseStart_5019441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019441 prefixEnd_5019441 := by exact prefixLift 5019441
  have htrace : WordTrace (prefixWord ++ tailWord_5019441) baseStart_5019441 baseEnd_5019441 := by
    simpa [prefixWord, tailWord_5019441, baseEnd_5019441] using wordTrace_append hprefix tailTrace_5019441
  have hstable : (prefixWord ++ tailWord_5019441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019441).length < 2 ^ (prefixWord ++ tailWord_5019441).sum := by decide
  have hdescent : baseEnd_5019441 < baseStart_5019441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019448 : List Nat := [2, 1, 2, 1, 3, 3, 1, 3, 3, 2, 2]
def baseStart_5019448 : Nat := 118140960795 + 5019448 * 2 ^ 59
def prefixEnd_5019448 : Nat := 4983230072969 + 3 ^ 40 * 5019448 * 2
def baseEnd_5019448 : Nat := 2577389444249182620315985

theorem tailTrace_5019448 : CollatzResearch.WordTrace tailWord_5019448 prefixEnd_5019448 2577389444249182620315985 := by
  unfold tailWord_5019448
  simp only [CollatzResearch.WordTrace]
  refine ⟨91537154359702312157037499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122049539146269749542716665 91537154359702312157037499)
  ·
    refine ⟨137305731539553468235556249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91537154359702312157037499 137305731539553468235556249)
    ·
      refine ⟨102979298654665101176667187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137305731539553468235556249 102979298654665101176667187)
      ·
        refine ⟨154468947981997651765000781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102979298654665101176667187 154468947981997651765000781)
        ·
          refine ⟨57925855493249119411875293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154468947981997651765000781 57925855493249119411875293)
          ·
            refine ⟨21722195809968419779453235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57925855493249119411875293 21722195809968419779453235)
            ·
              refine ⟨32583293714952629669179853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21722195809968419779453235 32583293714952629669179853)
              ·
                refine ⟨12218735143107236125942445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32583293714952629669179853 12218735143107236125942445)
                ·
                  refine ⟨4582025678665213547228417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12218735143107236125942445 4582025678665213547228417)
                  ·
                    refine ⟨3436519258998910160421313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4582025678665213547228417 3436519258998910160421313)
                    ·
                      refine ⟨2577389444249182620315985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3436519258998910160421313 2577389444249182620315985)
                      ·
                        rfl

theorem cell23_5019448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 3, 1, 3, 3, 2, 2].length) (baseStart_5019448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019448 prefixEnd_5019448 := by exact prefixLift 5019448
  have htrace : WordTrace (prefixWord ++ tailWord_5019448) baseStart_5019448 baseEnd_5019448 := by
    simpa [prefixWord, tailWord_5019448, baseEnd_5019448] using wordTrace_append hprefix tailTrace_5019448
  have hstable : (prefixWord ++ tailWord_5019448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019448).length < 2 ^ (prefixWord ++ tailWord_5019448).sum := by decide
  have hdescent : baseEnd_5019448 < baseStart_5019448 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019481 : List Nat := [1, 2, 1, 2, 2, 3, 1, 1, 6, 1, 3]
def baseStart_5019481 : Nat := 118140960795 + 5019481 * 2 ^ 59
def prefixEnd_5019481 : Nat := 4983230072969 + 3 ^ 40 * 5019481 * 2
def baseEnd_5019481 : Nat := 2577406389110780991203333

theorem tailTrace_5019481 : CollatzResearch.WordTrace tailWord_5019481 prefixEnd_5019481 2577406389110780991203333 := by
  unfold tailWord_5019481
  simp only [CollatzResearch.WordTrace]
  refine ⟨183075512328285070950026297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122050341552190047300017531 183075512328285070950026297)
  ·
    refine ⟨137306634246213803212519723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183075512328285070950026297 137306634246213803212519723)
    ·
      refine ⟨205959951369320704818779585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137306634246213803212519723 205959951369320704818779585)
      ·
        refine ⟨154469963526990528614084689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205959951369320704818779585 154469963526990528614084689)
        ·
          refine ⟨115852472645242896460563517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154469963526990528614084689 115852472645242896460563517)
          ·
            refine ⟨43444677241966086172711319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115852472645242896460563517 43444677241966086172711319)
            ·
              refine ⟨65167015862949129259066979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43444677241966086172711319 65167015862949129259066979)
              ·
                refine ⟨97750523794423693888600469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65167015862949129259066979 97750523794423693888600469)
                ·
                  refine ⟨4582055802863610651028147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 97750523794423693888600469 4582055802863610651028147)
                  ·
                    refine ⟨6873083704295415976542221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4582055802863610651028147 6873083704295415976542221)
                    ·
                      refine ⟨2577406389110780991203333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6873083704295415976542221 2577406389110780991203333)
                      ·
                        rfl

theorem cell23_5019481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 1, 1, 6, 1, 3].length) (baseStart_5019481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019481 prefixEnd_5019481 := by exact prefixLift 5019481
  have htrace : WordTrace (prefixWord ++ tailWord_5019481) baseStart_5019481 baseEnd_5019481 := by
    simpa [prefixWord, tailWord_5019481, baseEnd_5019481] using wordTrace_append hprefix tailTrace_5019481
  have hstable : (prefixWord ++ tailWord_5019481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019481).length < 2 ^ (prefixWord ++ tailWord_5019481).sum := by decide
  have hdescent : baseEnd_5019481 < baseStart_5019481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019504 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 4]
def baseStart_5019504 : Nat := 118140960795 + 5019504 * 2 ^ 59
def prefixEnd_5019504 : Nat := 4983230072969 + 3 ^ 40 * 5019504 * 2
def baseEnd_5019504 : Nat := 2577418199165834401215727

theorem tailTrace_5019504 : CollatzResearch.WordTrace tailWord_5019504 prefixEnd_5019504 2577418199165834401215727 := by
  unfold tailWord_5019504
  simp only [CollatzResearch.WordTrace]
  refine ⟨91538175603600872939056783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122050900804801163918742377 91538175603600872939056783)
  ·
    refine ⟨137307263405401309408585175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91538175603600872939056783 137307263405401309408585175)
    ·
      refine ⟨205960895108101964112877763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137307263405401309408585175 205960895108101964112877763)
      ·
        refine ⟨308941342662152946169316645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205960895108101964112877763 308941342662152946169316645)
        ·
          refine ⟨57926501749153677406746871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 308941342662152946169316645 57926501749153677406746871)
          ·
            refine ⟨86889752623730516110120307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57926501749153677406746871 86889752623730516110120307)
            ·
              refine ⟨130334628935595774165180461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86889752623730516110120307 130334628935595774165180461)
              ·
                refine ⟨48875485850848415311942673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130334628935595774165180461 48875485850848415311942673)
                ·
                  refine ⟨36656614388136311483957005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48875485850848415311942673 36656614388136311483957005)
                  ·
                    refine ⟨13746230395551116806483877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36656614388136311483957005 13746230395551116806483877)
                    ·
                      refine ⟨2577418199165834401215727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13746230395551116806483877 2577418199165834401215727)
                      ·
                        rfl

theorem cell23_5019504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 2, 3, 4].length) (baseStart_5019504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019504 prefixEnd_5019504 := by exact prefixLift 5019504
  have htrace : WordTrace (prefixWord ++ tailWord_5019504) baseStart_5019504 baseEnd_5019504 := by
    simpa [prefixWord, tailWord_5019504, baseEnd_5019504] using wordTrace_append hprefix tailTrace_5019504
  have hstable : (prefixWord ++ tailWord_5019504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019504).length < 2 ^ (prefixWord ++ tailWord_5019504).sum := by decide
  have hdescent : baseEnd_5019504 < baseStart_5019504 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019514 : List Nat := [3, 1, 1, 1, 1, 1, 4, 3, 2, 6]
def baseStart_5019514 : Nat := 118140960795 + 5019514 * 2 ^ 59
def prefixEnd_5019514 : Nat := 4983230072969 + 3 ^ 40 * 5019514 * 2
def baseEnd_5019514 : Nat := 859141111324126454030227

theorem tailTrace_5019514 : CollatzResearch.WordTrace tailWord_5019514 prefixEnd_5019514 859141111324126454030227 := by
  unfold tailWord_5019514
  simp only [CollatzResearch.WordTrace]
  refine ⟨45769178984291379396494399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122051143958110345057318397 45769178984291379396494399)
  ·
    refine ⟨68653768476437069094741599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45769178984291379396494399 68653768476437069094741599)
    ·
      refine ⟨102980652714655603642112399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68653768476437069094741599 102980652714655603642112399)
      ·
        refine ⟨154470979071983405463168599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102980652714655603642112399 154470979071983405463168599)
        ·
          refine ⟨231706468607975108194752899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154470979071983405463168599 231706468607975108194752899)
          ·
            refine ⟨347559702911962662292129349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231706468607975108194752899 347559702911962662292129349)
            ·
              refine ⟨65167444295992999179774253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 347559702911962662292129349 65167444295992999179774253)
              ·
                refine ⟨24437791610997374692415345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65167444295992999179774253 24437791610997374692415345)
                ·
                  refine ⟨18328343708248031019311509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24437791610997374692415345 18328343708248031019311509)
                  ·
                    refine ⟨859141111324126454030227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18328343708248031019311509 859141111324126454030227)
                    ·
                      rfl

theorem cell23_5019514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 3, 2, 6].length) (baseStart_5019514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019514 prefixEnd_5019514 := by exact prefixLift 5019514
  have htrace : WordTrace (prefixWord ++ tailWord_5019514) baseStart_5019514 baseEnd_5019514 := by
    simpa [prefixWord, tailWord_5019514, baseEnd_5019514] using wordTrace_append hprefix tailTrace_5019514
  have hstable : (prefixWord ++ tailWord_5019514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019514).length < 2 ^ (prefixWord ++ tailWord_5019514).sum := by decide
  have hdescent : baseEnd_5019514 < baseStart_5019514 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019550 : List Nat := [4, 3, 1, 3, 2, 1, 2, 2, 1, 2, 2]
def baseStart_5019550 : Nat := 118140960795 + 5019550 * 2 ^ 59
def prefixEnd_5019550 : Nat := 4983230072969 + 3 ^ 40 * 5019550 * 2
def baseEnd_5019550 : Nat := 2577441819275941221240517

theorem tailTrace_5019550 : CollatzResearch.WordTrace tailWord_5019550 prefixEnd_5019550 2577441819275941221240517 := by
  unfold tailWord_5019550
  simp only [CollatzResearch.WordTrace]
  refine ⟨22884753620629386966786013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122052019310023397156192069 22884753620629386966786013)
  ·
    refine ⟨8581782607736020112544755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22884753620629386966786013 8581782607736020112544755)
    ·
      refine ⟨12872673911604030168817133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8581782607736020112544755 12872673911604030168817133)
      ·
        refine ⟨4827252716851511313306425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12872673911604030168817133 4827252716851511313306425)
        ·
          refine ⟨3620439537638633484979819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4827252716851511313306425 3620439537638633484979819)
          ·
            refine ⟨5430659306457950227469729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3620439537638633484979819 5430659306457950227469729)
            ·
              refine ⟨4072994479843462670602297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5430659306457950227469729 4072994479843462670602297)
              ·
                refine ⟨3054745859882597002951723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4072994479843462670602297 3054745859882597002951723)
                ·
                  refine ⟨4582118789823895504427585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3054745859882597002951723 4582118789823895504427585)
                  ·
                    refine ⟨3436589092367921628320689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4582118789823895504427585 3436589092367921628320689)
                    ·
                      refine ⟨2577441819275941221240517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3436589092367921628320689 2577441819275941221240517)
                      ·
                        rfl

theorem cell23_5019550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_5019550 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019550 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019550 prefixEnd_5019550 := by exact prefixLift 5019550
  have htrace : WordTrace (prefixWord ++ tailWord_5019550) baseStart_5019550 baseEnd_5019550 := by
    simpa [prefixWord, tailWord_5019550, baseEnd_5019550] using wordTrace_append hprefix tailTrace_5019550
  have hstable : (prefixWord ++ tailWord_5019550).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019550).length < 2 ^ (prefixWord ++ tailWord_5019550).sum := by decide
  have hdescent : baseEnd_5019550 < baseStart_5019550 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019571 : List Nat := [1, 1, 1, 2, 3, 1, 5, 1, 2, 3, 3]
def baseStart_5019571 : Nat := 118140960795 + 5019571 * 2 ^ 59
def prefixEnd_5019571 : Nat := 4983230072969 + 3 ^ 40 * 5019571 * 2
def baseEnd_5019571 : Nat := 2577452602369685639077919

theorem tailTrace_5019571 : CollatzResearch.WordTrace tailWord_5019571 prefixEnd_5019571 2577452602369685639077919 := by
  unfold tailWord_5019571
  simp only [CollatzResearch.WordTrace]
  refine ⟨183078794897959016320802567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122052529931972677547201711 183078794897959016320802567)
  ·
    refine ⟨274618192346938524481203851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183078794897959016320802567 274618192346938524481203851)
    ·
      refine ⟨411927288520407786721805777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274618192346938524481203851 411927288520407786721805777)
      ·
        refine ⟨308945466390305840041354333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 411927288520407786721805777 308945466390305840041354333)
        ·
          refine ⟨115854549896364690015507875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 308945466390305840041354333 115854549896364690015507875)
          ·
            refine ⟨173781824844547035023261813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115854549896364690015507875 173781824844547035023261813)
            ·
              refine ⟨16292046079176284533430795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 173781824844547035023261813 16292046079176284533430795)
              ·
                refine ⟨24438069118764426800146193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16292046079176284533430795 24438069118764426800146193)
                ·
                  refine ⟨18328551839073320100109645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24438069118764426800146193 18328551839073320100109645)
                  ·
                    refine ⟨6873206939652495037541117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18328551839073320100109645 6873206939652495037541117)
                    ·
                      refine ⟨2577452602369685639077919, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6873206939652495037541117 2577452602369685639077919)
                      ·
                        rfl

theorem cell23_5019571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3, 3].length) (baseStart_5019571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019571 prefixEnd_5019571 := by exact prefixLift 5019571
  have htrace : WordTrace (prefixWord ++ tailWord_5019571) baseStart_5019571 baseEnd_5019571 := by
    simpa [prefixWord, tailWord_5019571, baseEnd_5019571] using wordTrace_append hprefix tailTrace_5019571
  have hstable : (prefixWord ++ tailWord_5019571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019571).length < 2 ^ (prefixWord ++ tailWord_5019571).sum := by decide
  have hdescent : baseEnd_5019571 < baseStart_5019571 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019606 : List Nat := [5, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2]
def baseStart_5019606 : Nat := 118140960795 + 5019606 * 2 ^ 59
def prefixEnd_5019606 : Nat := 4983230072969 + 3 ^ 40 * 5019606 * 2
def baseEnd_5019606 : Nat := 2577470574192593002140259

theorem tailTrace_5019606 : CollatzResearch.WordTrace tailWord_5019606 prefixEnd_5019606 2577470574192593002140259 := by
  unfold tailWord_5019606
  simp only [CollatzResearch.WordTrace]
  refine ⟨11442504465802013581145417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122053380968554811532217781 11442504465802013581145417)
  ·
    refine ⟨8581878349351510185859063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11442504465802013581145417 8581878349351510185859063)
    ·
      refine ⟨12872817524027265278788595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8581878349351510185859063 12872817524027265278788595)
      ·
        refine ⟨19309226286040897918182893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12872817524027265278788595 19309226286040897918182893)
        ·
          refine ⟨7240959857265336719318585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19309226286040897918182893 7240959857265336719318585)
          ·
            refine ⟨5430719892949002539488939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7240959857265336719318585 5430719892949002539488939)
            ·
              refine ⟨8146079839423503809233409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5430719892949002539488939 8146079839423503809233409)
              ·
                refine ⟨6109559879567627856925057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8146079839423503809233409 6109559879567627856925057)
                ·
                  refine ⟨4582169909675720892693793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6109559879567627856925057 4582169909675720892693793)
                  ·
                    refine ⟨3436627432256790669520345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4582169909675720892693793 3436627432256790669520345)
                    ·
                      refine ⟨2577470574192593002140259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3436627432256790669520345 2577470574192593002140259)
                      ·
                        rfl

theorem cell23_5019606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 2, 1, 2, 2, 2, 2].length) (baseStart_5019606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019606 prefixEnd_5019606 := by exact prefixLift 5019606
  have htrace : WordTrace (prefixWord ++ tailWord_5019606) baseStart_5019606 baseEnd_5019606 := by
    simpa [prefixWord, tailWord_5019606, baseEnd_5019606] using wordTrace_append hprefix tailTrace_5019606
  have hstable : (prefixWord ++ tailWord_5019606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019606).length < 2 ^ (prefixWord ++ tailWord_5019606).sum := by decide
  have hdescent : baseEnd_5019606 < baseStart_5019606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019612 : List Nat := [2, 2, 6, 1, 1, 1, 2, 1, 7]
def baseStart_5019612 : Nat := 118140960795 + 5019612 * 2 ^ 59
def prefixEnd_5019612 : Nat := 4983230072969 + 3 ^ 40 * 5019612 * 2
def baseEnd_5019612 : Nat := 286385961675168886518359

theorem tailTrace_5019612 : CollatzResearch.WordTrace tailWord_5019612 prefixEnd_5019612 286385961675168886518359 := by
  unfold tailWord_5019612
  simp only [CollatzResearch.WordTrace]
  refine ⟨91540145145405240161522545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122053526860540320215363393 91540145145405240161522545)
  ·
    refine ⟨68655108859053930121141909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91540145145405240161522545 68655108859053930121141909)
    ·
      refine ⟨3218208227768152974428527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68655108859053930121141909 3218208227768152974428527)
      ·
        refine ⟨4827312341652229461642791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3218208227768152974428527 4827312341652229461642791)
        ·
          refine ⟨7240968512478344192464187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4827312341652229461642791 7240968512478344192464187)
          ·
            refine ⟨10861452768717516288696281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7240968512478344192464187 10861452768717516288696281)
            ·
              refine ⟨8146089576538137216522211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10861452768717516288696281 8146089576538137216522211)
              ·
                refine ⟨12219134364807205824783317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8146089576538137216522211 12219134364807205824783317)
                ·
                  refine ⟨286385961675168886518359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12219134364807205824783317 286385961675168886518359)
                  ·
                    rfl

theorem cell23_5019612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 1, 7].length) (baseStart_5019612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019612 prefixEnd_5019612 := by exact prefixLift 5019612
  have htrace : WordTrace (prefixWord ++ tailWord_5019612) baseStart_5019612 baseEnd_5019612 := by
    simpa [prefixWord, tailWord_5019612, baseEnd_5019612] using wordTrace_append hprefix tailTrace_5019612
  have hstable : (prefixWord ++ tailWord_5019612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019612).length < 2 ^ (prefixWord ++ tailWord_5019612).sum := by decide
  have hdescent : baseEnd_5019612 < baseStart_5019612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019631 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 3, 4, 3]
def baseStart_5019631 : Nat := 118140960795 + 5019631 * 2 ^ 59
def prefixEnd_5019631 : Nat := 4983230072969 + 3 ^ 40 * 5019631 * 2
def baseEnd_5019631 : Nat := 2577483411208955404327643

theorem tailTrace_5019631 : CollatzResearch.WordTrace tailWord_5019631 prefixEnd_5019631 2577483411208955404327643 := by
  unfold tailWord_5019631
  simp only [CollatzResearch.WordTrace]
  refine ⟨183080983277741646567986747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122053988851827764378657831 183080983277741646567986747)
  ·
    refine ⟨274621474916612469851980121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183080983277741646567986747 274621474916612469851980121)
    ·
      refine ⟨205966106187459352388985091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274621474916612469851980121 205966106187459352388985091)
      ·
        refine ⟨308949159281189028583477637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205966106187459352388985091 308949159281189028583477637)
        ·
          refine ⟨57927967365222942859402057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 308949159281189028583477637 57927967365222942859402057)
          ·
            refine ⟨43445975523917207144551543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57927967365222942859402057 43445975523917207144551543)
            ·
              refine ⟨65168963285875810716827315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43445975523917207144551543 65168963285875810716827315)
              ·
                refine ⟨97753444928813716075240973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65168963285875810716827315 97753444928813716075240973)
                ·
                  refine ⟨36657541848305143528215365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97753444928813716075240973 36657541848305143528215365)
                  ·
                    refine ⟨6873289096557214411540381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36657541848305143528215365 6873289096557214411540381)
                    ·
                      refine ⟨2577483411208955404327643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6873289096557214411540381 2577483411208955404327643)
                      ·
                        rfl

theorem cell23_5019631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4, 3].length) (baseStart_5019631 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019631 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019631 prefixEnd_5019631 := by exact prefixLift 5019631
  have htrace : WordTrace (prefixWord ++ tailWord_5019631) baseStart_5019631 baseEnd_5019631 := by
    simpa [prefixWord, tailWord_5019631, baseEnd_5019631] using wordTrace_append hprefix tailTrace_5019631
  have hstable : (prefixWord ++ tailWord_5019631).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019631).length < 2 ^ (prefixWord ++ tailWord_5019631).sum := by decide
  have hdescent : baseEnd_5019631 < baseStart_5019631 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019672 : List Nat := [2, 1, 2, 3, 2, 1, 5, 2, 1, 4]
def baseStart_5019672 : Nat := 118140960795 + 5019672 * 2 ^ 59
def prefixEnd_5019672 : Nat := 4983230072969 + 3 ^ 40 * 5019672 * 2
def baseEnd_5019672 : Nat := 859168154638596581304985

theorem tailTrace_5019672 : CollatzResearch.WordTrace tailWord_5019672 prefixEnd_5019672 859168154638596581304985 := by
  unfold tailWord_5019672
  simp only [CollatzResearch.WordTrace]
  refine ⟨91541239335296555285114635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122054985780395407046819513 91541239335296555285114635)
  ·
    refine ⟨137311859002944832927671953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91541239335296555285114635 137311859002944832927671953)
    ·
      refine ⟨102983894252208624695753965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137311859002944832927671953 102983894252208624695753965)
      ·
        refine ⟨38618960344578234260907737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102983894252208624695753965 38618960344578234260907737)
        ·
          refine ⟨28964220258433675695680803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38618960344578234260907737 28964220258433675695680803)
          ·
            refine ⟨43446330387650513543521205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28964220258433675695680803 43446330387650513543521205)
            ·
              refine ⟨4073093473842235644705113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43446330387650513543521205 4073093473842235644705113)
              ·
                refine ⟨3054820105381676733528835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4073093473842235644705113 3054820105381676733528835)
                ·
                  refine ⟨4582230158072515100293253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3054820105381676733528835 4582230158072515100293253)
                  ·
                    refine ⟨859168154638596581304985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4582230158072515100293253 859168154638596581304985)
                    ·
                      rfl

theorem cell23_5019672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 1, 5, 2, 1, 4].length) (baseStart_5019672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019672 prefixEnd_5019672 := by exact prefixLift 5019672
  have htrace : WordTrace (prefixWord ++ tailWord_5019672) baseStart_5019672 baseEnd_5019672 := by
    simpa [prefixWord, tailWord_5019672, baseEnd_5019672] using wordTrace_append hprefix tailTrace_5019672
  have hstable : (prefixWord ++ tailWord_5019672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019672).length < 2 ^ (prefixWord ++ tailWord_5019672).sum := by decide
  have hdescent : baseEnd_5019672 < baseStart_5019672 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019685 : List Nat := [1, 3, 1, 2, 2, 5, 2, 1, 6]
def baseStart_5019685 : Nat := 118140960795 + 5019685 * 2 ^ 59
def prefixEnd_5019685 : Nat := 4983230072969 + 3 ^ 40 * 5019685 * 2
def baseEnd_5019685 : Nat := 286390126573810910339155

theorem tailTrace_5019685 : CollatzResearch.WordTrace tailWord_5019685 prefixEnd_5019685 286390126573810910339155 := by
  unfold tailWord_5019685
  simp only [CollatzResearch.WordTrace]
  refine ⟨183082952819546013790452509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122055301879697342526968339 183082952819546013790452509)
  ·
    refine ⟨68656107307329755171419691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183082952819546013790452509 68656107307329755171419691)
    ·
      refine ⟨102984160960994632757129537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68656107307329755171419691 102984160960994632757129537)
      ·
        refine ⟨77238120720745974567847153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102984160960994632757129537 77238120720745974567847153)
        ·
          refine ⟨57928590540559480925885365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77238120720745974567847153 57928590540559480925885365)
          ·
            refine ⟨5430805363177451336801753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57928590540559480925885365 5430805363177451336801753)
            ·
              refine ⟨4073104022383088502601315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5430805363177451336801753 4073104022383088502601315)
              ·
                refine ⟨6109656033574632753901973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4073104022383088502601315 6109656033574632753901973)
                ·
                  refine ⟨286390126573810910339155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6109656033574632753901973 286390126573810910339155)
                  ·
                    rfl

theorem cell23_5019685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 5, 2, 1, 6].length) (baseStart_5019685 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019685 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019685 prefixEnd_5019685 := by exact prefixLift 5019685
  have htrace : WordTrace (prefixWord ++ tailWord_5019685) baseStart_5019685 baseEnd_5019685 := by
    simpa [prefixWord, tailWord_5019685, baseEnd_5019685] using wordTrace_append hprefix tailTrace_5019685
  have hstable : (prefixWord ++ tailWord_5019685).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019685).length < 2 ^ (prefixWord ++ tailWord_5019685).sum := by decide
  have hdescent : baseEnd_5019685 < baseStart_5019685 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019698 : List Nat := [3, 2, 1, 1, 2, 4, 1, 1, 3, 5]
def baseStart_5019698 : Nat := 118140960795 + 5019698 * 2 ^ 59
def prefixEnd_5019698 : Nat := 4983230072969 + 3 ^ 40 * 5019698 * 2
def baseEnd_5019698 : Nat := 859172604804268880729945

theorem tailTrace_5019698 : CollatzResearch.WordTrace tailWord_5019698 prefixEnd_5019698 859172604804268880729945 := by
  unfold tailWord_5019698
  simp only [CollatzResearch.WordTrace]
  refine ⟨45770856742124729252668937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122055617978999278007117165 45770856742124729252668937)
  ·
    refine ⟨34328142556593546939501703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45770856742124729252668937 34328142556593546939501703)
    ·
      refine ⟨51492213834890320409252555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34328142556593546939501703 51492213834890320409252555)
      ·
        refine ⟨77238320752335480613878833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51492213834890320409252555 77238320752335480613878833)
        ·
          refine ⟨57928740564251610460409125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77238320752335480613878833 57928740564251610460409125)
          ·
            refine ⟨10861638855797176961326711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57928740564251610460409125 10861638855797176961326711)
            ·
              refine ⟨16292458283695765441990067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10861638855797176961326711 16292458283695765441990067)
              ·
                refine ⟨24438687425543648162985101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16292458283695765441990067 24438687425543648162985101)
                ·
                  refine ⟨9164507784578868061119413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24438687425543648162985101 9164507784578868061119413)
                  ·
                    refine ⟨859172604804268880729945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9164507784578868061119413 859172604804268880729945)
                    ·
                      rfl

theorem cell23_5019698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 1, 3, 5].length) (baseStart_5019698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019698 prefixEnd_5019698 := by exact prefixLift 5019698
  have htrace : WordTrace (prefixWord ++ tailWord_5019698) baseStart_5019698 baseEnd_5019698 := by
    simpa [prefixWord, tailWord_5019698, baseEnd_5019698] using wordTrace_append hprefix tailTrace_5019698
  have hstable : (prefixWord ++ tailWord_5019698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019698).length < 2 ^ (prefixWord ++ tailWord_5019698).sum := by decide
  have hdescent : baseEnd_5019698 < baseStart_5019698 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019711 : List Nat := [1, 1, 2, 2, 3, 1, 3, 1, 3, 6]
def baseStart_5019711 : Nat := 118140960795 + 5019711 * 2 ^ 59
def prefixEnd_5019711 : Nat := 4983230072969 + 3 ^ 40 * 5019711 * 2
def baseEnd_5019711 : Nat := 859174829887105030442425

theorem tailTrace_5019711 : CollatzResearch.WordTrace tailWord_5019711 prefixEnd_5019711 859174829887105030442425 := by
  unfold tailWord_5019711
  simp only [CollatzResearch.WordTrace]
  refine ⟨183083901117451820230898987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122055934078301213487265991 183083901117451820230898987)
  ·
    refine ⟨274625851676177730346348481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183083901117451820230898987 274625851676177730346348481)
    ·
      refine ⟨205969388757133297759761361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274625851676177730346348481 205969388757133297759761361)
      ·
        refine ⟨154477041567849973319821021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205969388757133297759761361 154477041567849973319821021)
        ·
          refine ⟨57928890587943739994932883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154477041567849973319821021 57928890587943739994932883)
          ·
            refine ⟨86893335881915609992399325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57928890587943739994932883 86893335881915609992399325)
            ·
              refine ⟨32585000955718353747149747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86893335881915609992399325 32585000955718353747149747)
              ·
                refine ⟨48877501433577530620724621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32585000955718353747149747 48877501433577530620724621)
                ·
                  refine ⟨18329063037591573982771733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48877501433577530620724621 18329063037591573982771733)
                  ·
                    refine ⟨859174829887105030442425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18329063037591573982771733 859174829887105030442425)
                    ·
                      rfl

theorem cell23_5019711_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 3, 1, 3, 6].length) (baseStart_5019711 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019711 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019711 prefixEnd_5019711 := by exact prefixLift 5019711
  have htrace : WordTrace (prefixWord ++ tailWord_5019711) baseStart_5019711 baseEnd_5019711 := by
    simpa [prefixWord, tailWord_5019711, baseEnd_5019711] using wordTrace_append hprefix tailTrace_5019711
  have hstable : (prefixWord ++ tailWord_5019711).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019711).length < 2 ^ (prefixWord ++ tailWord_5019711).sum := by decide
  have hdescent : baseEnd_5019711 < baseStart_5019711 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019711) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019738 : List Nat := [3, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3]
def baseStart_5019738 : Nat := 118140960795 + 5019738 * 2 ^ 59
def prefixEnd_5019738 : Nat := 4983230072969 + 3 ^ 40 * 5019738 * 2
def baseEnd_5019738 : Nat := 2577538353638986485689651

theorem tailTrace_5019738 : CollatzResearch.WordTrace tailWord_5019738 prefixEnd_5019738 2577538353638986485689651 := by
  unfold tailWord_5019738
  simp only [CollatzResearch.WordTrace]
  refine ⟨45771221472088500960532967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122056590592236002561421245 45771221472088500960532967)
  ·
    refine ⟨68656832208132751440799451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45771221472088500960532967 68656832208132751440799451)
    ·
      refine ⟨102985248312199127161199177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68656832208132751440799451 102985248312199127161199177)
      ·
        refine ⟨77238936234149345370899383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102985248312199127161199177 77238936234149345370899383)
        ·
          refine ⟨115858404351224018056349075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77238936234149345370899383 115858404351224018056349075)
          ·
            refine ⟨173787606526836027084523613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115858404351224018056349075 173787606526836027084523613)
            ·
              refine ⟨65170352447563510156696355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173787606526836027084523613 65170352447563510156696355)
              ·
                refine ⟨97755528671345265235044533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65170352447563510156696355 97755528671345265235044533)
                ·
                  refine ⟨9164580812938618615785425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97755528671345265235044533 9164580812938618615785425)
                  ·
                    refine ⟨6873435609703963961839069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9164580812938618615785425 6873435609703963961839069)
                    ·
                      refine ⟨2577538353638986485689651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6873435609703963961839069 2577538353638986485689651)
                      ·
                        rfl

theorem cell23_5019738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 3, 1, 5, 2, 3].length) (baseStart_5019738 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019738 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019738 prefixEnd_5019738 := by exact prefixLift 5019738
  have htrace : WordTrace (prefixWord ++ tailWord_5019738) baseStart_5019738 baseEnd_5019738 := by
    simpa [prefixWord, tailWord_5019738, baseEnd_5019738] using wordTrace_append hprefix tailTrace_5019738
  have hstable : (prefixWord ++ tailWord_5019738).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019738).length < 2 ^ (prefixWord ++ tailWord_5019738).sum := by decide
  have hdescent : baseEnd_5019738 < baseStart_5019738 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019748 : List Nat := [2, 3, 1, 1, 2, 1, 3, 3, 1, 2, 4]
def baseStart_5019748 : Nat := 118140960795 + 5019748 * 2 ^ 59
def prefixEnd_5019748 : Nat := 4983230072969 + 3 ^ 40 * 5019748 * 2
def baseEnd_5019748 : Nat := 2577543488445531446564605

theorem tailTrace_5019748 : CollatzResearch.WordTrace tailWord_5019748 prefixEnd_5019748 2577543488445531446564605 := by
  unfold tailWord_5019748
  simp only [CollatzResearch.WordTrace]
  refine ⟨91542625309158887774997949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122056833745545183699997265 91542625309158887774997949)
  ·
    refine ⟨34328484490934582915624231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91542625309158887774997949 34328484490934582915624231)
    ·
      refine ⟨51492726736401874373436347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34328484490934582915624231 51492726736401874373436347)
      ·
        refine ⟨77239090104602811560154521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51492726736401874373436347 77239090104602811560154521)
        ·
          refine ⟨57929317578452108670115891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77239090104602811560154521 57929317578452108670115891)
          ·
            refine ⟨86893976367678163005173837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57929317578452108670115891 86893976367678163005173837)
            ·
              refine ⟨32585241137879311126940189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86893976367678163005173837 32585241137879311126940189)
              ·
                refine ⟨12219465426704741672602571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32585241137879311126940189 12219465426704741672602571)
                ·
                  refine ⟨18329198140057112508903857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12219465426704741672602571 18329198140057112508903857)
                  ·
                    refine ⟨13746898605042834381677893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18329198140057112508903857 13746898605042834381677893)
                    ·
                      refine ⟨2577543488445531446564605, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13746898605042834381677893 2577543488445531446564605)
                      ·
                        rfl

theorem cell23_5019748_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 3, 1, 2, 4].length) (baseStart_5019748 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019748 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019748 prefixEnd_5019748 := by exact prefixLift 5019748
  have htrace : WordTrace (prefixWord ++ tailWord_5019748) baseStart_5019748 baseEnd_5019748 := by
    simpa [prefixWord, tailWord_5019748, baseEnd_5019748] using wordTrace_append hprefix tailTrace_5019748
  have hstable : (prefixWord ++ tailWord_5019748).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019748).length < 2 ^ (prefixWord ++ tailWord_5019748).sum := by decide
  have hdescent : baseEnd_5019748 < baseStart_5019748 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019748) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019769 : List Nat := [1, 2, 1, 3, 4, 1, 1, 5, 1, 2, 2]
def baseStart_5019769 : Nat := 118140960795 + 5019769 * 2 ^ 59
def prefixEnd_5019769 : Nat := 4983230072969 + 3 ^ 40 * 5019769 * 2
def baseEnd_5019769 : Nat := 2577554271539275864402009

theorem tailTrace_5019769 : CollatzResearch.WordTrace tailWord_5019769 prefixEnd_5019769 2577554271539275864402009 := by
  unfold tailWord_5019769
  simp only [CollatzResearch.WordTrace]
  refine ⟨183086016551241696136510361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122057344367494464091006907 183086016551241696136510361)
  ·
    refine ⟨137314512413431272102382771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183086016551241696136510361 137314512413431272102382771)
    ·
      refine ⟨205971768620146908153574157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137314512413431272102382771 205971768620146908153574157)
      ·
        refine ⟨77239413232555090557590309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205971768620146908153574157 77239413232555090557590309)
        ·
          refine ⟨14482389981104079479548183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77239413232555090557590309 14482389981104079479548183)
          ·
            refine ⟨21723584971656119219322275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14482389981104079479548183 21723584971656119219322275)
            ·
              refine ⟨32585377457484178828983413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21723584971656119219322275 32585377457484178828983413)
              ·
                refine ⟨3054879136639141765217195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32585377457484178828983413 3054879136639141765217195)
                ·
                  refine ⟨4582318704958712647825793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3054879136639141765217195 4582318704958712647825793)
                  ·
                    refine ⟨3436739028719034485869345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4582318704958712647825793 3436739028719034485869345)
                    ·
                      refine ⟨2577554271539275864402009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3436739028719034485869345 2577554271539275864402009)
                      ·
                        rfl

theorem cell23_5019769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 1, 1, 5, 1, 2, 2].length) (baseStart_5019769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019769 prefixEnd_5019769 := by exact prefixLift 5019769
  have htrace : WordTrace (prefixWord ++ tailWord_5019769) baseStart_5019769 baseEnd_5019769 := by
    simpa [prefixWord, tailWord_5019769, baseEnd_5019769] using wordTrace_append hprefix tailTrace_5019769
  have hstable : (prefixWord ++ tailWord_5019769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019769).length < 2 ^ (prefixWord ++ tailWord_5019769).sum := by decide
  have hdescent : baseEnd_5019769 < baseStart_5019769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019772 : List Nat := [2, 2, 2, 1, 1, 4, 4, 1, 1, 2, 3]
def baseStart_5019772 : Nat := 118140960795 + 5019772 * 2 ^ 59
def prefixEnd_5019772 : Nat := 4983230072969 + 3 ^ 40 * 5019772 * 2
def baseEnd_5019772 : Nat := 2577555811981239352664495

theorem tailTrace_5019772 : CollatzResearch.WordTrace tailWord_5019772 prefixEnd_5019772 2577555811981239352664495 := by
  unfold tailWord_5019772
  simp only [CollatzResearch.WordTrace]
  refine ⟨91543062985115413824434785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122057417313487218432579713 91543062985115413824434785)
  ·
    refine ⟨68657297238836560368326089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91543062985115413824434785 68657297238836560368326089)
    ·
      refine ⟨51492972929127420276244567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68657297238836560368326089 51492972929127420276244567)
      ·
        refine ⟨77239459393691130414366851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51492972929127420276244567 77239459393691130414366851)
        ·
          refine ⟨115859189090536695621550277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77239459393691130414366851 115859189090536695621550277)
          ·
            refine ⟨21723597954475630429040677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115859189090536695621550277 21723597954475630429040677)
            ·
              refine ⟨4073174616464180705445127, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21723597954475630429040677 4073174616464180705445127)
              ·
                refine ⟨6109761924696271058167691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4073174616464180705445127 6109761924696271058167691)
                ·
                  refine ⟨9164642887044406587251537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6109761924696271058167691 9164642887044406587251537)
                  ·
                    refine ⟨6873482165283304940438653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9164642887044406587251537 6873482165283304940438653)
                    ·
                      refine ⟨2577555811981239352664495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6873482165283304940438653 2577555811981239352664495)
                      ·
                        rfl

theorem cell23_5019772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 4, 1, 1, 2, 3].length) (baseStart_5019772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019772 prefixEnd_5019772 := by exact prefixLift 5019772
  have htrace : WordTrace (prefixWord ++ tailWord_5019772) baseStart_5019772 baseEnd_5019772 := by
    simpa [prefixWord, tailWord_5019772, baseEnd_5019772] using wordTrace_append hprefix tailTrace_5019772
  have hstable : (prefixWord ++ tailWord_5019772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019772).length < 2 ^ (prefixWord ++ tailWord_5019772).sum := by decide
  have hdescent : baseEnd_5019772 < baseStart_5019772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019785 : List Nat := [1, 2, 1, 1, 4, 2, 3, 1, 4, 1, 3]
def baseStart_5019785 : Nat := 118140960795 + 5019785 * 2 ^ 59
def prefixEnd_5019785 : Nat := 4983230072969 + 3 ^ 40 * 5019785 * 2
def baseEnd_5019785 : Nat := 2577562487229747801801935

theorem tailTrace_5019785 : CollatzResearch.WordTrace tailWord_5019785 prefixEnd_5019785 2577562487229747801801935 := by
  unfold tailWord_5019785
  simp only [CollatzResearch.WordTrace]
  refine ⟨183086600119183730869092809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122057733412789153912728539 183086600119183730869092809)
  ·
    refine ⟨137314950089387798151819607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183086600119183730869092809 137314950089387798151819607)
    ·
      refine ⟨205972425134081697227729411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137314950089387798151819607 205972425134081697227729411)
      ·
        refine ⟨308958637701122545841594117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205972425134081697227729411 308958637701122545841594117)
        ·
          refine ⟨57929744568960477345298897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 308958637701122545841594117 57929744568960477345298897)
          ·
            refine ⟨43447308426720358008974173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57929744568960477345298897 43447308426720358008974173)
            ·
              refine ⟨16292740660020134253365315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43447308426720358008974173 16292740660020134253365315)
              ·
                refine ⟨24439110990030201380047973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16292740660020134253365315 24439110990030201380047973)
                ·
                  refine ⟨4582333310630662758758995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24439110990030201380047973 4582333310630662758758995)
                  ·
                    refine ⟨6873499965945994138138493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4582333310630662758758995 6873499965945994138138493)
                    ·
                      refine ⟨2577562487229747801801935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6873499965945994138138493 2577562487229747801801935)
                      ·
                        rfl

theorem cell23_5019785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 3, 1, 4, 1, 3].length) (baseStart_5019785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019785 prefixEnd_5019785 := by exact prefixLift 5019785
  have htrace : WordTrace (prefixWord ++ tailWord_5019785) baseStart_5019785 baseEnd_5019785 := by
    simpa [prefixWord, tailWord_5019785, baseEnd_5019785] using wordTrace_append hprefix tailTrace_5019785
  have hstable : (prefixWord ++ tailWord_5019785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019785).length < 2 ^ (prefixWord ++ tailWord_5019785).sum := by decide
  have hdescent : baseEnd_5019785 < baseStart_5019785 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019796 : List Nat := [2, 4, 2, 3, 1, 1, 3, 1, 2, 4]
def baseStart_5019796 : Nat := 118140960795 + 5019796 * 2 ^ 59
def prefixEnd_5019796 : Nat := 4983230072969 + 3 ^ 40 * 5019796 * 2
def baseEnd_5019796 : Nat := 859189378505649086254795

theorem tailTrace_5019796 : CollatzResearch.WordTrace tailWord_5019796 prefixEnd_5019796 859189378505649086254795 := by
  unfold tailWord_5019796
  simp only [CollatzResearch.WordTrace]
  refine ⟨91543500661071939873871621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122058000881429253165162161 91543500661071939873871621)
  ·
    refine ⟨17164406373950988726350929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91543500661071939873871621 17164406373950988726350929)
    ·
      refine ⟨12873304780463241544763197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17164406373950988726350929 12873304780463241544763197)
      ·
        refine ⟨4827489292673715579286199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12873304780463241544763197 4827489292673715579286199)
        ·
          refine ⟨7241233939010573368929299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4827489292673715579286199 7241233939010573368929299)
          ·
            refine ⟨10861850908515860053393949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7241233939010573368929299 10861850908515860053393949)
            ·
              refine ⟨4073194090693447520022731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10861850908515860053393949 4073194090693447520022731)
              ·
                refine ⟨6109791136040171280034097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4073194090693447520022731 6109791136040171280034097)
                ·
                  refine ⟨4582343352030128460025573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6109791136040171280034097 4582343352030128460025573)
                  ·
                    refine ⟨859189378505649086254795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4582343352030128460025573 859189378505649086254795)
                    ·
                      rfl

theorem cell23_5019796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 1, 1, 3, 1, 2, 4].length) (baseStart_5019796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019796 prefixEnd_5019796 := by exact prefixLift 5019796
  have htrace : WordTrace (prefixWord ++ tailWord_5019796) baseStart_5019796 baseEnd_5019796 := by
    simpa [prefixWord, tailWord_5019796, baseEnd_5019796] using wordTrace_append hprefix tailTrace_5019796
  have hstable : (prefixWord ++ tailWord_5019796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019796).length < 2 ^ (prefixWord ++ tailWord_5019796).sum := by decide
  have hdescent : baseEnd_5019796 < baseStart_5019796 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019862 : List Nat := [5, 2, 1, 2, 1, 1, 1, 2, 2, 1, 5]
def baseStart_5019862 : Nat := 118140960795 + 5019862 * 2 ^ 59
def prefixEnd_5019862 : Nat := 4983230072969 + 3 ^ 40 * 5019862 * 2
def baseEnd_5019862 : Nat := 2577602025240144000539081

theorem tailTrace_5019862 : CollatzResearch.WordTrace tailWord_5019862 prefixEnd_5019862 2577602025240144000539081 := by
  unfold tailWord_5019862
  simp only [CollatzResearch.WordTrace]
  refine ⟨11443088033744048313727865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122059605693269848679763893 11443088033744048313727865)
  ·
    refine ⟨8582316025308036235295899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11443088033744048313727865 8582316025308036235295899)
    ·
      refine ⟨12873474037962054352943849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8582316025308036235295899 12873474037962054352943849)
      ·
        refine ⟨9655105528471540764707887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12873474037962054352943849 9655105528471540764707887)
        ·
          refine ⟨14482658292707311147061831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9655105528471540764707887 14482658292707311147061831)
          ·
            refine ⟨21723987439060966720592747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14482658292707311147061831 21723987439060966720592747)
            ·
              refine ⟨32585981158591450080889121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21723987439060966720592747 32585981158591450080889121)
              ·
                refine ⟨24439485868943587560666841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32585981158591450080889121 24439485868943587560666841)
                ·
                  refine ⟨18329614401707690670500131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24439485868943587560666841 18329614401707690670500131)
                  ·
                    refine ⟨27494421602561536005750197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18329614401707690670500131 27494421602561536005750197)
                    ·
                      refine ⟨2577602025240144000539081, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27494421602561536005750197 2577602025240144000539081)
                      ·
                        rfl

theorem cell23_5019862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_5019862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019862 prefixEnd_5019862 := by exact prefixLift 5019862
  have htrace : WordTrace (prefixWord ++ tailWord_5019862) baseStart_5019862 baseEnd_5019862 := by
    simpa [prefixWord, tailWord_5019862, baseEnd_5019862] using wordTrace_append hprefix tailTrace_5019862
  have hstable : (prefixWord ++ tailWord_5019862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019862).length < 2 ^ (prefixWord ++ tailWord_5019862).sum := by decide
  have hdescent : baseEnd_5019862 < baseStart_5019862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019902 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2]
def baseStart_5019902 : Nat := 118140960795 + 5019902 * 2 ^ 59
def prefixEnd_5019902 : Nat := 4983230072969 + 3 ^ 40 * 5019902 * 2
def baseEnd_5019902 : Nat := 2577622564466323844038897

theorem tailTrace_5019902 : CollatzResearch.WordTrace tailWord_5019902 prefixEnd_5019902 2577622564466323844038897 := by
  unfold tailWord_5019902
  simp only [CollatzResearch.WordTrace]
  refine ⟨22886358432469982481387745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122060578306506573234067973 22886358432469982481387745)
  ·
    refine ⟨17164768824352486861040809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22886358432469982481387745 17164768824352486861040809)
    ·
      refine ⟨12873576618264365145780607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17164768824352486861040809 12873576618264365145780607)
      ·
        refine ⟨19310364927396547718670911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12873576618264365145780607 19310364927396547718670911)
        ·
          refine ⟨28965547391094821578006367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19310364927396547718670911 28965547391094821578006367)
          ·
            refine ⟨43448321086642232367009551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28965547391094821578006367 43448321086642232367009551)
            ·
              refine ⟨65172481629963348550514327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43448321086642232367009551 65172481629963348550514327)
              ·
                refine ⟨97758722444945022825771491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65172481629963348550514327 97758722444945022825771491)
                ·
                  refine ⟨146638083667417534238657237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97758722444945022825771491 146638083667417534238657237)
                  ·
                    refine ⟨3436830085955098458718529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 146638083667417534238657237 3436830085955098458718529)
                    ·
                      refine ⟨2577622564466323844038897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3436830085955098458718529 2577622564466323844038897)
                      ·
                        rfl

theorem cell23_5019902_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 1, 7, 2].length) (baseStart_5019902 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019902 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019902 prefixEnd_5019902 := by exact prefixLift 5019902
  have htrace : WordTrace (prefixWord ++ tailWord_5019902) baseStart_5019902 baseEnd_5019902 := by
    simpa [prefixWord, tailWord_5019902, baseEnd_5019902] using wordTrace_append hprefix tailTrace_5019902
  have hstable : (prefixWord ++ tailWord_5019902).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019902).length < 2 ^ (prefixWord ++ tailWord_5019902).sum := by decide
  have hdescent : baseEnd_5019902 < baseStart_5019902 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019902) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019925 : List Nat := [1, 3, 2, 1, 2, 1, 3, 1, 5, 4]
def baseStart_5019925 : Nat := 118140960795 + 5019925 * 2 ^ 59
def prefixEnd_5019925 : Nat := 4983230072969 + 3 ^ 40 * 5019925 * 2
def baseEnd_5019925 : Nat := 859211458173792418017097

theorem tailTrace_5019925 : CollatzResearch.WordTrace tailWord_5019925 prefixEnd_5019925 859211458173792418017097 := by
  unfold tailWord_5019925
  simp only [CollatzResearch.WordTrace]
  refine ⟨183091706338676534779189229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122061137559117689852792819 183091706338676534779189229)
  ·
    refine ⟨68659389877003700542195961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183091706338676534779189229 68659389877003700542195961)
    ·
      refine ⟨51494542407752775406646971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68659389877003700542195961 51494542407752775406646971)
      ·
        refine ⟨77241813611629163109970457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51494542407752775406646971 77241813611629163109970457)
        ·
          refine ⟨57931360208721872332477843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77241813611629163109970457 57931360208721872332477843)
          ·
            refine ⟨86897040313082808498716765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57931360208721872332477843 86897040313082808498716765)
            ·
              refine ⟨32586390117406053187018787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86897040313082808498716765 32586390117406053187018787)
              ·
                refine ⟨48879585176109079780528181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32586390117406053187018787 48879585176109079780528181)
                ·
                  refine ⟨4582461110260226229424517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48879585176109079780528181 4582461110260226229424517)
                  ·
                    refine ⟨859211458173792418017097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4582461110260226229424517 859211458173792418017097)
                    ·
                      rfl

theorem cell23_5019925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 3, 1, 5, 4].length) (baseStart_5019925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019925 prefixEnd_5019925 := by exact prefixLift 5019925
  have htrace : WordTrace (prefixWord ++ tailWord_5019925) baseStart_5019925 baseEnd_5019925 := by
    simpa [prefixWord, tailWord_5019925, baseEnd_5019925] using wordTrace_append hprefix tailTrace_5019925
  have hstable : (prefixWord ++ tailWord_5019925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019925).length < 2 ^ (prefixWord ++ tailWord_5019925).sum := by decide
  have hdescent : baseEnd_5019925 < baseStart_5019925 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019968 : List Nat := [2, 1, 1, 2, 2, 1, 2, 1, 2, 9]
def baseStart_5019968 : Nat := 118140960795 + 5019968 * 2 ^ 59
def prefixEnd_5019968 : Nat := 4983230072969 + 3 ^ 40 * 5019968 * 2
def baseEnd_5019968 : Nat := 859218818063173528604531

theorem tailTrace_5019968 : CollatzResearch.WordTrace tailWord_5019968 prefixEnd_5019968 859218818063173528604531 := by
  unfold tailWord_5019968
  simp only [CollatzResearch.WordTrace]
  refine ⟨91546637338760376561502279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122062183118347168748669705 91546637338760376561502279)
  ·
    refine ⟨137319956008140564842253419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91546637338760376561502279 137319956008140564842253419)
    ·
      refine ⟨205979934012210847263380129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137319956008140564842253419 205979934012210847263380129)
      ·
        refine ⟨154484950509158135447535097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 205979934012210847263380129 154484950509158135447535097)
        ·
          refine ⟨115863712881868601585651323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154484950509158135447535097 115863712881868601585651323)
          ·
            refine ⟨173795569322802902378476985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115863712881868601585651323 173795569322802902378476985)
            ·
              refine ⟨130346676992102176783857739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173795569322802902378476985 130346676992102176783857739)
              ·
                refine ⟨195520015488153265175786609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130346676992102176783857739 195520015488153265175786609)
                ·
                  refine ⟨146640011616114948881839957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195520015488153265175786609 146640011616114948881839957)
                  ·
                    refine ⟨859218818063173528604531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 146640011616114948881839957 859218818063173528604531)
                    ·
                      rfl

theorem cell23_5019968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 9].length) (baseStart_5019968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019968 prefixEnd_5019968 := by exact prefixLift 5019968
  have htrace : WordTrace (prefixWord ++ tailWord_5019968) baseStart_5019968 baseEnd_5019968 := by
    simpa [prefixWord, tailWord_5019968, baseEnd_5019968] using wordTrace_append hprefix tailTrace_5019968
  have hstable : (prefixWord ++ tailWord_5019968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019968).length < 2 ^ (prefixWord ++ tailWord_5019968).sum := by decide
  have hdescent : baseEnd_5019968 < baseStart_5019968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5019982 : List Nat := [4, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3]
def baseStart_5019982 : Nat := 118140960795 + 5019982 * 2 ^ 59
def prefixEnd_5019982 : Nat := 4983230072969 + 3 ^ 40 * 5019982 * 2
def baseEnd_5019982 : Nat := 2577663642918683531038529

theorem tailTrace_5019982 : CollatzResearch.WordTrace tailWord_5019982 prefixEnd_5019982 2577663642918683531038529 := by
  unfold tailWord_5019982
  simp only [CollatzResearch.WordTrace]
  refine ⟨22886723162433754189251775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122062523532980022342676133 22886723162433754189251775)
  ·
    refine ⟨34330084743650631283877663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22886723162433754189251775 34330084743650631283877663)
    ·
      refine ⟨51495127115475946925816495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34330084743650631283877663 51495127115475946925816495)
      ·
        refine ⟨77242690673213920388724743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51495127115475946925816495 77242690673213920388724743)
        ·
          refine ⟨115864036009820880583087115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77242690673213920388724743 115864036009820880583087115)
          ·
            refine ⟨173796054014731320874630673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115864036009820880583087115 173796054014731320874630673)
            ·
              refine ⟨130347040511048490655973005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173796054014731320874630673 130347040511048490655973005)
              ·
                refine ⟨48880140191643183995989877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130347040511048490655973005 48880140191643183995989877)
                ·
                  refine ⟨4582513142966548499624051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48880140191643183995989877 4582513142966548499624051)
                  ·
                    refine ⟨6873769714449822749436077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4582513142966548499624051 6873769714449822749436077)
                    ·
                      refine ⟨2577663642918683531038529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6873769714449822749436077 2577663642918683531038529)
                      ·
                        rfl

theorem cell23_5019982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 3, 5, 1, 3].length) (baseStart_5019982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5019982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5019982 prefixEnd_5019982 := by exact prefixLift 5019982
  have htrace : WordTrace (prefixWord ++ tailWord_5019982) baseStart_5019982 baseEnd_5019982 := by
    simpa [prefixWord, tailWord_5019982, baseEnd_5019982] using wordTrace_append hprefix tailTrace_5019982
  have hstable : (prefixWord ++ tailWord_5019982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5019982).length < 2 ^ (prefixWord ++ tailWord_5019982).sum := by decide
  have hdescent : baseEnd_5019982 < baseStart_5019982 := by decide
  rcases family_descends (prefixWord ++ tailWord_5019982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020025 : List Nat := [1, 2, 1, 3, 2, 1, 1, 1, 2, 6, 3]
def baseStart_5020025 : Nat := 118140960795 + 5020025 * 2 ^ 59
def prefixEnd_5020025 : Nat := 4983230072969 + 3 ^ 40 * 5020025 * 2
def baseEnd_5020025 : Nat := 2577685722586826862800831

theorem tailTrace_5020025 : CollatzResearch.WordTrace tailWord_5020025 prefixEnd_5020025 2577685722586826862800831 := by
  unfold tailWord_5020025
  simp only [CollatzResearch.WordTrace]
  refine ⟨183095353638314251857829529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122063569092209501238553019 183095353638314251857829529)
  ·
    refine ⟨137321515228735688893372147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183095353638314251857829529 137321515228735688893372147)
    ·
      refine ⟨205982272843103533340058221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137321515228735688893372147 205982272843103533340058221)
      ·
        refine ⟨77243352316163825002521833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 205982272843103533340058221 77243352316163825002521833)
        ·
          refine ⟨57932514237122868751891375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77243352316163825002521833 57932514237122868751891375)
          ·
            refine ⟨86898771355684303127837063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57932514237122868751891375 86898771355684303127837063)
            ·
              refine ⟨130348157033526454691755595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86898771355684303127837063 130348157033526454691755595)
              ·
                refine ⟨195522235550289682037633393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130348157033526454691755595 195522235550289682037633393)
                ·
                  refine ⟨146641676662717261528225045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195522235550289682037633393 146641676662717261528225045)
                  ·
                    refine ⟨6873828593564871634135549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 146641676662717261528225045 6873828593564871634135549)
                    ·
                      refine ⟨2577685722586826862800831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6873828593564871634135549 2577685722586826862800831)
                      ·
                        rfl

theorem cell23_5020025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 6, 3].length) (baseStart_5020025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020025 prefixEnd_5020025 := by exact prefixLift 5020025
  have htrace : WordTrace (prefixWord ++ tailWord_5020025) baseStart_5020025 baseEnd_5020025 := by
    simpa [prefixWord, tailWord_5020025, baseEnd_5020025] using wordTrace_append hprefix tailTrace_5020025
  have hstable : (prefixWord ++ tailWord_5020025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020025).length < 2 ^ (prefixWord ++ tailWord_5020025).sum := by decide
  have hdescent : baseEnd_5020025 < baseStart_5020025 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020039 : List Nat := [1, 1, 4, 2, 2, 1, 2, 1, 5, 2, 2]
def baseStart_5020039 : Nat := 118140960795 + 5020039 * 2 ^ 59
def prefixEnd_5020039 : Nat := 4983230072969 + 3 ^ 40 * 5020039 * 2
def baseEnd_5020039 : Nat := 2577692911315989808025767

theorem tailTrace_5020039 : CollatzResearch.WordTrace tailWord_5020039 prefixEnd_5020039 2577692911315989808025767 := by
  unfold tailWord_5020039
  simp only [CollatzResearch.WordTrace]
  refine ⟨183095864260263532248839171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122063909506842354832559447 183095864260263532248839171)
  ·
    refine ⟨274643796390395298373258757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183095864260263532248839171 274643796390395298373258757)
    ·
      refine ⟨51495711823199118444986017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 274643796390395298373258757 51495711823199118444986017)
      ·
        refine ⟨38621783867399338833739513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51495711823199118444986017 38621783867399338833739513)
        ·
          refine ⟨28966337900549504125304635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38621783867399338833739513 28966337900549504125304635)
          ·
            refine ⟨43449506850824256187956953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28966337900549504125304635 43449506850824256187956953)
            ·
              refine ⟨32587130138118192140967715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43449506850824256187956953 32587130138118192140967715)
              ·
                refine ⟨48880695207177288211451573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32587130138118192140967715 48880695207177288211451573)
                ·
                  refine ⟨4582565175672870769823585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48880695207177288211451573 4582565175672870769823585)
                  ·
                    refine ⟨3436923881754653077367689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4582565175672870769823585 3436923881754653077367689)
                    ·
                      refine ⟨2577692911315989808025767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3436923881754653077367689 2577692911315989808025767)
                      ·
                        rfl

theorem cell23_5020039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5, 2, 2].length) (baseStart_5020039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020039 prefixEnd_5020039 := by exact prefixLift 5020039
  have htrace : WordTrace (prefixWord ++ tailWord_5020039) baseStart_5020039 baseEnd_5020039 := by
    simpa [prefixWord, tailWord_5020039, baseEnd_5020039] using wordTrace_append hprefix tailTrace_5020039
  have hstable : (prefixWord ++ tailWord_5020039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020039).length < 2 ^ (prefixWord ++ tailWord_5020039).sum := by decide
  have hdescent : baseEnd_5020039 < baseStart_5020039 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020056 : List Nat := [2, 1, 2, 5, 1, 2, 3, 1, 1, 1, 4]
def baseStart_5020056 : Nat := 118140960795 + 5020056 * 2 ^ 59
def prefixEnd_5020056 : Nat := 4983230072969 + 3 ^ 40 * 5020056 * 2
def baseEnd_5020056 : Nat := 2577701640487116241513189

theorem tailTrace_5020056 : CollatzResearch.WordTrace tailWord_5020056 prefixEnd_5020056 2577701640487116241513189 := by
  unfold tailWord_5020056
  simp only [CollatzResearch.WordTrace]
  refine ⟨91548242150600972076104011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122064322867467962768138681 91548242150600972076104011)
  ·
    refine ⟨137322363225901458114156017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91548242150600972076104011 137322363225901458114156017)
    ·
      refine ⟨102991772419426093585617013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137322363225901458114156017 102991772419426093585617013)
      ·
        refine ⟨9655478664321196273651595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102991772419426093585617013 9655478664321196273651595)
        ·
          refine ⟨14483217996481794410477393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9655478664321196273651595 14483217996481794410477393)
          ·
            refine ⟨10862413497361345807858045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14483217996481794410477393 10862413497361345807858045)
            ·
              refine ⟨4073405061510504677946767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10862413497361345807858045 4073405061510504677946767)
              ·
                refine ⟨6110107592265757016920151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4073405061510504677946767 6110107592265757016920151)
                ·
                  refine ⟨9165161388398635525380227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6110107592265757016920151 9165161388398635525380227)
                  ·
                    refine ⟨13747742082597953288070341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9165161388398635525380227 13747742082597953288070341)
                    ·
                      refine ⟨2577701640487116241513189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13747742082597953288070341 2577701640487116241513189)
                      ·
                        rfl

theorem cell23_5020056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_5020056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020056 prefixEnd_5020056 := by exact prefixLift 5020056
  have htrace : WordTrace (prefixWord ++ tailWord_5020056) baseStart_5020056 baseEnd_5020056 := by
    simpa [prefixWord, tailWord_5020056, baseEnd_5020056] using wordTrace_append hprefix tailTrace_5020056
  have hstable : (prefixWord ++ tailWord_5020056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020056).length < 2 ^ (prefixWord ++ tailWord_5020056).sum := by decide
  have hdescent : baseEnd_5020056 < baseStart_5020056 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020062 : List Nat := [4, 3, 1, 2, 1, 12]
def baseStart_5020062 : Nat := 118140960795 + 5020062 * 2 ^ 59
def prefixEnd_5020062 : Nat := 4983230072969 + 3 ^ 40 * 5020062 * 2
def baseEnd_5020062 : Nat := 10607838359551618181227

theorem tailTrace_5020062 : CollatzResearch.WordTrace tailWord_5020062 prefixEnd_5020062 10607838359551618181227 := by
  unfold tailWord_5020062
  simp only [CollatzResearch.WordTrace]
  refine ⟨22887087892397525897115805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122064468759453471451284293 22887087892397525897115805)
  ·
    refine ⟨8582657959649072211418427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22887087892397525897115805 8582657959649072211418427)
    ·
      refine ⟨12873986939473608317127641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8582657959649072211418427 12873986939473608317127641)
      ·
        refine ⟨9655490204605206237845731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12873986939473608317127641 9655490204605206237845731)
        ·
          refine ⟨14483235306907809356768597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9655490204605206237845731 14483235306907809356768597)
          ·
            refine ⟨10607838359551618181227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 14483235306907809356768597 10607838359551618181227)
            ·
              rfl

theorem cell23_5020062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 1, 12].length) (baseStart_5020062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020062 prefixEnd_5020062 := by exact prefixLift 5020062
  have htrace : WordTrace (prefixWord ++ tailWord_5020062) baseStart_5020062 baseEnd_5020062 := by
    simpa [prefixWord, tailWord_5020062, baseEnd_5020062] using wordTrace_append hprefix tailTrace_5020062
  have hstable : (prefixWord ++ tailWord_5020062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020062).length < 2 ^ (prefixWord ++ tailWord_5020062).sum := by decide
  have hdescent : baseEnd_5020062 < baseStart_5020062 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020089 : List Nat := [1, 2, 1, 4, 3, 2, 2, 1, 1, 3, 3]
def baseStart_5020089 : Nat := 118140960795 + 5020089 * 2 ^ 59
def prefixEnd_5020089 : Nat := 4983230072969 + 3 ^ 40 * 5020089 * 2
def baseEnd_5020089 : Nat := 2577718585348714612400537

theorem tailTrace_5020089 : CollatzResearch.WordTrace tailWord_5020089 prefixEnd_5020089 2577718585348714612400537 := by
  unfold tailWord_5020089
  simp only [CollatzResearch.WordTrace]
  refine ⟨183097687910082390788159321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122065125273388260525439547 183097687910082390788159321)
  ·
    refine ⟨137323265932561793091119491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183097687910082390788159321 137323265932561793091119491)
    ·
      refine ⟨205984898898842689636679237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137323265932561793091119491 205984898898842689636679237)
      ·
        refine ⟨38622168543533004306877357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 205984898898842689636679237 38622168543533004306877357)
        ·
          refine ⟨14483313203824876615079009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38622168543533004306877357 14483313203824876615079009)
          ·
            refine ⟨10862484902868657461309257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14483313203824876615079009 10862484902868657461309257)
            ·
              refine ⟨8146863677151493095981943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10862484902868657461309257 8146863677151493095981943)
              ·
                refine ⟨12220295515727239643972915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8146863677151493095981943 12220295515727239643972915)
                ·
                  refine ⟨18330443273590859465959373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12220295515727239643972915 18330443273590859465959373)
                  ·
                    refine ⟨6873916227596572299734765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18330443273590859465959373 6873916227596572299734765)
                    ·
                      refine ⟨2577718585348714612400537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6873916227596572299734765 2577718585348714612400537)
                      ·
                        rfl

theorem cell23_5020089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 1, 1, 3, 3].length) (baseStart_5020089 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020089 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020089 prefixEnd_5020089 := by exact prefixLift 5020089
  have htrace : WordTrace (prefixWord ++ tailWord_5020089) baseStart_5020089 baseEnd_5020089 := by
    simpa [prefixWord, tailWord_5020089, baseEnd_5020089] using wordTrace_append hprefix tailTrace_5020089
  have hstable : (prefixWord ++ tailWord_5020089).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020089).length < 2 ^ (prefixWord ++ tailWord_5020089).sum := by decide
  have hdescent : baseEnd_5020089 < baseStart_5020089 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020099 : List Nat := [1, 1, 1, 3, 1, 1, 3, 6, 1, 3, 2]
def baseStart_5020099 : Nat := 118140960795 + 5020099 * 2 ^ 59
def prefixEnd_5020099 : Nat := 4983230072969 + 3 ^ 40 * 5020099 * 2
def baseEnd_5020099 : Nat := 2577723720155259573275491

theorem tailTrace_5020099 : CollatzResearch.WordTrace tailWord_5020099 prefixEnd_5020099 2577723720155259573275491 := by
  unfold tailWord_5020099
  simp only [CollatzResearch.WordTrace]
  refine ⟨183098052640046162496023351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122065368426697441664015567 183098052640046162496023351)
  ·
    refine ⟨274647078960069243744035027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183098052640046162496023351 274647078960069243744035027)
    ·
      refine ⟨411970618440103865616052541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274647078960069243744035027 411970618440103865616052541)
      ·
        refine ⟨154488981915038949606019703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 411970618440103865616052541 154488981915038949606019703)
        ·
          refine ⟨231733472872558424409029555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154488981915038949606019703 231733472872558424409029555)
          ·
            refine ⟨347600209308837636613544333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231733472872558424409029555 347600209308837636613544333)
            ·
              refine ⟨130350078490814113730079125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 347600209308837636613544333 130350078490814113730079125)
              ·
                refine ⟨6110159929256911581097459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 130350078490814113730079125 6110159929256911581097459)
                ·
                  refine ⟨9165239893885367371646189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6110159929256911581097459 9165239893885367371646189)
                  ·
                    refine ⟨3436964960207012764367321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9165239893885367371646189 3436964960207012764367321)
                    ·
                      refine ⟨2577723720155259573275491, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3436964960207012764367321 2577723720155259573275491)
                      ·
                        rfl

theorem cell23_5020099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 3, 2].length) (baseStart_5020099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020099 prefixEnd_5020099 := by exact prefixLift 5020099
  have htrace : WordTrace (prefixWord ++ tailWord_5020099) baseStart_5020099 baseEnd_5020099 := by
    simpa [prefixWord, tailWord_5020099, baseEnd_5020099] using wordTrace_append hprefix tailTrace_5020099
  have hstable : (prefixWord ++ tailWord_5020099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020099).length < 2 ^ (prefixWord ++ tailWord_5020099).sum := by decide
  have hdescent : baseEnd_5020099 < baseStart_5020099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020115 : List Nat := [1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 5]
def baseStart_5020115 : Nat := 118140960795 + 5020115 * 2 ^ 59
def prefixEnd_5020115 : Nat := 4983230072969 + 3 ^ 40 * 5020115 * 2
def baseEnd_5020115 : Nat := 2577731935845731510675417

theorem tailTrace_5020115 : CollatzResearch.WordTrace tailWord_5020115 prefixEnd_5020115 2577731935845731510675417 := by
  unfold tailWord_5020115
  simp only [CollatzResearch.WordTrace]
  refine ⟨183098636207988197228605799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122065757471992131485737199 183098636207988197228605799)
  ·
    refine ⟨274647954311982295842908699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183098636207988197228605799 274647954311982295842908699)
    ·
      refine ⟨411971931467973443764363049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274647954311982295842908699 411971931467973443764363049)
      ·
        refine ⟨308978948600980082823272287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 411971931467973443764363049 308978948600980082823272287)
        ·
          refine ⟨463468422901470124234908431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308978948600980082823272287 463468422901470124234908431)
          ·
            refine ⟨695202634352205186352362647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463468422901470124234908431 695202634352205186352362647)
            ·
              refine ⟨1042803951528307779528543971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 695202634352205186352362647 1042803951528307779528543971)
              ·
                refine ⟨1564205927292461669292815957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1042803951528307779528543971 1564205927292461669292815957)
                ·
                  refine ⟨18330538210458535187025187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1564205927292461669292815957 18330538210458535187025187)
                  ·
                    refine ⟨27495807315687802780537781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18330538210458535187025187 27495807315687802780537781)
                    ·
                      refine ⟨2577731935845731510675417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27495807315687802780537781 2577731935845731510675417)
                      ·
                        rfl

theorem cell23_5020115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 1, 5].length) (baseStart_5020115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020115 prefixEnd_5020115 := by exact prefixLift 5020115
  have htrace : WordTrace (prefixWord ++ tailWord_5020115) baseStart_5020115 baseEnd_5020115 := by
    simpa [prefixWord, tailWord_5020115, baseEnd_5020115] using wordTrace_append hprefix tailTrace_5020115
  have hstable : (prefixWord ++ tailWord_5020115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020115).length < 2 ^ (prefixWord ++ tailWord_5020115).sum := by decide
  have hdescent : baseEnd_5020115 < baseStart_5020115 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020239 : List Nat := [1, 1, 2, 1, 1, 2, 6, 2, 2, 2, 3]
def baseStart_5020239 : Nat := 118140960795 + 5020239 * 2 ^ 59
def prefixEnd_5020239 : Nat := 4983230072969 + 3 ^ 40 * 5020239 * 2
def baseEnd_5020239 : Nat := 2577795607446889025524847

theorem tailTrace_5020239 : CollatzResearch.WordTrace tailWord_5020239 prefixEnd_5020239 2577795607446889025524847 := by
  unfold tailWord_5020239
  simp only [CollatzResearch.WordTrace]
  refine ⟨183103158859538966406119771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122068772573025977604079847 183103158859538966406119771)
  ·
    refine ⟨274654738289308449609179657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183103158859538966406119771 274654738289308449609179657)
    ·
      refine ⟨205991053716981337206884743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274654738289308449609179657 205991053716981337206884743)
      ·
        refine ⟨308986580575472005810327115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 205991053716981337206884743 308986580575472005810327115)
        ·
          refine ⟨463479870863208008715490673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 308986580575472005810327115 463479870863208008715490673)
          ·
            refine ⟨347609903147406006536618005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 463479870863208008715490673 347609903147406006536618005)
            ·
              refine ⟨16294214210034656556403969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 347609903147406006536618005 16294214210034656556403969)
              ·
                refine ⟨12220660657525992417302977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16294214210034656556403969 12220660657525992417302977)
                ·
                  refine ⟨9165495493144494312977233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12220660657525992417302977 9165495493144494312977233)
                  ·
                    refine ⟨6874121619858370734732925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9165495493144494312977233 6874121619858370734732925)
                    ·
                      refine ⟨2577795607446889025524847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6874121619858370734732925 2577795607446889025524847)
                      ·
                        rfl

theorem cell23_5020239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 6, 2, 2, 2, 3].length) (baseStart_5020239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020239 prefixEnd_5020239 := by exact prefixLift 5020239
  have htrace : WordTrace (prefixWord ++ tailWord_5020239) baseStart_5020239 baseEnd_5020239 := by
    simpa [prefixWord, tailWord_5020239, baseEnd_5020239] using wordTrace_append hprefix tailTrace_5020239
  have hstable : (prefixWord ++ tailWord_5020239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020239).length < 2 ^ (prefixWord ++ tailWord_5020239).sum := by decide
  have hdescent : baseEnd_5020239 < baseStart_5020239 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020346 : List Nat := [3, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3]
def baseStart_5020346 : Nat := 118140960795 + 5020346 * 2 ^ 59
def prefixEnd_5020346 : Nat := 4983230072969 + 3 ^ 40 * 5020346 * 2
def baseEnd_5020346 : Nat := 2577850549876920106886855

theorem tailTrace_5020346 : CollatzResearch.WordTrace tailWord_5020346 prefixEnd_5020346 2577850549876920106886855 := by
  unfold tailWord_5020346
  simp only [CollatzResearch.WordTrace]
  refine ⟨45776765367537830920066223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122071374313434215786843261 45776765367537830920066223)
  ·
    refine ⟨68665148051306746380099335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45776765367537830920066223 68665148051306746380099335)
    ·
      refine ⟨102997722076960119570149003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68665148051306746380099335 102997722076960119570149003)
      ·
        refine ⟨154496583115440179355223505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102997722076960119570149003 154496583115440179355223505)
        ·
          refine ⟨115872437336580134516417629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154496583115440179355223505 115872437336580134516417629)
          ·
            refine ⟨43452164001217550443656611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115872437336580134516417629 43452164001217550443656611)
            ·
              refine ⟨65178246001826325665484917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43452164001217550443656611 65178246001826325665484917)
              ·
                refine ⟨6110460562671218031139211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65178246001826325665484917 6110460562671218031139211)
                ·
                  refine ⟨9165690844006827046708817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6110460562671218031139211 9165690844006827046708817)
                  ·
                    refine ⟨6874268133005120285031613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9165690844006827046708817 6874268133005120285031613)
                    ·
                      refine ⟨2577850549876920106886855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6874268133005120285031613 2577850549876920106886855)
                      ·
                        rfl

theorem cell23_5020346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 5, 1, 2, 3].length) (baseStart_5020346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020346 prefixEnd_5020346 := by exact prefixLift 5020346
  have htrace : WordTrace (prefixWord ++ tailWord_5020346) baseStart_5020346 baseEnd_5020346 := by
    simpa [prefixWord, tailWord_5020346, baseEnd_5020346] using wordTrace_append hprefix tailTrace_5020346
  have hstable : (prefixWord ++ tailWord_5020346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020346).length < 2 ^ (prefixWord ++ tailWord_5020346).sum := by decide
  have hdescent : baseEnd_5020346 < baseStart_5020346 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020349 : List Nat := [1, 4, 1, 2, 1, 5, 9]
def baseStart_5020349 : Nat := 118140960795 + 5020349 * 2 ^ 59
def prefixEnd_5020349 : Nat := 4983230072969 + 3 ^ 40 * 5020349 * 2
def baseEnd_5020349 : Nat := 31825334448381278952461

theorem tailTrace_5020349 : CollatzResearch.WordTrace tailWord_5020349 prefixEnd_5020349 31825334448381278952461 := by
  unfold tailWord_5020349
  simp only [CollatzResearch.WordTrace]
  refine ⟨183107170889140455192624101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122071447259426970128416067 183107170889140455192624101)
  ·
    refine ⟨34332594541713835348617019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183107170889140455192624101 34332594541713835348617019)
    ·
      refine ⟨51498891812570753022925529, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34332594541713835348617019 51498891812570753022925529)
      ·
        refine ⟨38624168859428064767194147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51498891812570753022925529 38624168859428064767194147)
        ·
          refine ⟨57936253289142097150791221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38624168859428064767194147 57936253289142097150791221)
          ·
            refine ⟨5431523745857071607886677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57936253289142097150791221 5431523745857071607886677)
            ·
              refine ⟨31825334448381278952461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 5431523745857071607886677 31825334448381278952461)
              ·
                rfl

theorem cell23_5020349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 9].length) (baseStart_5020349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020349 prefixEnd_5020349 := by exact prefixLift 5020349
  have htrace : WordTrace (prefixWord ++ tailWord_5020349) baseStart_5020349 baseEnd_5020349 := by
    simpa [prefixWord, tailWord_5020349, baseEnd_5020349] using wordTrace_append hprefix tailTrace_5020349
  have hstable : (prefixWord ++ tailWord_5020349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020349).length < 2 ^ (prefixWord ++ tailWord_5020349).sum := by decide
  have hdescent : baseEnd_5020349 < baseStart_5020349 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020359 : List Nat := [1, 1, 4, 1, 1, 1, 2, 1, 5, 3, 3]
def baseStart_5020359 : Nat := 118140960795 + 5020359 * 2 ^ 59
def prefixEnd_5020359 : Nat := 4983230072969 + 3 ^ 40 * 5020359 * 2
def baseEnd_5020359 : Nat := 2577857225125428556024295

theorem tailTrace_5020359 : CollatzResearch.WordTrace tailWord_5020359 prefixEnd_5020359 2577857225125428556024295 := by
  unfold tailWord_5020359
  simp only [CollatzResearch.WordTrace]
  refine ⟨183107535619104226900488131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122071690412736151266992087 183107535619104226900488131)
  ·
    refine ⟨274661303428656340350732197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183107535619104226900488131 274661303428656340350732197)
    ·
      refine ⟨51498994392873063815762287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 274661303428656340350732197 51498994392873063815762287)
      ·
        refine ⟨77248491589309595723643431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51498994392873063815762287 77248491589309595723643431)
        ·
          refine ⟨115872737383964393585465147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77248491589309595723643431 115872737383964393585465147)
          ·
            refine ⟨173809106075946590378197721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115872737383964393585465147 173809106075946590378197721)
            ·
              refine ⟨130356829556959942783648291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173809106075946590378197721 130356829556959942783648291)
              ·
                refine ⟨195535244335439914175472437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130356829556959942783648291 195535244335439914175472437)
                ·
                  refine ⟨18331429156447491953950541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 195535244335439914175472437 18331429156447491953950541)
                  ·
                    refine ⟨6874285933667809482731453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18331429156447491953950541 6874285933667809482731453)
                    ·
                      refine ⟨2577857225125428556024295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6874285933667809482731453 2577857225125428556024295)
                      ·
                        rfl

theorem cell23_5020359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 5, 3, 3].length) (baseStart_5020359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020359 prefixEnd_5020359 := by exact prefixLift 5020359
  have htrace : WordTrace (prefixWord ++ tailWord_5020359) baseStart_5020359 baseEnd_5020359 := by
    simpa [prefixWord, tailWord_5020359, baseEnd_5020359] using wordTrace_append hprefix tailTrace_5020359
  have hstable : (prefixWord ++ tailWord_5020359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020359).length < 2 ^ (prefixWord ++ tailWord_5020359).sum := by decide
  have hdescent : baseEnd_5020359 < baseStart_5020359 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020360 : List Nat := [2, 1, 3, 1, 2, 5, 1, 1, 3, 2, 2]
def baseStart_5020360 : Nat := 118140960795 + 5020360 * 2 ^ 59
def prefixEnd_5020360 : Nat := 4983230072969 + 3 ^ 40 * 5020360 * 2
def baseEnd_5020360 : Nat := 2577857738606083052111791

theorem tailTrace_5020360 : CollatzResearch.WordTrace tailWord_5020360 prefixEnd_5020360 2577857738606083052111791 := by
  unfold tailWord_5020360
  simp only [CollatzResearch.WordTrace]
  refine ⟨91553786046050302035637267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122071714728067069380849689 91553786046050302035637267)
  ·
    refine ⟨137330679069075453053455901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91553786046050302035637267 137330679069075453053455901)
    ·
      refine ⟨51499004650903294895045963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137330679069075453053455901 51499004650903294895045963)
      ·
        refine ⟨77248506976354942342568945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51499004650903294895045963 77248506976354942342568945)
        ·
          refine ⟨57936380232266206756926709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77248506976354942342568945 57936380232266206756926709)
          ·
            refine ⟨5431535646774956883461879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57936380232266206756926709 5431535646774956883461879)
            ·
              refine ⟨8147303470162435325192819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5431535646774956883461879 8147303470162435325192819)
              ·
                refine ⟨12220955205243652987789229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8147303470162435325192819 12220955205243652987789229)
                ·
                  refine ⟨4582858201966369870420961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12220955205243652987789229 4582858201966369870420961)
                  ·
                    refine ⟨3437143651474777402815721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4582858201966369870420961 3437143651474777402815721)
                    ·
                      refine ⟨2577857738606083052111791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3437143651474777402815721 2577857738606083052111791)
                      ·
                        rfl

theorem cell23_5020360_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 1, 1, 3, 2, 2].length) (baseStart_5020360 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020360 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020360 prefixEnd_5020360 := by exact prefixLift 5020360
  have htrace : WordTrace (prefixWord ++ tailWord_5020360) baseStart_5020360 baseEnd_5020360 := by
    simpa [prefixWord, tailWord_5020360, baseEnd_5020360] using wordTrace_append hprefix tailTrace_5020360
  have hstable : (prefixWord ++ tailWord_5020360).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020360).length < 2 ^ (prefixWord ++ tailWord_5020360).sum := by decide
  have hdescent : baseEnd_5020360 < baseStart_5020360 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020360) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020380 : List Nat := [2, 2, 5, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_5020380 : Nat := 118140960795 + 5020380 * 2 ^ 59
def prefixEnd_5020380 : Nat := 4983230072969 + 3 ^ 40 * 5020380 * 2
def baseEnd_5020380 : Nat := 2577868008219172973861699

theorem tailTrace_5020380 : CollatzResearch.WordTrace tailWord_5020380 prefixEnd_5020380 2577868008219172973861699 := by
  unfold tailWord_5020380
  simp only [CollatzResearch.WordTrace]
  refine ⟨91554150776014073743501297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122072201034685431658001729 91554150776014073743501297)
  ·
    refine ⟨68665613082010555307625973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91554150776014073743501297 68665613082010555307625973)
    ·
      refine ⟨6437401226438489560089935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68665613082010555307625973 6437401226438489560089935)
      ·
        refine ⟨9656101839657734340134903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6437401226438489560089935 9656101839657734340134903)
        ·
          refine ⟨14484152759486601510202355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9656101839657734340134903 14484152759486601510202355)
          ·
            refine ⟨21726229139229902265303533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14484152759486601510202355 21726229139229902265303533)
            ·
              refine ⟨8147335927211213349488825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21726229139229902265303533 8147335927211213349488825)
              ·
                refine ⟨6110501945408410012116619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8147335927211213349488825 6110501945408410012116619)
                ·
                  refine ⟨9165752918112615018174929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6110501945408410012116619 9165752918112615018174929)
                  ·
                    refine ⟨6874314688584461263631197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9165752918112615018174929 6874314688584461263631197)
                    ·
                      refine ⟨2577868008219172973861699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6874314688584461263631197 2577868008219172973861699)
                      ·
                        rfl

theorem cell23_5020380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_5020380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020380 prefixEnd_5020380 := by exact prefixLift 5020380
  have htrace : WordTrace (prefixWord ++ tailWord_5020380) baseStart_5020380 baseEnd_5020380 := by
    simpa [prefixWord, tailWord_5020380, baseEnd_5020380] using wordTrace_append hprefix tailTrace_5020380
  have hstable : (prefixWord ++ tailWord_5020380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020380).length < 2 ^ (prefixWord ++ tailWord_5020380).sum := by decide
  have hdescent : baseEnd_5020380 < baseStart_5020380 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020461 : List Nat := [1, 5, 3, 2, 2, 1, 1, 2, 2, 1, 3]
def baseStart_5020461 : Nat := 118140960795 + 5020461 * 2 ^ 59
def prefixEnd_5020461 : Nat := 4983230072969 + 3 ^ 40 * 5020461 * 2
def baseEnd_5020461 : Nat := 2577909600152187156948827

theorem tailTrace_5020461 : CollatzResearch.WordTrace tailWord_5020461 prefixEnd_5020461 2577909600152187156948827 := by
  unfold tailWord_5020461
  simp only [CollatzResearch.WordTrace]
  refine ⟨183111255864734698320701237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122074170576489798880467491 183111255864734698320701237)
  ·
    refine ⟨17166680237318877967565741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 183111255864734698320701237 17166680237318877967565741)
    ·
      refine ⟨6437505088994579237837153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17166680237318877967565741 6437505088994579237837153)
      ·
        refine ⟨4828128816745934428377865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6437505088994579237837153 4828128816745934428377865)
        ·
          refine ⟨3621096612559450821283399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4828128816745934428377865 3621096612559450821283399)
          ·
            refine ⟨5431644918839176231925099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3621096612559450821283399 5431644918839176231925099)
            ·
              refine ⟨8147467378258764347887649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5431644918839176231925099 8147467378258764347887649)
              ·
                refine ⟨6110600533694073260915737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8147467378258764347887649 6110600533694073260915737)
                ·
                  refine ⟨4582950400270554945686803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6110600533694073260915737 4582950400270554945686803)
                  ·
                    refine ⟨6874425600405832418530205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4582950400270554945686803 6874425600405832418530205)
                    ·
                      refine ⟨2577909600152187156948827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6874425600405832418530205 2577909600152187156948827)
                      ·
                        rfl

theorem cell23_5020461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_5020461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020461 prefixEnd_5020461 := by exact prefixLift 5020461
  have htrace : WordTrace (prefixWord ++ tailWord_5020461) baseStart_5020461 baseEnd_5020461 := by
    simpa [prefixWord, tailWord_5020461, baseEnd_5020461] using wordTrace_append hprefix tailTrace_5020461
  have hstable : (prefixWord ++ tailWord_5020461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020461).length < 2 ^ (prefixWord ++ tailWord_5020461).sum := by decide
  have hdescent : baseEnd_5020461 < baseStart_5020461 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020466 : List Nat := [3, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3]
def baseStart_5020466 : Nat := 118140960795 + 5020466 * 2 ^ 59
def prefixEnd_5020466 : Nat := 4983230072969 + 3 ^ 40 * 5020466 * 2
def baseEnd_5020466 : Nat := 2577912167555459637386303

theorem tailTrace_5020466 : CollatzResearch.WordTrace tailWord_5020466 prefixEnd_5020466 2577912167555459637386303 := by
  unfold tailWord_5020466
  simp only [CollatzResearch.WordTrace]
  refine ⟨45777859557429146043658313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122074292153144389449755501 45777859557429146043658313)
  ·
    refine ⟨34333394668071859532743735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45777859557429146043658313 34333394668071859532743735)
    ·
      refine ⟨51500092002107789299115603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34333394668071859532743735 51500092002107789299115603)
      ·
        refine ⟨77250138003161683948673405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51500092002107789299115603 77250138003161683948673405)
        ·
          refine ⟨28968801751185631480752527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77250138003161683948673405 28968801751185631480752527)
          ·
            refine ⟨43453202626778447221128791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28968801751185631480752527 43453202626778447221128791)
            ·
              refine ⟨65179803940167670831693187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43453202626778447221128791 65179803940167670831693187)
              ·
                refine ⟨97769705910251506247539781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65179803940167670831693187 97769705910251506247539781)
                ·
                  refine ⟨18331819858172157421413709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97769705910251506247539781 18331819858172157421413709)
                  ·
                    refine ⟨6874432446814559033030141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18331819858172157421413709 6874432446814559033030141)
                    ·
                      refine ⟨2577912167555459637386303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6874432446814559033030141 2577912167555459637386303)
                      ·
                        rfl

theorem cell23_5020466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 1, 4, 3, 3].length) (baseStart_5020466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020466 prefixEnd_5020466 := by exact prefixLift 5020466
  have htrace : WordTrace (prefixWord ++ tailWord_5020466) baseStart_5020466 baseEnd_5020466 := by
    simpa [prefixWord, tailWord_5020466, baseEnd_5020466] using wordTrace_append hprefix tailTrace_5020466
  have hstable : (prefixWord ++ tailWord_5020466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020466).length < 2 ^ (prefixWord ++ tailWord_5020466).sum := by decide
  have hdescent : baseEnd_5020466 < baseStart_5020466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020467 : List Nat := [1, 1, 1, 2, 6, 3, 1, 2, 2, 2, 2]
def baseStart_5020467 : Nat := 118140960795 + 5020467 * 2 ^ 59
def prefixEnd_5020467 : Nat := 4983230072969 + 3 ^ 40 * 5020467 * 2
def baseEnd_5020467 : Nat := 2577912681036114133473799

theorem tailTrace_5020467 : CollatzResearch.WordTrace tailWord_5020467 prefixEnd_5020467 2577912681036114133473799 := by
  unfold tailWord_5020467
  simp only [CollatzResearch.WordTrace]
  refine ⟨183111474702712961345419655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122074316468475307563613103 183111474702712961345419655)
  ·
    refine ⟨274667212054069442018129483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183111474702712961345419655 274667212054069442018129483)
    ·
      refine ⟨412000818081104163027194225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274667212054069442018129483 412000818081104163027194225)
      ·
        refine ⟨309000613560828122270395669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412000818081104163027194225 309000613560828122270395669)
        ·
          refine ⟨14484403760663818231424797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 309000613560828122270395669 14484403760663818231424797)
          ·
            refine ⟨5431651410248931836784299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14484403760663818231424797 5431651410248931836784299)
            ·
              refine ⟨8147477115373397755176449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5431651410248931836784299 8147477115373397755176449)
              ·
                refine ⟨6110607836530048316382337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8147477115373397755176449 6110607836530048316382337)
                ·
                  refine ⟨4582955877397536237286753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6110607836530048316382337 4582955877397536237286753)
                  ·
                    refine ⟨3437216908048152177965065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4582955877397536237286753 3437216908048152177965065)
                    ·
                      refine ⟨2577912681036114133473799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3437216908048152177965065 2577912681036114133473799)
                      ·
                        rfl

theorem cell23_5020467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2, 2, 2].length) (baseStart_5020467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020467 prefixEnd_5020467 := by exact prefixLift 5020467
  have htrace : WordTrace (prefixWord ++ tailWord_5020467) baseStart_5020467 baseEnd_5020467 := by
    simpa [prefixWord, tailWord_5020467, baseEnd_5020467] using wordTrace_append hprefix tailTrace_5020467
  have hstable : (prefixWord ++ tailWord_5020467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020467).length < 2 ^ (prefixWord ++ tailWord_5020467).sum := by decide
  have hdescent : baseEnd_5020467 < baseStart_5020467 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020484 : List Nat := [2, 3, 4, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_5020484 : Nat := 118140960795 + 5020484 * 2 ^ 59
def prefixEnd_5020484 : Nat := 4983230072969 + 3 ^ 40 * 5020484 * 2
def baseEnd_5020484 : Nat := 2577921410207240566961221

theorem tailTrace_5020484 : CollatzResearch.WordTrace tailWord_5020484 prefixEnd_5020484 2577921410207240566961221 := by
  unfold tailWord_5020484
  simp only [CollatzResearch.WordTrace]
  refine ⟨91556047371825686624394253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122074729829100915499192337 91556047371825686624394253)
  ·
    refine ⟨34333517764434632484147845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91556047371825686624394253 34333517764434632484147845)
    ·
      refine ⟨6437534580831493590777721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34333517764434632484147845 6437534580831493590777721)
      ·
        refine ⟨4828150935623620193083291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6437534580831493590777721 4828150935623620193083291)
        ·
          refine ⟨7242226403435430289624937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4828150935623620193083291 7242226403435430289624937)
          ·
            refine ⟨5431669802576572717218703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7242226403435430289624937 5431669802576572717218703)
            ·
              refine ⟨8147504703864859075828055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5431669802576572717218703 8147504703864859075828055)
              ·
                refine ⟨12221257055797288613742083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8147504703864859075828055 12221257055797288613742083)
                ·
                  refine ⟨18331885583695932920613125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12221257055797288613742083 18331885583695932920613125)
                  ·
                    refine ⟨3437228546942987422614961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18331885583695932920613125 3437228546942987422614961)
                    ·
                      refine ⟨2577921410207240566961221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3437228546942987422614961 2577921410207240566961221)
                      ·
                        rfl

theorem cell23_5020484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_5020484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020484 prefixEnd_5020484 := by exact prefixLift 5020484
  have htrace : WordTrace (prefixWord ++ tailWord_5020484) baseStart_5020484 baseEnd_5020484 := by
    simpa [prefixWord, tailWord_5020484, baseEnd_5020484] using wordTrace_append hprefix tailTrace_5020484
  have hstable : (prefixWord ++ tailWord_5020484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020484).length < 2 ^ (prefixWord ++ tailWord_5020484).sum := by decide
  have hdescent : baseEnd_5020484 < baseStart_5020484 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020506 : List Nat := [3, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4]
def baseStart_5020506 : Nat := 118140960795 + 5020506 * 2 ^ 59
def prefixEnd_5020506 : Nat := 4983230072969 + 3 ^ 40 * 5020506 * 2
def baseEnd_5020506 : Nat := 2577932706781639480886119

theorem tailTrace_5020506 : CollatzResearch.WordTrace tailWord_5020506 prefixEnd_5020506 2577932706781639480886119 := by
  unfold tailWord_5020506
  simp only [CollatzResearch.WordTrace]
  refine ⟨45778224287392917751522343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122075264766381114004059581 45778224287392917751522343)
  ·
    refine ⟨68667336431089376627283515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45778224287392917751522343 68667336431089376627283515)
    ·
      refine ⟨103001004646634064940925273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68667336431089376627283515 103001004646634064940925273)
      ·
        refine ⟨77250753484975548705693955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103001004646634064940925273 77250753484975548705693955)
        ·
          refine ⟨115876130227463323058540933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77250753484975548705693955 115876130227463323058540933)
          ·
            refine ⟨21726774417649373073476425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115876130227463323058540933 21726774417649373073476425)
            ·
              refine ⟨16295080813237029805107319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21726774417649373073476425 16295080813237029805107319)
              ·
                refine ⟨24442621219855544707660979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16295080813237029805107319 24442621219855544707660979)
                ·
                  refine ⟨36663931829783317061491469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24442621219855544707660979 36663931829783317061491469)
                  ·
                    refine ⟨13748974436168743898059301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36663931829783317061491469 13748974436168743898059301)
                    ·
                      refine ⟨2577932706781639480886119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13748974436168743898059301 2577932706781639480886119)
                      ·
                        rfl

theorem cell23_5020506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 1, 3, 4].length) (baseStart_5020506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020506 prefixEnd_5020506 := by exact prefixLift 5020506
  have htrace : WordTrace (prefixWord ++ tailWord_5020506) baseStart_5020506 baseEnd_5020506 := by
    simpa [prefixWord, tailWord_5020506, baseEnd_5020506] using wordTrace_append hprefix tailTrace_5020506
  have hstable : (prefixWord ++ tailWord_5020506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020506).length < 2 ^ (prefixWord ++ tailWord_5020506).sum := by decide
  have hdescent : baseEnd_5020506 < baseStart_5020506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020556 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 2, 5, 3]
def baseStart_5020556 : Nat := 118140960795 + 5020556 * 2 ^ 59
def prefixEnd_5020556 : Nat := 4983230072969 + 3 ^ 40 * 5020556 * 2
def baseEnd_5020556 : Nat := 2577958380814364285260889

theorem tailTrace_5020556 : CollatzResearch.WordTrace tailWord_5020556 prefixEnd_5020556 2577958380814364285260889 := by
  unfold tailWord_5020556
  simp only [CollatzResearch.WordTrace]
  refine ⟨91557360399695264772704761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122076480532927019696939681 91557360399695264772704761)
  ·
    refine ⟨68668020299771448579528571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91557360399695264772704761 68668020299771448579528571)
    ·
      refine ⟨103002030449657172869292857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68668020299771448579528571 103002030449657172869292857)
      ·
        refine ⟨77251522837242879651969643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103002030449657172869292857 77251522837242879651969643)
        ·
          refine ⟨115877284255864319477954465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77251522837242879651969643 115877284255864319477954465)
          ·
            refine ⟨86907963191898239608465849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115877284255864319477954465 86907963191898239608465849)
            ·
              refine ⟨65180972393923679706349387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86907963191898239608465849 65180972393923679706349387)
              ·
                refine ⟨97771458590885519559524081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65180972393923679706349387 97771458590885519559524081)
                ·
                  refine ⟨73328593943164139669643061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97771458590885519559524081 73328593943164139669643061)
                  ·
                    refine ⟨6874555682171638094029037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73328593943164139669643061 6874555682171638094029037)
                    ·
                      refine ⟨2577958380814364285260889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6874555682171638094029037 2577958380814364285260889)
                      ·
                        rfl

theorem cell23_5020556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 5, 3].length) (baseStart_5020556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020556 prefixEnd_5020556 := by exact prefixLift 5020556
  have htrace : WordTrace (prefixWord ++ tailWord_5020556) baseStart_5020556 baseEnd_5020556 := by
    simpa [prefixWord, tailWord_5020556, baseEnd_5020556] using wordTrace_append hprefix tailTrace_5020556
  have hstable : (prefixWord ++ tailWord_5020556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020556).length < 2 ^ (prefixWord ++ tailWord_5020556).sum := by decide
  have hdescent : baseEnd_5020556 < baseStart_5020556 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020647 : List Nat := [1, 1, 5, 2, 2, 1, 1, 3, 3, 2, 2]
def baseStart_5020647 : Nat := 118140960795 + 5020647 * 2 ^ 59
def prefixEnd_5020647 : Nat := 4983230072969 + 3 ^ 40 * 5020647 * 2
def baseEnd_5020647 : Nat := 2578005107553923429222971

theorem tailTrace_5020647 : CollatzResearch.WordTrace tailWord_5020647 prefixEnd_5020647 2578005107553923429222971 := by
  unfold tailWord_5020647
  simp only [CollatzResearch.WordTrace]
  refine ⟨183118039842060852086972195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122078693228040568057981463 183118039842060852086972195)
  ·
    refine ⟨274677059763091278130458293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183118039842060852086972195 274677059763091278130458293)
    ·
      refine ⟨25750974352789807324730465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 274677059763091278130458293 25750974352789807324730465)
      ·
        refine ⟨19313230764592355493547849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25750974352789807324730465 19313230764592355493547849)
        ·
          refine ⟨14484923073444266620160887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19313230764592355493547849 14484923073444266620160887)
          ·
            refine ⟨21727384610166399930241331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14484923073444266620160887 21727384610166399930241331)
            ·
              refine ⟨32591076915249599895361997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21727384610166399930241331 32591076915249599895361997)
              ·
                refine ⟨12221653843218599960760749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32591076915249599895361997 12221653843218599960760749)
                ·
                  refine ⟨4583120191206974985285281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12221653843218599960760749 4583120191206974985285281)
                  ·
                    refine ⟨3437340143405231238963961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4583120191206974985285281 3437340143405231238963961)
                    ·
                      refine ⟨2578005107553923429222971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3437340143405231238963961 2578005107553923429222971)
                      ·
                        rfl

theorem cell23_5020647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 2, 1, 1, 3, 3, 2, 2].length) (baseStart_5020647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020647 prefixEnd_5020647 := by exact prefixLift 5020647
  have htrace : WordTrace (prefixWord ++ tailWord_5020647) baseStart_5020647 baseEnd_5020647 := by
    simpa [prefixWord, tailWord_5020647, baseEnd_5020647] using wordTrace_append hprefix tailTrace_5020647
  have hstable : (prefixWord ++ tailWord_5020647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020647).length < 2 ^ (prefixWord ++ tailWord_5020647).sum := by decide
  have hdescent : baseEnd_5020647 < baseStart_5020647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020657 : List Nat := [1, 2, 2, 2, 4, 2, 3, 1, 2, 4]
def baseStart_5020657 : Nat := 118140960795 + 5020657 * 2 ^ 59
def prefixEnd_5020657 : Nat := 4983230072969 + 3 ^ 40 * 5020657 * 2
def baseEnd_5020657 : Nat := 859336747453489463365975

theorem tailTrace_5020657 : CollatzResearch.WordTrace tailWord_5020657 prefixEnd_5020657 859336747453489463365975 := by
  unfold tailWord_5020657
  simp only [CollatzResearch.WordTrace]
  refine ⟨183118404572024623794836225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122078936381349749196557483 183118404572024623794836225)
  ·
    refine ⟨137338803429018467846127169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183118404572024623794836225 137338803429018467846127169)
    ·
      refine ⟨103004102571763850884595377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137338803429018467846127169 103004102571763850884595377)
      ·
        refine ⟨77253076928822888163446533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103004102571763850884595377 77253076928822888163446533)
        ·
          refine ⟨14484951924154291530646225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77253076928822888163446533 14484951924154291530646225)
          ·
            refine ⟨10863713943115718647984669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14484951924154291530646225 10863713943115718647984669)
            ·
              refine ⟨4073892728668394492994251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10863713943115718647984669 4073892728668394492994251)
              ·
                refine ⟨6110839093002591739491377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4073892728668394492994251 6110839093002591739491377)
                ·
                  refine ⟨4583129319751943804618533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6110839093002591739491377 4583129319751943804618533)
                  ·
                    refine ⟨859336747453489463365975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4583129319751943804618533 859336747453489463365975)
                    ·
                      rfl

theorem cell23_5020657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 4, 2, 3, 1, 2, 4].length) (baseStart_5020657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020657 prefixEnd_5020657 := by exact prefixLift 5020657
  have htrace : WordTrace (prefixWord ++ tailWord_5020657) baseStart_5020657 baseEnd_5020657 := by
    simpa [prefixWord, tailWord_5020657, baseEnd_5020657] using wordTrace_append hprefix tailTrace_5020657
  have hstable : (prefixWord ++ tailWord_5020657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020657).length < 2 ^ (prefixWord ++ tailWord_5020657).sum := by decide
  have hdescent : baseEnd_5020657 < baseStart_5020657 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020666 : List Nat := [3, 1, 1, 1, 1, 2, 1, 4, 2, 7]
def baseStart_5020666 : Nat := 118140960795 + 5020666 * 2 ^ 59
def prefixEnd_5020666 : Nat := 4983230072969 + 3 ^ 40 * 5020666 * 2
def baseEnd_5020666 : Nat := 859338287895452951628461

theorem tailTrace_5020666 : CollatzResearch.WordTrace tailWord_5020666 prefixEnd_5020666 859338287895452951628461 := by
  unfold tailWord_5020666
  simp only [CollatzResearch.WordTrace]
  refine ⟨45779683207248004582978463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122079155219328012221275901 45779683207248004582978463)
  ·
    refine ⟨68669524810872006874467695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45779683207248004582978463 68669524810872006874467695)
    ·
      refine ⟨103004287216308010311701543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68669524810872006874467695 103004287216308010311701543)
      ·
        refine ⟨154506430824462015467552315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103004287216308010311701543 154506430824462015467552315)
        ·
          refine ⟨231759646236693023201328473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154506430824462015467552315 231759646236693023201328473)
          ·
            refine ⟨173819734677519767400996355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231759646236693023201328473 173819734677519767400996355)
            ·
              refine ⟨260729602016279651101494533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173819734677519767400996355 260729602016279651101494533)
              ·
                refine ⟨48886800378052434581530225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 260729602016279651101494533 48886800378052434581530225)
                ·
                  refine ⟨36665100283539325936147669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48886800378052434581530225 36665100283539325936147669)
                  ·
                    refine ⟨859338287895452951628461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36665100283539325936147669 859338287895452951628461)
                    ·
                      rfl

theorem cell23_5020666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 4, 2, 7].length) (baseStart_5020666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020666 prefixEnd_5020666 := by exact prefixLift 5020666
  have htrace : WordTrace (prefixWord ++ tailWord_5020666) baseStart_5020666 baseEnd_5020666 := by
    simpa [prefixWord, tailWord_5020666, baseEnd_5020666] using wordTrace_append hprefix tailTrace_5020666
  have hstable : (prefixWord ++ tailWord_5020666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020666).length < 2 ^ (prefixWord ++ tailWord_5020666).sum := by decide
  have hdescent : baseEnd_5020666 < baseStart_5020666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020670 : List Nat := [4, 2, 2, 2, 2, 1, 1, 9]
def baseStart_5020670 : Nat := 118140960795 + 5020670 * 2 ^ 59
def prefixEnd_5020670 : Nat := 4983230072969 + 3 ^ 40 * 5020670 * 2
def baseEnd_5020670 : Nat := 95482108059591734786495

theorem tailTrace_5020670 : CollatzResearch.WordTrace tailWord_5020670 prefixEnd_5020670 95482108059591734786495 := by
  unfold tailWord_5020670
  simp only [CollatzResearch.WordTrace]
  refine ⟨22889859840122190876882433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122079252480651684676706309 22889859840122190876882433)
  ·
    refine ⟨17167394880091643157661825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22889859840122190876882433 17167394880091643157661825)
    ·
      refine ⟨12875546160068732368246369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17167394880091643157661825 12875546160068732368246369)
      ·
        refine ⟨9656659620051549276184777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12875546160068732368246369 9656659620051549276184777)
        ·
          refine ⟨7242494715038661957138583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9656659620051549276184777 7242494715038661957138583)
          ·
            refine ⟨10863742072557992935707875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7242494715038661957138583 10863742072557992935707875)
            ·
              refine ⟨16295613108836989403561813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10863742072557992935707875 16295613108836989403561813)
              ·
                refine ⟨95482108059591734786495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16295613108836989403561813 95482108059591734786495)
                ·
                  rfl

theorem cell23_5020670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 9].length) (baseStart_5020670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020670 prefixEnd_5020670 := by exact prefixLift 5020670
  have htrace : WordTrace (prefixWord ++ tailWord_5020670) baseStart_5020670 baseEnd_5020670 := by
    simpa [prefixWord, tailWord_5020670, baseEnd_5020670] using wordTrace_append hprefix tailTrace_5020670
  have hstable : (prefixWord ++ tailWord_5020670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020670).length < 2 ^ (prefixWord ++ tailWord_5020670).sum := by decide
  have hdescent : baseEnd_5020670 < baseStart_5020670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020680 : List Nat := [2, 1, 3, 2, 1, 3, 1, 2, 4, 1, 3]
def baseStart_5020680 : Nat := 118140960795 + 5020680 * 2 ^ 59
def prefixEnd_5020680 : Nat := 4983230072969 + 3 ^ 40 * 5020680 * 2
def baseEnd_5020680 : Nat := 2578022052415521800110319

theorem tailTrace_5020680 : CollatzResearch.WordTrace tailWord_5020680 prefixEnd_5020680 2578022052415521800110319 := by
  unfold tailWord_5020680
  simp only [CollatzResearch.WordTrace]
  refine ⟨91559621725470649361461747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122079495633960865815282329 91559621725470649361461747)
  ·
    refine ⟨137339432588205974042192621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91559621725470649361461747 137339432588205974042192621)
    ·
      refine ⟨51502287220577240265822233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137339432588205974042192621 51502287220577240265822233)
      ·
        refine ⟨38626715415432930199366675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51502287220577240265822233 38626715415432930199366675)
        ·
          refine ⟨57940073123149395299050013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38626715415432930199366675 57940073123149395299050013)
          ·
            refine ⟨21727527421181023237143755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57940073123149395299050013 21727527421181023237143755)
            ·
              refine ⟨32591291131771534855715633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21727527421181023237143755 32591291131771534855715633)
              ·
                refine ⟨24443468348828651141786725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32591291131771534855715633 24443468348828651141786725)
                ·
                  refine ⟨4583150315405372089085011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24443468348828651141786725 4583150315405372089085011)
                  ·
                    refine ⟨6874725473108058133627517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4583150315405372089085011 6874725473108058133627517)
                    ·
                      refine ⟨2578022052415521800110319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6874725473108058133627517 2578022052415521800110319)
                      ·
                        rfl

theorem cell23_5020680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 3, 1, 2, 4, 1, 3].length) (baseStart_5020680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020680 prefixEnd_5020680 := by exact prefixLift 5020680
  have htrace : WordTrace (prefixWord ++ tailWord_5020680) baseStart_5020680 baseEnd_5020680 := by
    simpa [prefixWord, tailWord_5020680, baseEnd_5020680] using wordTrace_append hprefix tailTrace_5020680
  have hstable : (prefixWord ++ tailWord_5020680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020680).length < 2 ^ (prefixWord ++ tailWord_5020680).sum := by decide
  have hdescent : baseEnd_5020680 < baseStart_5020680 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020714 : List Nat := [3, 1, 4, 1, 3, 1, 1, 3, 2, 1, 3]
def baseStart_5020714 : Nat := 118140960795 + 5020714 * 2 ^ 59
def prefixEnd_5020714 : Nat := 4983230072969 + 3 ^ 40 * 5020714 * 2
def baseEnd_5020714 : Nat := 2578039510757774667085163

theorem tailTrace_5020714 : CollatzResearch.WordTrace tailWord_5020714 prefixEnd_5020714 2578039510757774667085163 := by
  unfold tailWord_5020714
  simp only [CollatzResearch.WordTrace]
  refine ⟨45780120883204530632415299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122080322355212081686440797 45780120883204530632415299)
  ·
    refine ⟨68670181324806795948622949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45780120883204530632415299 68670181324806795948622949)
    ·
      refine ⟨12875658998401274240366803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68670181324806795948622949 12875658998401274240366803)
      ·
        refine ⟨19313488497601911360550205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12875658998401274240366803 19313488497601911360550205)
        ·
          refine ⟨7242558186600716760206327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19313488497601911360550205 7242558186600716760206327)
          ·
            refine ⟨10863837279901075140309491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7242558186600716760206327 10863837279901075140309491)
            ·
              refine ⟨16295755919851612710464237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10863837279901075140309491 16295755919851612710464237)
              ·
                refine ⟨6110908469944354766424089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16295755919851612710464237 6110908469944354766424089)
                ·
                  refine ⟨4583181352458266074818067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6110908469944354766424089 4583181352458266074818067)
                  ·
                    refine ⟨6874772028687399112227101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4583181352458266074818067 6874772028687399112227101)
                    ·
                      refine ⟨2578039510757774667085163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6874772028687399112227101 2578039510757774667085163)
                      ·
                        rfl

theorem cell23_5020714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 3, 1, 1, 3, 2, 1, 3].length) (baseStart_5020714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020714 prefixEnd_5020714 := by exact prefixLift 5020714
  have htrace : WordTrace (prefixWord ++ tailWord_5020714) baseStart_5020714 baseEnd_5020714 := by
    simpa [prefixWord, tailWord_5020714, baseEnd_5020714] using wordTrace_append hprefix tailTrace_5020714
  have hstable : (prefixWord ++ tailWord_5020714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020714).length < 2 ^ (prefixWord ++ tailWord_5020714).sum := by decide
  have hdescent : baseEnd_5020714 < baseStart_5020714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020720 : List Nat := [2, 1, 1, 1, 2, 4, 2, 3, 1, 4, 2]
def baseStart_5020720 : Nat := 118140960795 + 5020720 * 2 ^ 59
def prefixEnd_5020720 : Nat := 4983230072969 + 3 ^ 40 * 5020720 * 2
def baseEnd_5020720 : Nat := 2578042591641701643610135

theorem tailTrace_5020720 : CollatzResearch.WordTrace tailWord_5020720 prefixEnd_5020720 2578042591641701643610135 := by
  unfold tailWord_5020720
  simp only [CollatzResearch.WordTrace]
  refine ⟨91560351185398192777189807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122080468247197590369586409 91560351185398192777189807)
  ·
    refine ⟨137340526778097289165784711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91560351185398192777189807 137340526778097289165784711)
    ·
      refine ⟨206010790167145933748677067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137340526778097289165784711 206010790167145933748677067)
      ·
        refine ⟨309016185250718900623015601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206010790167145933748677067 309016185250718900623015601)
        ·
          refine ⟨231762138938039175467261701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309016185250718900623015601 231762138938039175467261701)
          ·
            refine ⟨43455401050882345400111569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 231762138938039175467261701 43455401050882345400111569)
            ·
              refine ⟨32591550788161759050083677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43455401050882345400111569 32591550788161759050083677)
              ·
                refine ⟨12221831545560659643781379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32591550788161759050083677 12221831545560659643781379)
                ·
                  refine ⟨18332747318340989465672069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12221831545560659643781379 18332747318340989465672069)
                  ·
                    refine ⟨3437390122188935524813513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18332747318340989465672069 3437390122188935524813513)
                    ·
                      refine ⟨2578042591641701643610135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3437390122188935524813513 2578042591641701643610135)
                      ·
                        rfl

theorem cell23_5020720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 2, 3, 1, 4, 2].length) (baseStart_5020720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020720 prefixEnd_5020720 := by exact prefixLift 5020720
  have htrace : WordTrace (prefixWord ++ tailWord_5020720) baseStart_5020720 baseEnd_5020720 := by
    simpa [prefixWord, tailWord_5020720, baseEnd_5020720] using wordTrace_append hprefix tailTrace_5020720
  have hstable : (prefixWord ++ tailWord_5020720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020720).length < 2 ^ (prefixWord ++ tailWord_5020720).sum := by decide
  have hdescent : baseEnd_5020720 < baseStart_5020720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020724 : List Nat := [2, 5, 1, 2, 1, 2, 1, 1, 3, 3, 2]
def baseStart_5020724 : Nat := 118140960795 + 5020724 * 2 ^ 59
def prefixEnd_5020724 : Nat := 4983230072969 + 3 ^ 40 * 5020724 * 2
def baseEnd_5020724 : Nat := 2578044645564319627960117

theorem tailTrace_5020724 : CollatzResearch.WordTrace tailWord_5020724 prefixEnd_5020724 2578044645564319627960117 := by
  unfold tailWord_5020724
  simp only [CollatzResearch.WordTrace]
  refine ⟨91560424131390947118762613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122080565508521262825016817 91560424131390947118762613)
  ·
    refine ⟨8583789762317901292383995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91560424131390947118762613 8583789762317901292383995)
    ·
      refine ⟨12875684643476851938575993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8583789762317901292383995 12875684643476851938575993)
      ·
        refine ⟨9656763482607638953931995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12875684643476851938575993 9656763482607638953931995)
        ·
          refine ⟨14485145223911458430897993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9656763482607638953931995 14485145223911458430897993)
          ·
            refine ⟨10863858917933593823173495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14485145223911458430897993 10863858917933593823173495)
            ·
              refine ⟨16295788376900390734760243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10863858917933593823173495 16295788376900390734760243)
              ·
                refine ⟨24443682565350586102140365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16295788376900390734760243 24443682565350586102140365)
                ·
                  refine ⟨9166380962006469788302637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24443682565350586102140365 9166380962006469788302637)
                  ·
                    refine ⟨3437392860752426170613489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9166380962006469788302637 3437392860752426170613489)
                    ·
                      refine ⟨2578044645564319627960117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3437392860752426170613489 2578044645564319627960117)
                      ·
                        rfl

theorem cell23_5020724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 1, 2, 1, 1, 3, 3, 2].length) (baseStart_5020724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020724 prefixEnd_5020724 := by exact prefixLift 5020724
  have htrace : WordTrace (prefixWord ++ tailWord_5020724) baseStart_5020724 baseEnd_5020724 := by
    simpa [prefixWord, tailWord_5020724, baseEnd_5020724] using wordTrace_append hprefix tailTrace_5020724
  have hstable : (prefixWord ++ tailWord_5020724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020724).length < 2 ^ (prefixWord ++ tailWord_5020724).sum := by decide
  have hdescent : baseEnd_5020724 < baseStart_5020724 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020754 : List Nat := [3, 2, 2, 1, 3, 1, 1, 4, 2, 2, 2]
def baseStart_5020754 : Nat := 118140960795 + 5020754 * 2 ^ 59
def prefixEnd_5020754 : Nat := 4983230072969 + 3 ^ 40 * 5020754 * 2
def baseEnd_5020754 : Nat := 2578060049983954510584979

theorem tailTrace_5020754 : CollatzResearch.WordTrace tailWord_5020754 prefixEnd_5020754 2578060049983954510584979 := by
  unfold tailWord_5020754
  simp only [CollatzResearch.WordTrace]
  refine ⟨45780485613168302340279329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122081294968448806240744877 45780485613168302340279329)
  ·
    refine ⟨34335364209876226755209497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45780485613168302340279329 34335364209876226755209497)
    ·
      refine ⟨25751523157407170066407123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34335364209876226755209497 25751523157407170066407123)
      ·
        refine ⟨38627284736110755099610685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25751523157407170066407123 38627284736110755099610685)
        ·
          refine ⟨14485231776041533162354007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38627284736110755099610685 14485231776041533162354007)
          ·
            refine ⟨21727847664062299743531011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14485231776041533162354007 21727847664062299743531011)
            ·
              refine ⟨32591771496093449615296517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21727847664062299743531011 32591771496093449615296517)
              ·
                refine ⟨6110957155517521802868097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32591771496093449615296517 6110957155517521802868097)
                ·
                  refine ⟨4583217866638141352151073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6110957155517521802868097 4583217866638141352151073)
                  ·
                    refine ⟨3437413399978606014113305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4583217866638141352151073 3437413399978606014113305)
                    ·
                      refine ⟨2578060049983954510584979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3437413399978606014113305 2578060049983954510584979)
                      ·
                        rfl

theorem cell23_5020754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 4, 2, 2, 2].length) (baseStart_5020754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020754 prefixEnd_5020754 := by exact prefixLift 5020754
  have htrace : WordTrace (prefixWord ++ tailWord_5020754) baseStart_5020754 baseEnd_5020754 := by
    simpa [prefixWord, tailWord_5020754, baseEnd_5020754] using wordTrace_append hprefix tailTrace_5020754
  have hstable : (prefixWord ++ tailWord_5020754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020754).length < 2 ^ (prefixWord ++ tailWord_5020754).sum := by decide
  have hdescent : baseEnd_5020754 < baseStart_5020754 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020760 : List Nat := [2, 1, 2, 2, 1, 3, 3, 4, 5]
def baseStart_5020760 : Nat := 118140960795 + 5020760 * 2 ^ 59
def prefixEnd_5020760 : Nat := 4983230072969 + 3 ^ 40 * 5020760 * 2
def baseEnd_5020760 : Nat := 286451458985320165234439

theorem tailTrace_5020760 : CollatzResearch.WordTrace tailWord_5020760 prefixEnd_5020760 286451458985320165234439 := by
  unfold tailWord_5020760
  simp only [CollatzResearch.WordTrace]
  refine ⟨91561080645325736192917867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122081440860434314923890489 91561080645325736192917867)
  ·
    refine ⟨137341620967988604289376801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91561080645325736192917867 137341620967988604289376801)
    ·
      refine ⟨103006215725991453217032601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137341620967988604289376801 103006215725991453217032601)
      ·
        refine ⟨77254661794493589912774451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103006215725991453217032601 77254661794493589912774451)
        ·
          refine ⟨115881992691740384869161677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77254661794493589912774451 115881992691740384869161677)
          ·
            refine ⟨43455747259402644325935629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115881992691740384869161677 43455747259402644325935629)
            ·
              refine ⟨16295905222275991622225861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43455747259402644325935629 16295905222275991622225861)
              ·
                refine ⟨3055482229176748429167349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16295905222275991622225861 3055482229176748429167349)
                ·
                  refine ⟨286451458985320165234439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3055482229176748429167349 286451458985320165234439)
                  ·
                    rfl

theorem cell23_5020760_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 3, 4, 5].length) (baseStart_5020760 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020760 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020760 prefixEnd_5020760 := by exact prefixLift 5020760
  have htrace : WordTrace (prefixWord ++ tailWord_5020760) baseStart_5020760 baseEnd_5020760 := by
    simpa [prefixWord, tailWord_5020760, baseEnd_5020760] using wordTrace_append hprefix tailTrace_5020760
  have hstable : (prefixWord ++ tailWord_5020760).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020760).length < 2 ^ (prefixWord ++ tailWord_5020760).sum := by decide
  have hdescent : baseEnd_5020760 < baseStart_5020760 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020760) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020773 : List Nat := [1, 3, 1, 3, 2, 1, 2, 2, 1, 7]
def baseStart_5020773 : Nat := 118140960795 + 5020773 * 2 ^ 59
def prefixEnd_5020773 : Nat := 4983230072969 + 3 ^ 40 * 5020773 * 2
def baseEnd_5020773 : Nat := 859356602038796645415797

theorem tailTrace_5020773 : CollatzResearch.WordTrace tailWord_5020773 prefixEnd_5020773 859356602038796645415797 := by
  unfold tailWord_5020773
  simp only [CollatzResearch.WordTrace]
  refine ⟨183122635439604375606058973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122081756959736250404039315 183122635439604375606058973)
  ·
    refine ⟨68670988289851640852272115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183122635439604375606058973 68670988289851640852272115)
    ·
      refine ⟨103006482434777461278408173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68670988289851640852272115 103006482434777461278408173)
      ·
        refine ⟨38627430913041547979403065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103006482434777461278408173 38627430913041547979403065)
        ·
          refine ⟨28970573184781160984552299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38627430913041547979403065 28970573184781160984552299)
          ·
            refine ⟨43455859777171741476828449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28970573184781160984552299 43455859777171741476828449)
            ·
              refine ⟨32591894832878806107621337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43455859777171741476828449 32591894832878806107621337)
              ·
                refine ⟨24443921124659104580716003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32591894832878806107621337 24443921124659104580716003)
                ·
                  refine ⟨36665881686988656871074005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24443921124659104580716003 36665881686988656871074005)
                  ·
                    refine ⟨859356602038796645415797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36665881686988656871074005 859356602038796645415797)
                    ·
                      rfl

theorem cell23_5020773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 2, 2, 1, 7].length) (baseStart_5020773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020773 prefixEnd_5020773 := by exact prefixLift 5020773
  have htrace : WordTrace (prefixWord ++ tailWord_5020773) baseStart_5020773 baseEnd_5020773 := by
    simpa [prefixWord, tailWord_5020773, baseEnd_5020773] using wordTrace_append hprefix tailTrace_5020773
  have hstable : (prefixWord ++ tailWord_5020773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020773).length < 2 ^ (prefixWord ++ tailWord_5020773).sum := by decide
  have hdescent : baseEnd_5020773 < baseStart_5020773 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020780 : List Nat := [2, 2, 1, 1, 3, 2, 1, 2, 2, 5, 2]
def baseStart_5020780 : Nat := 118140960795 + 5020780 * 2 ^ 59
def prefixEnd_5020780 : Nat := 4983230072969 + 3 ^ 40 * 5020780 * 2
def baseEnd_5020780 : Nat := 2578073400480971408859859

theorem tailTrace_5020780 : CollatzResearch.WordTrace tailWord_5020780 prefixEnd_5020780 2578073400480971408859859 := by
  unfold tailWord_5020780
  simp only [CollatzResearch.WordTrace]
  refine ⟨91561445375289507900781897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122081927167052677201042529 91561445375289507900781897)
  ·
    refine ⟨68671084031467130925586423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91561445375289507900781897 68671084031467130925586423)
    ·
      refine ⟨103006626047200696388379635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68671084031467130925586423 103006626047200696388379635)
      ·
        refine ⟨154509939070801044582569453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103006626047200696388379635 154509939070801044582569453)
        ·
          refine ⟨57941227151550391718463545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154509939070801044582569453 57941227151550391718463545)
          ·
            refine ⟨43455920363662793788847659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57941227151550391718463545 43455920363662793788847659)
            ·
              refine ⟨65183880545494190683271489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43455920363662793788847659 65183880545494190683271489)
              ·
                refine ⟨48887910409120643012453617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65183880545494190683271489 48887910409120643012453617)
                ·
                  refine ⟨36665932806840482259340213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48887910409120643012453617 36665932806840482259340213)
                  ·
                    refine ⟨3437431200641295211813145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36665932806840482259340213 3437431200641295211813145)
                    ·
                      refine ⟨2578073400480971408859859, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3437431200641295211813145 2578073400480971408859859)
                      ·
                        rfl

theorem cell23_5020780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 5, 2].length) (baseStart_5020780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020780 prefixEnd_5020780 := by exact prefixLift 5020780
  have htrace : WordTrace (prefixWord ++ tailWord_5020780) baseStart_5020780 baseEnd_5020780 := by
    simpa [prefixWord, tailWord_5020780, baseEnd_5020780] using wordTrace_append hprefix tailTrace_5020780
  have hstable : (prefixWord ++ tailWord_5020780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020780).length < 2 ^ (prefixWord ++ tailWord_5020780).sum := by decide
  have hdescent : baseEnd_5020780 < baseStart_5020780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020790 : List Nat := [5, 1, 1, 2, 1, 1, 3, 1, 1, 7]
def baseStart_5020790 : Nat := 118140960795 + 5020790 * 2 ^ 59
def prefixEnd_5020790 : Nat := 4983230072969 + 3 ^ 40 * 5020790 * 2
def baseEnd_5020790 : Nat := 859359511762505456578271

theorem tailTrace_5020790 : CollatzResearch.WordTrace tailWord_5020790 prefixEnd_5020790 859359511762505456578271 := by
  unfold tailWord_5020790
  simp only [CollatzResearch.WordTrace]
  refine ⟨11445203467533924219339239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122082170320361858339618549 11445203467533924219339239)
  ·
    refine ⟨17167805201300886329008859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11445203467533924219339239 17167805201300886329008859)
    ·
      refine ⟨25751707801951329493513289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17167805201300886329008859 25751707801951329493513289)
      ·
        refine ⟨19313780851463497120134967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25751707801951329493513289 19313780851463497120134967)
        ·
          refine ⟨28970671277195245680202451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19313780851463497120134967 28970671277195245680202451)
          ·
            refine ⟨43456006915792868520303677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28970671277195245680202451 43456006915792868520303677)
            ·
              refine ⟨16296002593422325695113879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43456006915792868520303677 16296002593422325695113879)
              ·
                refine ⟨24444003890133488542670819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16296002593422325695113879 24444003890133488542670819)
                ·
                  refine ⟨36666005835200232814006229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24444003890133488542670819 36666005835200232814006229)
                  ·
                    refine ⟨859359511762505456578271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36666005835200232814006229 859359511762505456578271)
                    ·
                      rfl

theorem cell23_5020790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 1, 3, 1, 1, 7].length) (baseStart_5020790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020790 prefixEnd_5020790 := by exact prefixLift 5020790
  have htrace : WordTrace (prefixWord ++ tailWord_5020790) baseStart_5020790 baseEnd_5020790 := by
    simpa [prefixWord, tailWord_5020790, baseEnd_5020790] using wordTrace_append hprefix tailTrace_5020790
  have hstable : (prefixWord ++ tailWord_5020790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020790).length < 2 ^ (prefixWord ++ tailWord_5020790).sum := by decide
  have hdescent : baseEnd_5020790 < baseStart_5020790 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020810 : List Nat := [3, 1, 2, 3, 1, 1, 2, 1, 4, 1, 4]
def baseStart_5020810 : Nat := 118140960795 + 5020810 * 2 ^ 59
def prefixEnd_5020810 : Nat := 4983230072969 + 3 ^ 40 * 5020810 * 2
def baseEnd_5020810 : Nat := 2578088804900606291484721

theorem tailTrace_5020810 : CollatzResearch.WordTrace tailWord_5020810 prefixEnd_5020810 2578088804900606291484721 := by
  unfold tailWord_5020810
  simp only [CollatzResearch.WordTrace]
  refine ⟨45780996235117582731288971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122082656626980220616770589 45780996235117582731288971)
  ·
    refine ⟨68671494352676374096933457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45780996235117582731288971 68671494352676374096933457)
    ·
      refine ⟨51503620764507280572700093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68671494352676374096933457 51503620764507280572700093)
      ·
        refine ⟨19313857786690230214762535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51503620764507280572700093 19313857786690230214762535)
        ·
          refine ⟨28970786680035345322143803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19313857786690230214762535 28970786680035345322143803)
          ·
            refine ⟨43456180020053017983215705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28970786680035345322143803 43456180020053017983215705)
            ·
              refine ⟨32592135015039763487411779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43456180020053017983215705 32592135015039763487411779)
              ·
                refine ⟨48888202522559645231117669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32592135015039763487411779 48888202522559645231117669)
                ·
                  refine ⟨9166537972979933480834563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48888202522559645231117669 9166537972979933480834563)
                  ·
                    refine ⟨13749806959469900221251845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9166537972979933480834563 13749806959469900221251845)
                    ·
                      refine ⟨2578088804900606291484721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13749806959469900221251845 2578088804900606291484721)
                      ·
                        rfl

theorem cell23_5020810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_5020810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020810 prefixEnd_5020810 := by exact prefixLift 5020810
  have htrace : WordTrace (prefixWord ++ tailWord_5020810) baseStart_5020810 baseEnd_5020810 := by
    simpa [prefixWord, tailWord_5020810, baseEnd_5020810] using wordTrace_append hprefix tailTrace_5020810
  have hstable : (prefixWord ++ tailWord_5020810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020810).length < 2 ^ (prefixWord ++ tailWord_5020810).sum := by decide
  have hdescent : baseEnd_5020810 < baseStart_5020810 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020884 : List Nat := [2, 4, 1, 4, 1, 1, 1, 3, 6]
def baseStart_5020884 : Nat := 118140960795 + 5020884 * 2 ^ 59
def prefixEnd_5020884 : Nat := 4983230072969 + 3 ^ 40 * 5020884 * 2
def baseEnd_5020884 : Nat := 286458533607671000217709

theorem tailTrace_5020884 : CollatzResearch.WordTrace tailWord_5020884 prefixEnd_5020884 286458533607671000217709 := by
  unfold tailWord_5020884
  simp only [CollatzResearch.WordTrace]
  refine ⟨91563341971101120781674853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122084455961468161042233137 91563341971101120781674853)
  ·
    refine ⟨17168126619581460146564035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91563341971101120781674853 17168126619581460146564035)
    ·
      refine ⟨25752189929372190219846053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17168126619581460146564035 25752189929372190219846053)
      ·
        refine ⟨4828535611757285666221135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25752189929372190219846053 4828535611757285666221135)
        ·
          refine ⟨7242803417635928499331703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4828535611757285666221135 7242803417635928499331703)
          ·
            refine ⟨10864205126453892748997555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7242803417635928499331703 10864205126453892748997555)
            ·
              refine ⟨16296307689680839123496333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10864205126453892748997555 16296307689680839123496333)
              ·
                refine ⟨6111115383630314671311125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16296307689680839123496333 6111115383630314671311125)
                ·
                  refine ⟨286458533607671000217709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6111115383630314671311125 286458533607671000217709)
                  ·
                    rfl

theorem cell23_5020884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 1, 1, 3, 6].length) (baseStart_5020884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020884 prefixEnd_5020884 := by exact prefixLift 5020884
  have htrace : WordTrace (prefixWord ++ tailWord_5020884) baseStart_5020884 baseEnd_5020884 := by
    simpa [prefixWord, tailWord_5020884, baseEnd_5020884] using wordTrace_append hprefix tailTrace_5020884
  have hstable : (prefixWord ++ tailWord_5020884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020884).length < 2 ^ (prefixWord ++ tailWord_5020884).sum := by decide
  have hdescent : baseEnd_5020884 < baseStart_5020884 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020897 : List Nat := [1, 2, 3, 1, 3, 2, 3, 2, 1, 5]
def baseStart_5020897 : Nat := 118140960795 + 5020897 * 2 ^ 59
def prefixEnd_5020897 : Nat := 4983230072969 + 3 ^ 40 * 5020897 * 2
def baseEnd_5020897 : Nat := 859377825905849150365607

theorem tailTrace_5020897 : CollatzResearch.WordTrace tailWord_5020897 prefixEnd_5020897 859377825905849150365607 := by
  unfold tailWord_5020897
  simp only [CollatzResearch.WordTrace]
  refine ⟨183127158091155144783572945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122084772060770096522381963 183127158091155144783572945)
  ·
    refine ⟨137345368568366358587679709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183127158091155144783572945 137345368568366358587679709)
    ·
      refine ⟨51504513213137384470379891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137345368568366358587679709 51504513213137384470379891)
      ·
        refine ⟨77256769819706076705569837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51504513213137384470379891 77256769819706076705569837)
        ·
          refine ⟨28971288682389778764588689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77256769819706076705569837 28971288682389778764588689)
          ·
            refine ⟨21728466511792334073441517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28971288682389778764588689 21728466511792334073441517)
            ·
              refine ⟨8148174941922125277540569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21728466511792334073441517 8148174941922125277540569)
              ·
                refine ⟨6111131206441593958155427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8148174941922125277540569 6111131206441593958155427)
                ·
                  refine ⟨9166696809662390937233141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6111131206441593958155427 9166696809662390937233141)
                  ·
                    refine ⟨859377825905849150365607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9166696809662390937233141 859377825905849150365607)
                    ·
                      rfl

theorem cell23_5020897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 3, 2, 1, 5].length) (baseStart_5020897 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020897 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020897 prefixEnd_5020897 := by exact prefixLift 5020897
  have htrace : WordTrace (prefixWord ++ tailWord_5020897) baseStart_5020897 baseEnd_5020897 := by
    simpa [prefixWord, tailWord_5020897, baseEnd_5020897] using wordTrace_append hprefix tailTrace_5020897
  have hstable : (prefixWord ++ tailWord_5020897).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020897).length < 2 ^ (prefixWord ++ tailWord_5020897).sum := by decide
  have hdescent : baseEnd_5020897 < baseStart_5020897 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020904 : List Nat := [2, 1, 4, 1, 2, 1, 4, 1, 2, 3, 2]
def baseStart_5020904 : Nat := 118140960795 + 5020904 * 2 ^ 59
def prefixEnd_5020904 : Nat := 4983230072969 + 3 ^ 40 * 5020904 * 2
def baseEnd_5020904 : Nat := 2578137072082128923709289

theorem tailTrace_5020904 : CollatzResearch.WordTrace tailWord_5020904 prefixEnd_5020904 2578137072082128923709289 := by
  unfold tailWord_5020904
  simp only [CollatzResearch.WordTrace]
  refine ⟨91563706701064892489538883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122084942268086523319385177 91563706701064892489538883)
  ·
    refine ⟨137345560051597338734308325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91563706701064892489538883 137345560051597338734308325)
    ·
      refine ⟨25752292509674501012682811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137345560051597338734308325 25752292509674501012682811)
      ·
        refine ⟨38628438764511751519024217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25752292509674501012682811 38628438764511751519024217)
        ·
          refine ⟨28971329073383813639268163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38628438764511751519024217 28971329073383813639268163)
          ·
            refine ⟨43456993610075720458902245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28971329073383813639268163 43456993610075720458902245)
            ·
              refine ⟨8148186301889197586044171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43456993610075720458902245 8148186301889197586044171)
              ·
                refine ⟨12222279452833796379066257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8148186301889197586044171 12222279452833796379066257)
                ·
                  refine ⟨9166709589625347284299693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12222279452833796379066257 9166709589625347284299693)
                  ·
                    refine ⟨3437516096109505231612385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9166709589625347284299693 3437516096109505231612385)
                    ·
                      refine ⟨2578137072082128923709289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3437516096109505231612385 2578137072082128923709289)
                      ·
                        rfl

theorem cell23_5020904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 4, 1, 2, 3, 2].length) (baseStart_5020904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020904 prefixEnd_5020904 := by exact prefixLift 5020904
  have htrace : WordTrace (prefixWord ++ tailWord_5020904) baseStart_5020904 baseEnd_5020904 := by
    simpa [prefixWord, tailWord_5020904, baseEnd_5020904] using wordTrace_append hprefix tailTrace_5020904
  have hstable : (prefixWord ++ tailWord_5020904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020904).length < 2 ^ (prefixWord ++ tailWord_5020904).sum := by decide
  have hdescent : baseEnd_5020904 < baseStart_5020904 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020910 : List Nat := [4, 1, 2, 1, 1, 1, 3, 1, 3, 6]
def baseStart_5020910 : Nat := 118140960795 + 5020910 * 2 ^ 59
def prefixEnd_5020910 : Nat := 4983230072969 + 3 ^ 40 * 5020910 * 2
def baseEnd_5020910 : Nat := 859380050988685300078087

theorem tailTrace_5020910 : CollatzResearch.WordTrace tailWord_5020910 prefixEnd_5020910 859380050988685300078087 := by
  unfold tailWord_5020910
  simp only [CollatzResearch.WordTrace]
  refine ⟨22890954030013506000474523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122085088160072032002530789 22890954030013506000474523)
  ·
    refine ⟨34336431045020259000711785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22890954030013506000474523 34336431045020259000711785)
    ·
      refine ⟨25752323283765194250533839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34336431045020259000711785 25752323283765194250533839)
      ·
        refine ⟨38628484925647791375800759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25752323283765194250533839 38628484925647791375800759)
        ·
          refine ⟨57942727388471687063701139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38628484925647791375800759 57942727388471687063701139)
          ·
            refine ⟨86914091082707530595551709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57942727388471687063701139 86914091082707530595551709)
            ·
              refine ⟨32592784156015323973331891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86914091082707530595551709 32592784156015323973331891)
              ·
                refine ⟨48889176234022985959997837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32592784156015323973331891 48889176234022985959997837)
                ·
                  refine ⟨18333441087758619734999189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48889176234022985959997837 18333441087758619734999189)
                  ·
                    refine ⟨859380050988685300078087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18333441087758619734999189 859380050988685300078087)
                    ·
                      rfl

theorem cell23_5020910_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 3, 1, 3, 6].length) (baseStart_5020910 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020910 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020910 prefixEnd_5020910 := by exact prefixLift 5020910
  have htrace : WordTrace (prefixWord ++ tailWord_5020910) baseStart_5020910 baseEnd_5020910 := by
    simpa [prefixWord, tailWord_5020910, baseEnd_5020910] using wordTrace_append hprefix tailTrace_5020910
  have hstable : (prefixWord ++ tailWord_5020910).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020910).length < 2 ^ (prefixWord ++ tailWord_5020910).sum := by decide
  have hdescent : baseEnd_5020910 < baseStart_5020910 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020910) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020927 : List Nat := [1, 1, 2, 2, 1, 5, 1, 4, 2, 4]
def baseStart_5020927 : Nat := 118140960795 + 5020927 * 2 ^ 59
def prefixEnd_5020927 : Nat := 4983230072969 + 3 ^ 40 * 5020927 * 2
def baseEnd_5020927 : Nat := 859382960712394111240561

theorem tailTrace_5020927 : CollatzResearch.WordTrace tailWord_5020927 prefixEnd_5020927 859382960712394111240561 := by
  unfold tailWord_5020927
  simp only [CollatzResearch.WordTrace]
  refine ⟨183128252281046459907165035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122085501520697639938110023 183128252281046459907165035)
  ·
    refine ⟨274692378421569689860747553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183128252281046459907165035 274692378421569689860747553)
    ·
      refine ⟨206019283816177267395560665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274692378421569689860747553 206019283816177267395560665)
      ·
        refine ⟨154514462862132950546670499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206019283816177267395560665 154514462862132950546670499)
        ·
          refine ⟨231771694293199425820005749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154514462862132950546670499 231771694293199425820005749)
          ·
            refine ⟨21728596339987446170625539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 231771694293199425820005749 21728596339987446170625539)
            ·
              refine ⟨32592894509981169255938309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21728596339987446170625539 32592894509981169255938309)
              ·
                refine ⟨6111167720621469235488433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32592894509981169255938309 6111167720621469235488433)
                ·
                  refine ⟨4583375790466101926616325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6111167720621469235488433 4583375790466101926616325)
                  ·
                    refine ⟨859382960712394111240561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4583375790466101926616325 859382960712394111240561)
                    ·
                      rfl

theorem cell23_5020927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 5, 1, 4, 2, 4].length) (baseStart_5020927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020927 prefixEnd_5020927 := by exact prefixLift 5020927
  have htrace : WordTrace (prefixWord ++ tailWord_5020927) baseStart_5020927 baseEnd_5020927 := by
    simpa [prefixWord, tailWord_5020927, baseEnd_5020927] using wordTrace_append hprefix tailTrace_5020927
  have hstable : (prefixWord ++ tailWord_5020927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020927).length < 2 ^ (prefixWord ++ tailWord_5020927).sum := by decide
  have hdescent : baseEnd_5020927 < baseStart_5020927 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020940 : List Nat := [2, 2, 1, 2, 2, 3, 3, 8]
def baseStart_5020940 : Nat := 118140960795 + 5020940 * 2 ^ 59
def prefixEnd_5020940 : Nat := 4983230072969 + 3 ^ 40 * 5020940 * 2
def baseEnd_5020940 : Nat := 95487242866136695661449

theorem tailTrace_5020940 : CollatzResearch.WordTrace tailWord_5020940 prefixEnd_5020940 95487242866136695661449 := by
  unfold tailWord_5020940
  simp only [CollatzResearch.WordTrace]
  refine ⟨91564363214999681563694137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122085817619999575418258849 91564363214999681563694137)
  ·
    refine ⟨68673272411249761172770603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91564363214999681563694137 68673272411249761172770603)
    ·
      refine ⟨103009908616874641759155905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68673272411249761172770603 103009908616874641759155905)
      ·
        refine ⟨77257431462655981319366929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103009908616874641759155905 77257431462655981319366929)
        ·
          refine ⟨57943073596991985989525197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77257431462655981319366929 57943073596991985989525197)
          ·
            refine ⟨21728652598871994746071949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57943073596991985989525197 21728652598871994746071949)
            ·
              refine ⟨8148244724576998029776981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21728652598871994746071949 8148244724576998029776981)
              ·
                refine ⟨95487242866136695661449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8148244724576998029776981 95487242866136695661449)
                ·
                  rfl

theorem cell23_5020940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 8].length) (baseStart_5020940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020940 prefixEnd_5020940 := by exact prefixLift 5020940
  have htrace : WordTrace (prefixWord ++ tailWord_5020940) baseStart_5020940 baseEnd_5020940 := by
    simpa [prefixWord, tailWord_5020940, baseEnd_5020940] using wordTrace_append hprefix tailTrace_5020940
  have hstable : (prefixWord ++ tailWord_5020940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020940).length < 2 ^ (prefixWord ++ tailWord_5020940).sum := by decide
  have hdescent : baseEnd_5020940 < baseStart_5020940 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5020968 : List Nat := [2, 1, 5, 1, 2, 1, 1, 5, 1, 2, 2]
def baseStart_5020968 : Nat := 118140960795 + 5020968 * 2 ^ 59
def prefixEnd_5020968 : Nat := 4983230072969 + 3 ^ 40 * 5020968 * 2
def baseEnd_5020968 : Nat := 2578169934844016673308995

theorem tailTrace_5020968 : CollatzResearch.WordTrace tailWord_5020968 prefixEnd_5020968 2578169934844016673308995 := by
  unfold tailWord_5020968
  simp only [CollatzResearch.WordTrace]
  refine ⟨91564873836948961954703779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122086498449265282606271705 91564873836948961954703779)
  ·
    refine ⟨137347310755423442932055669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91564873836948961954703779 137347310755423442932055669)
    ·
      refine ⟨12876310383320947774880219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 137347310755423442932055669 12876310383320947774880219)
      ·
        refine ⟨19314465574981421662320329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12876310383320947774880219 19314465574981421662320329)
        ·
          refine ⟨14485849181236066246740247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19314465574981421662320329 14485849181236066246740247)
          ·
            refine ⟨21728773771854099370110371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14485849181236066246740247 21728773771854099370110371)
            ·
              refine ⟨32593160657781149055165557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21728773771854099370110371 32593160657781149055165557)
              ·
                refine ⟨3055608811666982723921771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32593160657781149055165557 3055608811666982723921771)
                ·
                  refine ⟨4583413217500474085882657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3055608811666982723921771 4583413217500474085882657)
                  ·
                    refine ⟨3437559913125355564411993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4583413217500474085882657 3437559913125355564411993)
                    ·
                      refine ⟨2578169934844016673308995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3437559913125355564411993 2578169934844016673308995)
                      ·
                        rfl

theorem cell23_5020968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_5020968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5020968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5020968 prefixEnd_5020968 := by exact prefixLift 5020968
  have htrace : WordTrace (prefixWord ++ tailWord_5020968) baseStart_5020968 baseEnd_5020968 := by
    simpa [prefixWord, tailWord_5020968, baseEnd_5020968] using wordTrace_append hprefix tailTrace_5020968
  have hstable : (prefixWord ++ tailWord_5020968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5020968).length < 2 ^ (prefixWord ++ tailWord_5020968).sum := by decide
  have hdescent : baseEnd_5020968 < baseStart_5020968 := by decide
  rcases family_descends (prefixWord ++ tailWord_5020968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021027 : List Nat := [1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 5]
def baseStart_5021027 : Nat := 118140960795 + 5021027 * 2 ^ 59
def prefixEnd_5021027 : Nat := 4983230072969 + 3 ^ 40 * 5021027 * 2
def baseEnd_5021027 : Nat := 2578200230202631942471223

theorem tailTrace_5021027 : CollatzResearch.WordTrace tailWord_5021027 prefixEnd_5021027 2578200230202631942471223 := by
  unfold tailWord_5021027
  simp only [CollatzResearch.WordTrace]
  refine ⟨183131899580684176985805335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122087933053789451323870223 183131899580684176985805335)
  ·
    refine ⟨274697849371026265478708003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183131899580684176985805335 274697849371026265478708003)
    ·
      refine ⟨412046774056539398218062005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274697849371026265478708003 412046774056539398218062005)
      ·
        refine ⟨38629385067800568582943313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 412046774056539398218062005 38629385067800568582943313)
        ·
          refine ⟨28972038800850426437207485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38629385067800568582943313 28972038800850426437207485)
          ·
            refine ⟨10864514550318909913952807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28972038800850426437207485 10864514550318909913952807)
            ·
              refine ⟨16296771825478364870929211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10864514550318909913952807 16296771825478364870929211)
              ·
                refine ⟨24445157738217547306393817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16296771825478364870929211 24445157738217547306393817)
                ·
                  refine ⟨18333868303663160479795363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24445157738217547306393817 18333868303663160479795363)
                  ·
                    refine ⟨27500802455494740719693045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18333868303663160479795363 27500802455494740719693045)
                    ·
                      refine ⟨2578200230202631942471223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27500802455494740719693045 2578200230202631942471223)
                      ·
                        rfl

theorem cell23_5021027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 1, 5].length) (baseStart_5021027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021027 prefixEnd_5021027 := by exact prefixLift 5021027
  have htrace : WordTrace (prefixWord ++ tailWord_5021027) baseStart_5021027 baseEnd_5021027 := by
    simpa [prefixWord, tailWord_5021027, baseEnd_5021027] using wordTrace_append hprefix tailTrace_5021027
  have hstable : (prefixWord ++ tailWord_5021027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021027).length < 2 ^ (prefixWord ++ tailWord_5021027).sum := by decide
  have hdescent : baseEnd_5021027 < baseStart_5021027 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021040 : List Nat := [2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 7]
def baseStart_5021040 : Nat := 118140960795 + 5021040 * 2 ^ 59
def prefixEnd_5021040 : Nat := 4983230072969 + 3 ^ 40 * 5021040 * 2
def baseEnd_5021040 : Nat := 2578206905451140391608663

theorem tailTrace_5021040 : CollatzResearch.WordTrace tailWord_5021040 prefixEnd_5021040 2578206905451140391608663 := by
  unfold tailWord_5021040
  simp only [CollatzResearch.WordTrace]
  refine ⟨91566186864818540103014287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122088249153091386804019049 91566186864818540103014287)
  ·
    refine ⟨137349280297227810154521431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91566186864818540103014287 137349280297227810154521431)
    ·
      refine ⟨206023920445841715231782147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137349280297227810154521431 206023920445841715231782147)
      ·
        refine ⟨309035880668762572847673221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206023920445841715231782147 309035880668762572847673221)
        ·
          refine ⟨57944227625392982408938729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 309035880668762572847673221 57944227625392982408938729)
          ·
            refine ⟨43458170719044736806704047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57944227625392982408938729 43458170719044736806704047)
            ·
              refine ⟨65187256078567105210056071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43458170719044736806704047 65187256078567105210056071)
              ·
                refine ⟨97780884117850657815084107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65187256078567105210056071 97780884117850657815084107)
                ·
                  refine ⟨146671326176775986722626161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97780884117850657815084107 146671326176775986722626161)
                  ·
                    refine ⟨110003494632581990041969621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 146671326176775986722626161 110003494632581990041969621)
                    ·
                      refine ⟨2578206905451140391608663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 110003494632581990041969621 2578206905451140391608663)
                      ·
                        rfl

theorem cell23_5021040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 7].length) (baseStart_5021040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021040 prefixEnd_5021040 := by exact prefixLift 5021040
  have htrace : WordTrace (prefixWord ++ tailWord_5021040) baseStart_5021040 baseEnd_5021040 := by
    simpa [prefixWord, tailWord_5021040, baseEnd_5021040] using wordTrace_append hprefix tailTrace_5021040
  have hstable : (prefixWord ++ tailWord_5021040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021040).length < 2 ^ (prefixWord ++ tailWord_5021040).sum := by decide
  have hdescent : baseEnd_5021040 < baseStart_5021040 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021077 : List Nat := [1, 3, 2, 1, 1, 2, 3, 3, 2, 5]
def baseStart_5021077 : Nat := 118140960795 + 5021077 * 2 ^ 59
def prefixEnd_5021077 : Nat := 4983230072969 + 3 ^ 40 * 5021077 * 2
def baseEnd_5021077 : Nat := 859408634745118915615331

theorem tailTrace_5021077 : CollatzResearch.WordTrace tailWord_5021077 prefixEnd_5021077 859408634745118915615331 := by
  unfold tailWord_5021077
  simp only [CollatzResearch.WordTrace]
  refine ⟨183133723230503035525125485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122089148820335357016750323 183133723230503035525125485)
  ·
    refine ⟨68675146211438638321922057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183133723230503035525125485 68675146211438638321922057)
    ·
      refine ⟨51506359658578978741441543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68675146211438638321922057 51506359658578978741441543)
      ·
        refine ⟨77259539487868468112162315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51506359658578978741441543 77259539487868468112162315)
        ·
          refine ⟨115889309231802702168243473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77259539487868468112162315 115889309231802702168243473)
          ·
            refine ⟨86916981923852026626182605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115889309231802702168243473 86916981923852026626182605)
            ·
              refine ⟨32593868221444509984818477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86916981923852026626182605 32593868221444509984818477)
              ·
                refine ⟨12222700583041691244306929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32593868221444509984818477 12222700583041691244306929)
                ·
                  refine ⟨9167025437281268433230197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12222700583041691244306929 9167025437281268433230197)
                  ·
                    refine ⟨859408634745118915615331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9167025437281268433230197 859408634745118915615331)
                    ·
                      rfl

theorem cell23_5021077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 3, 3, 2, 5].length) (baseStart_5021077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021077 prefixEnd_5021077 := by exact prefixLift 5021077
  have htrace : WordTrace (prefixWord ++ tailWord_5021077) baseStart_5021077 baseEnd_5021077 := by
    simpa [prefixWord, tailWord_5021077, baseEnd_5021077] using wordTrace_append hprefix tailTrace_5021077
  have hstable : (prefixWord ++ tailWord_5021077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021077).length < 2 ^ (prefixWord ++ tailWord_5021077).sum := by decide
  have hdescent : baseEnd_5021077 < baseStart_5021077 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021087 : List Nat := [1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 5]
def baseStart_5021087 : Nat := 118140960795 + 5021087 * 2 ^ 59
def prefixEnd_5021087 : Nat := 4983230072969 + 3 ^ 40 * 5021087 * 2
def baseEnd_5021087 : Nat := 2578231039041901707720947

theorem tailTrace_5021087 : CollatzResearch.WordTrace tailWord_5021087 prefixEnd_5021087 2578231039041901707720947 := by
  unfold tailWord_5021087
  simp only [CollatzResearch.WordTrace]
  refine ⟨183134087960466807232989515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122089391973644538155326343 183134087960466807232989515)
  ·
    refine ⟨274701131940700210849484273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183134087960466807232989515 274701131940700210849484273)
    ·
      refine ⟨206025848955525158137113205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274701131940700210849484273 206025848955525158137113205)
      ·
        refine ⟨19314923339580483575354363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 206025848955525158137113205 19314923339580483575354363)
        ·
          refine ⟨28972385009370725363031545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19314923339580483575354363 28972385009370725363031545)
          ·
            refine ⟨21729288757028044022273659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28972385009370725363031545 21729288757028044022273659)
            ·
              refine ⟨32593933135542066033410489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21729288757028044022273659 32593933135542066033410489)
              ·
                refine ⟨24445449851656549525057867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32593933135542066033410489 24445449851656549525057867)
                ·
                  refine ⟨36668174777484824287586801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24445449851656549525057867 36668174777484824287586801)
                  ·
                    refine ⟨27501131083113618215690101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36668174777484824287586801 27501131083113618215690101)
                    ·
                      refine ⟨2578231039041901707720947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27501131083113618215690101 2578231039041901707720947)
                      ·
                        rfl

theorem cell23_5021087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 2, 5].length) (baseStart_5021087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021087 prefixEnd_5021087 := by exact prefixLift 5021087
  have htrace : WordTrace (prefixWord ++ tailWord_5021087) baseStart_5021087 baseEnd_5021087 := by
    simpa [prefixWord, tailWord_5021087, baseEnd_5021087] using wordTrace_append hprefix tailTrace_5021087
  have hstable : (prefixWord ++ tailWord_5021087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021087).length < 2 ^ (prefixWord ++ tailWord_5021087).sum := by decide
  have hdescent : baseEnd_5021087 < baseStart_5021087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021101 : List Nat := [1, 5, 2, 2, 1, 1, 1, 1, 2, 5, 2]
def baseStart_5021101 : Nat := 118140960795 + 5021101 * 2 ^ 59
def prefixEnd_5021101 : Nat := 4983230072969 + 3 ^ 40 * 5021101 * 2
def baseEnd_5021101 : Nat := 2578238227771064652945883

theorem tailTrace_5021101 : CollatzResearch.WordTrace tailWord_5021101 prefixEnd_5021101 2578238227771064652945883 := by
  unfold tailWord_5021101
  simp only [CollatzResearch.WordTrace]
  refine ⟨183134598582416087623999157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122089732388277391749332771 183134598582416087623999157)
  ·
    refine ⟨17168868617101508214749921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 183134598582416087623999157 17168868617101508214749921)
    ·
      refine ⟨12876651462826131161062441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17168868617101508214749921 12876651462826131161062441)
      ·
        refine ⟨9657488597119598370796831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12876651462826131161062441 9657488597119598370796831)
        ·
          refine ⟨14486232895679397556195247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9657488597119598370796831 14486232895679397556195247)
          ·
            refine ⟨21729349343519096334292871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14486232895679397556195247 21729349343519096334292871)
            ·
              refine ⟨32594024015278644501439307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21729349343519096334292871 32594024015278644501439307)
              ·
                refine ⟨48891036022917966752158961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32594024015278644501439307 48891036022917966752158961)
                ·
                  refine ⟨36668277017188475064119221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48891036022917966752158961 36668277017188475064119221)
                  ·
                    refine ⟨3437650970361419537261177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36668277017188475064119221 3437650970361419537261177)
                    ·
                      refine ⟨2578238227771064652945883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3437650970361419537261177 2578238227771064652945883)
                      ·
                        rfl

theorem cell23_5021101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 1, 1, 1, 2, 5, 2].length) (baseStart_5021101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021101 prefixEnd_5021101 := by exact prefixLift 5021101
  have htrace : WordTrace (prefixWord ++ tailWord_5021101) baseStart_5021101 baseEnd_5021101 := by
    simpa [prefixWord, tailWord_5021101, baseEnd_5021101] using wordTrace_append hprefix tailTrace_5021101
  have hstable : (prefixWord ++ tailWord_5021101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021101).length < 2 ^ (prefixWord ++ tailWord_5021101).sum := by decide
  have hdescent : baseEnd_5021101 < baseStart_5021101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021107 : List Nat := [1, 1, 1, 2, 3, 1, 1, 2, 7, 4]
def baseStart_5021107 : Nat := 118140960795 + 5021107 * 2 ^ 59
def prefixEnd_5021107 : Nat := 4983230072969 + 3 ^ 40 * 5021107 * 2
def baseEnd_5021107 : Nat := 859413769551663876490285

theorem tailTrace_5021107 : CollatzResearch.WordTrace tailWord_5021107 prefixEnd_5021107 859413769551663876490285 := by
  unfold tailWord_5021107
  simp only [CollatzResearch.WordTrace]
  refine ⟨183134817420394350648717575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122089878280262900432478383 183134817420394350648717575)
  ·
    refine ⟨274702226130591525973076363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183134817420394350648717575 274702226130591525973076363)
    ·
      refine ⟨412053339195887288959614545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274702226130591525973076363 412053339195887288959614545)
      ·
        refine ⟨309040004396915466719710909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412053339195887288959614545 309040004396915466719710909)
        ·
          refine ⟨115890001648843300019891591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 309040004396915466719710909 115890001648843300019891591)
          ·
            refine ⟨173835002473264950029837387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115890001648843300019891591 173835002473264950029837387)
            ·
              refine ⟨260752503709897425044756081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173835002473264950029837387 260752503709897425044756081)
              ·
                refine ⟨195564377782423068783567061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 260752503709897425044756081 195564377782423068783567061)
                ·
                  refine ⟨4583540104275540674614853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 195564377782423068783567061 4583540104275540674614853)
                  ·
                    refine ⟨859413769551663876490285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4583540104275540674614853 859413769551663876490285)
                    ·
                      rfl

theorem cell23_5021107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 2, 7, 4].length) (baseStart_5021107 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021107 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021107 prefixEnd_5021107 := by exact prefixLift 5021107
  have htrace : WordTrace (prefixWord ++ tailWord_5021107) baseStart_5021107 baseEnd_5021107 := by
    simpa [prefixWord, tailWord_5021107, baseEnd_5021107] using wordTrace_append hprefix tailTrace_5021107
  have hstable : (prefixWord ++ tailWord_5021107).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021107).length < 2 ^ (prefixWord ++ tailWord_5021107).sum := by decide
  have hdescent : baseEnd_5021107 < baseStart_5021107 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021167 : List Nat := [1, 1, 2, 1, 4, 1, 2, 1, 5, 5]
def baseStart_5021167 : Nat := 118140960795 + 5021167 * 2 ^ 59
def prefixEnd_5021167 : Nat := 4983230072969 + 3 ^ 40 * 5021167 * 2
def baseEnd_5021167 : Nat := 859424039164753798240193

theorem tailTrace_5021167 : CollatzResearch.WordTrace tailWord_5021167 prefixEnd_5021167 859424039164753798240193 := by
  unfold tailWord_5021167
  simp only [CollatzResearch.WordTrace]
  refine ⟨183137005800176980895901755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122091337200117987263934503 183137005800176980895901755)
  ·
    refine ⟨274705508700265471343852633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183137005800176980895901755 274705508700265471343852633)
    ·
      refine ⟨206029131525199103507889475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274705508700265471343852633 206029131525199103507889475)
      ·
        refine ⟨309043697287798655261834213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206029131525199103507889475 309043697287798655261834213)
        ·
          refine ⟨57945693241462247861593915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 309043697287798655261834213 57945693241462247861593915)
          ·
            refine ⟨86918539862193371792390873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57945693241462247861593915 86918539862193371792390873)
            ·
              refine ⟨65188904896645028844293155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86918539862193371792390873 65188904896645028844293155)
              ·
                refine ⟨97783357344967543266439733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65188904896645028844293155 97783357344967543266439733)
                ·
                  refine ⟨9167189751090707181228725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97783357344967543266439733 9167189751090707181228725)
                  ·
                    refine ⟨859424039164753798240193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9167189751090707181228725 859424039164753798240193)
                    ·
                      rfl

theorem cell23_5021167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 1, 5, 5].length) (baseStart_5021167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021167 prefixEnd_5021167 := by exact prefixLift 5021167
  have htrace : WordTrace (prefixWord ++ tailWord_5021167) baseStart_5021167 baseEnd_5021167 := by
    simpa [prefixWord, tailWord_5021167, baseEnd_5021167] using wordTrace_append hprefix tailTrace_5021167
  have hstable : (prefixWord ++ tailWord_5021167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021167).length < 2 ^ (prefixWord ++ tailWord_5021167).sum := by decide
  have hdescent : baseEnd_5021167 < baseStart_5021167 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021181 : List Nat := [1, 4, 1, 1, 1, 4, 2, 2, 3, 1, 3]
def baseStart_5021181 : Nat := 118140960795 + 5021181 * 2 ^ 59
def prefixEnd_5021181 : Nat := 4983230072969 + 3 ^ 40 * 5021181 * 2
def baseEnd_5021181 : Nat := 2578279306223424339945515

theorem tailTrace_5021181 : CollatzResearch.WordTrace tailWord_5021181 prefixEnd_5021181 2578279306223424339945515 := by
  unfold tailWord_5021181
  simp only [CollatzResearch.WordTrace]
  refine ⟨183137516422126261286911397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122091677614750840857940931 183137516422126261286911397)
  ·
    refine ⟨34338284329148673991295887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183137516422126261286911397 34338284329148673991295887)
    ·
      refine ⟨51507426493723010986943831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34338284329148673991295887 51507426493723010986943831)
      ·
        refine ⟨77261139740584516480415747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51507426493723010986943831 77261139740584516480415747)
        ·
          refine ⟨115891709610876774720623621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77261139740584516480415747 115891709610876774720623621)
          ·
            refine ⟨21729695552039395260116929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115891709610876774720623621 21729695552039395260116929)
            ·
              refine ⟨16297271664029546445087697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21729695552039395260116929 16297271664029546445087697)
              ·
                refine ⟨12222953748022159833815773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16297271664029546445087697 12222953748022159833815773)
                ·
                  refine ⟨4583607655508309937680915, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12222953748022159833815773 4583607655508309937680915)
                  ·
                    refine ⟨6875411483262464906521373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4583607655508309937680915 6875411483262464906521373)
                    ·
                      refine ⟨2578279306223424339945515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6875411483262464906521373 2578279306223424339945515)
                      ·
                        rfl

theorem cell23_5021181_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 2, 3, 1, 3].length) (baseStart_5021181 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021181 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021181 prefixEnd_5021181 := by exact prefixLift 5021181
  have htrace : WordTrace (prefixWord ++ tailWord_5021181) baseStart_5021181 baseEnd_5021181 := by
    simpa [prefixWord, tailWord_5021181, baseEnd_5021181] using wordTrace_append hprefix tailTrace_5021181
  have hstable : (prefixWord ++ tailWord_5021181).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021181).length < 2 ^ (prefixWord ++ tailWord_5021181).sum := by decide
  have hdescent : baseEnd_5021181 < baseStart_5021181 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021181) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021191 : List Nat := [1, 1, 4, 3, 2, 1, 2, 1, 1, 5, 2]
def baseStart_5021191 : Nat := 118140960795 + 5021191 * 2 ^ 59
def prefixEnd_5021191 : Nat := 4983230072969 + 3 ^ 40 * 5021191 * 2
def baseEnd_5021191 : Nat := 2578284441029969300820469

theorem tailTrace_5021191 : CollatzResearch.WordTrace tailWord_5021191 prefixEnd_5021191 2578284441029969300820469 := by
  unfold tailWord_5021191
  simp only [CollatzResearch.WordTrace]
  refine ⟨183137881152090032994775427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122091920768060021996516951 183137881152090032994775427)
  ·
    refine ⟨274706821728135049492163141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183137881152090032994775427 274706821728135049492163141)
    ·
      refine ⟨51507529074025321779780589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 274706821728135049492163141 51507529074025321779780589)
      ·
        refine ⟨19315323402759495667417721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51507529074025321779780589 19315323402759495667417721)
        ·
          refine ⟨14486492552069621750563291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19315323402759495667417721 14486492552069621750563291)
          ·
            refine ⟨21729738828104432625844937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14486492552069621750563291 21729738828104432625844937)
            ·
              refine ⟨16297304121078324469383703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21729738828104432625844937 16297304121078324469383703)
              ·
                refine ⟨24445956181617486704075555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16297304121078324469383703 24445956181617486704075555)
                ·
                  refine ⟨36668934272426230056113333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24445956181617486704075555 36668934272426230056113333)
                  ·
                    refine ⟨3437712588039959067760625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36668934272426230056113333 3437712588039959067760625)
                    ·
                      refine ⟨2578284441029969300820469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3437712588039959067760625 2578284441029969300820469)
                      ·
                        rfl

theorem cell23_5021191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_5021191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021191 prefixEnd_5021191 := by exact prefixLift 5021191
  have htrace : WordTrace (prefixWord ++ tailWord_5021191) baseStart_5021191 baseEnd_5021191 := by
    simpa [prefixWord, tailWord_5021191, baseEnd_5021191] using wordTrace_append hprefix tailTrace_5021191
  have hstable : (prefixWord ++ tailWord_5021191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021191).length < 2 ^ (prefixWord ++ tailWord_5021191).sum := by decide
  have hdescent : baseEnd_5021191 < baseStart_5021191 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021208 : List Nat := [2, 1, 2, 3, 4, 1, 1, 2, 2, 3, 2]
def baseStart_5021208 : Nat := 118140960795 + 5021208 * 2 ^ 59
def prefixEnd_5021208 : Nat := 4983230072969 + 3 ^ 40 * 5021208 * 2
def baseEnd_5021208 : Nat := 2578293170201095734307891

theorem tailTrace_5021208 : CollatzResearch.WordTrace tailWord_5021208 prefixEnd_5021208 2578293170201095734307891 := by
  unfold tailWord_5021208
  simp only [CollatzResearch.WordTrace]
  refine ⟨91569250596514222449072139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122092334128685629932096185 91569250596514222449072139)
  ·
    refine ⟨137353875894771333673608209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91569250596514222449072139 137353875894771333673608209)
    ·
      refine ⟨103015406921078500255206157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137353875894771333673608209 103015406921078500255206157)
      ·
        refine ⟨38630777595404437595702309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103015406921078500255206157 38630777595404437595702309)
        ·
          refine ⟨7243270799138332049194183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38630777595404437595702309 7243270799138332049194183)
          ·
            refine ⟨10864906198707498073791275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7243270799138332049194183 10864906198707498073791275)
            ·
              refine ⟨16297359298061247110686913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10864906198707498073791275 16297359298061247110686913)
              ·
                refine ⟨12223019473545935333015185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16297359298061247110686913 12223019473545935333015185)
                ·
                  refine ⟨9167264605159451499761389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12223019473545935333015185 9167264605159451499761389)
                  ·
                    refine ⟨3437724226934794312410521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9167264605159451499761389 3437724226934794312410521)
                    ·
                      refine ⟨2578293170201095734307891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3437724226934794312410521 2578293170201095734307891)
                      ·
                        rfl

theorem cell23_5021208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_5021208 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021208 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021208 prefixEnd_5021208 := by exact prefixLift 5021208
  have htrace : WordTrace (prefixWord ++ tailWord_5021208) baseStart_5021208 baseEnd_5021208 := by
    simpa [prefixWord, tailWord_5021208, baseEnd_5021208] using wordTrace_append hprefix tailTrace_5021208
  have hstable : (prefixWord ++ tailWord_5021208).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021208).length < 2 ^ (prefixWord ++ tailWord_5021208).sum := by decide
  have hdescent : baseEnd_5021208 < baseStart_5021208 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021234 : List Nat := [3, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4]
def baseStart_5021234 : Nat := 118140960795 + 5021234 * 2 ^ 59
def prefixEnd_5021234 : Nat := 4983230072969 + 3 ^ 40 * 5021234 * 2
def baseEnd_5021234 : Nat := 2578306520698112632582771

theorem tailTrace_5021234 : CollatzResearch.WordTrace tailWord_5021234 prefixEnd_5021234 2578306520698112632582771 := by
  unfold tailWord_5021234
  simp only [CollatzResearch.WordTrace]
  refine ⟨45784862372733562834647689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122092966327289500892393837 45784862372733562834647689)
  ·
    refine ⟨34338646779550172125985767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45784862372733562834647689 34338646779550172125985767)
    ·
      refine ⟨51507970169325258188978651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34338646779550172125985767 51507970169325258188978651)
      ·
        refine ⟨77261955253987887283467977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51507970169325258188978651 77261955253987887283467977)
        ·
          refine ⟨57946466440490915462600983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77261955253987887283467977 57946466440490915462600983)
          ·
            refine ⟨86919699660736373193901475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57946466440490915462600983 86919699660736373193901475)
            ·
              refine ⟨130379549491104559790852213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86919699660736373193901475 130379549491104559790852213)
              ·
                refine ⟨12223082764791052480392395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 130379549491104559790852213 12223082764791052480392395)
                ·
                  refine ⟨18334624147186578720588593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12223082764791052480392395 18334624147186578720588593)
                  ·
                    refine ⟨13750968110389934040441445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18334624147186578720588593 13750968110389934040441445)
                    ·
                      refine ⟨2578306520698112632582771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13750968110389934040441445 2578306520698112632582771)
                      ·
                        rfl

theorem cell23_5021234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 5, 1, 2, 4].length) (baseStart_5021234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021234 prefixEnd_5021234 := by exact prefixLift 5021234
  have htrace : WordTrace (prefixWord ++ tailWord_5021234) baseStart_5021234 baseEnd_5021234 := by
    simpa [prefixWord, tailWord_5021234, baseEnd_5021234] using wordTrace_append hprefix tailTrace_5021234
  have hstable : (prefixWord ++ tailWord_5021234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021234).length < 2 ^ (prefixWord ++ tailWord_5021234).sum := by decide
  have hdescent : baseEnd_5021234 < baseStart_5021234 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021238 : List Nat := [5, 1, 2, 1, 3, 1, 1, 1, 3, 1, 4]
def baseStart_5021238 : Nat := 118140960795 + 5021238 * 2 ^ 59
def prefixEnd_5021238 : Nat := 4983230072969 + 3 ^ 40 * 5021238 * 2
def baseEnd_5021238 : Nat := 2578308574620730616932753

theorem tailTrace_5021238 : CollatzResearch.WordTrace tailWord_5021238 prefixEnd_5021238 2578308574620730616932753 := by
  unfold tailWord_5021238
  simp only [CollatzResearch.WordTrace]
  refine ⟨11446224711432485001358523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122093063588613173347824245 11446224711432485001358523)
  ·
    refine ⟨17169337067148727502037785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11446224711432485001358523 17169337067148727502037785)
    ·
      refine ⟨12877002800361545626528339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17169337067148727502037785 12877002800361545626528339)
      ·
        refine ⟨19315504200542318439792509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12877002800361545626528339 19315504200542318439792509)
        ·
          refine ⟨7243314075203369414922191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19315504200542318439792509 7243314075203369414922191)
          ·
            refine ⟨10864971112805054122383287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7243314075203369414922191 10864971112805054122383287)
            ·
              refine ⟨16297456669207581183574931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10864971112805054122383287 16297456669207581183574931)
              ·
                refine ⟨24446185003811371775362397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16297456669207581183574931 24446185003811371775362397)
                ·
                  refine ⟨9167319376429264415760899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24446185003811371775362397 9167319376429264415760899)
                  ·
                    refine ⟨13750979064643896623641349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9167319376429264415760899 13750979064643896623641349)
                    ·
                      refine ⟨2578308574620730616932753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13750979064643896623641349 2578308574620730616932753)
                      ·
                        rfl

theorem cell23_5021238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_5021238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021238 prefixEnd_5021238 := by exact prefixLift 5021238
  have htrace : WordTrace (prefixWord ++ tailWord_5021238) baseStart_5021238 baseEnd_5021238 := by
    simpa [prefixWord, tailWord_5021238, baseEnd_5021238] using wordTrace_append hprefix tailTrace_5021238
  have hstable : (prefixWord ++ tailWord_5021238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021238).length < 2 ^ (prefixWord ++ tailWord_5021238).sum := by decide
  have hdescent : baseEnd_5021238 < baseStart_5021238 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021241 : List Nat := [1, 2, 1, 5, 1, 3, 1, 1, 3, 2, 3]
def baseStart_5021241 : Nat := 118140960795 + 5021241 * 2 ^ 59
def prefixEnd_5021241 : Nat := 4983230072969 + 3 ^ 40 * 5021241 * 2
def baseEnd_5021241 : Nat := 2578310115062694105195239

theorem tailTrace_5021241 : CollatzResearch.WordTrace tailWord_5021241 prefixEnd_5021241 2578310115062694105195239 := by
  unfold tailWord_5021241
  simp only [CollatzResearch.WordTrace]
  refine ⟨183139704801908891534095577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122093136534605927689397051 183139704801908891534095577)
  ·
    refine ⟨137354778601431668650571683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183139704801908891534095577 137354778601431668650571683)
    ·
      refine ⟨206032167902147502975857525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137354778601431668650571683 206032167902147502975857525)
      ·
        refine ⟨19315515740826328403986643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 206032167902147502975857525 19315515740826328403986643)
        ·
          refine ⟨28973273611239492605979965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19315515740826328403986643 28973273611239492605979965)
          ·
            refine ⟨10864977604214809727242487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28973273611239492605979965 10864977604214809727242487)
            ·
              refine ⟨16297466406322214590863731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10864977604214809727242487 16297466406322214590863731)
              ·
                refine ⟨24446199609483321886295597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16297466406322214590863731 24446199609483321886295597)
                ·
                  refine ⟨9167324853556245707360849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24446199609483321886295597 9167324853556245707360849)
                  ·
                    refine ⟨6875493640167184280520637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9167324853556245707360849 6875493640167184280520637)
                    ·
                      refine ⟨2578310115062694105195239, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6875493640167184280520637 2578310115062694105195239)
                      ·
                        rfl

theorem cell23_5021241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 1, 3, 2, 3].length) (baseStart_5021241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021241 prefixEnd_5021241 := by exact prefixLift 5021241
  have htrace : WordTrace (prefixWord ++ tailWord_5021241) baseStart_5021241 baseEnd_5021241 := by
    simpa [prefixWord, tailWord_5021241, baseEnd_5021241] using wordTrace_append hprefix tailTrace_5021241
  have hstable : (prefixWord ++ tailWord_5021241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021241).length < 2 ^ (prefixWord ++ tailWord_5021241).sum := by decide
  have hdescent : baseEnd_5021241 < baseStart_5021241 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021257 : List Nat := [1, 2, 1, 1, 2, 2, 1, 2, 4, 7]
def baseStart_5021257 : Nat := 118140960795 + 5021257 * 2 ^ 59
def prefixEnd_5021257 : Nat := 4983230072969 + 3 ^ 40 * 5021257 * 2
def baseEnd_5021257 : Nat := 859439443584388680865055

theorem tailTrace_5021257 : CollatzResearch.WordTrace tailWord_5021257 prefixEnd_5021257 859439443584388680865055 := by
  unfold tailWord_5021257
  simp only [CollatzResearch.WordTrace]
  refine ⟨183140288369850926266678025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122093525579900617511118683 183140288369850926266678025)
  ·
    refine ⟨137355216277388194700008519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183140288369850926266678025 137355216277388194700008519)
    ·
      refine ⟨206032824416082292050012779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137355216277388194700008519 206032824416082292050012779)
      ·
        refine ⟨309049236624123438075019169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206032824416082292050012779 309049236624123438075019169)
        ·
          refine ⟨231786927468092578556264377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309049236624123438075019169 231786927468092578556264377)
          ·
            refine ⟨173840195601069433917198283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231786927468092578556264377 173840195601069433917198283)
            ·
              refine ⟨260760293401604150875797425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173840195601069433917198283 260760293401604150875797425)
              ·
                refine ⟨195570220051203113156848069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 260760293401604150875797425 195570220051203113156848069)
                ·
                  refine ⟨36669416259600583716909013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 195570220051203113156848069 36669416259600583716909013)
                  ·
                    refine ⟨859439443584388680865055, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36669416259600583716909013 859439443584388680865055)
                    ·
                      rfl

theorem cell23_5021257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 1, 2, 4, 7].length) (baseStart_5021257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021257 prefixEnd_5021257 := by exact prefixLift 5021257
  have htrace : WordTrace (prefixWord ++ tailWord_5021257) baseStart_5021257 baseEnd_5021257 := by
    simpa [prefixWord, tailWord_5021257, baseEnd_5021257] using wordTrace_append hprefix tailTrace_5021257
  have hstable : (prefixWord ++ tailWord_5021257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021257).length < 2 ^ (prefixWord ++ tailWord_5021257).sum := by decide
  have hdescent : baseEnd_5021257 < baseStart_5021257 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021258 : List Nat := [3, 1, 2, 1, 1, 3, 5, 1, 1, 2, 3]
def baseStart_5021258 : Nat := 118140960795 + 5021258 * 2 ^ 59
def prefixEnd_5021258 : Nat := 4983230072969 + 3 ^ 40 * 5021258 * 2
def baseEnd_5021258 : Nat := 2578318844233820538682661

theorem tailTrace_5021258 : CollatzResearch.WordTrace tailWord_5021258 prefixEnd_5021258 2578318844233820538682661 := by
  unfold tailWord_5021258
  simp only [CollatzResearch.WordTrace]
  refine ⟨45785081210711825859366107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122093549895231535624976285 45785081210711825859366107)
  ·
    refine ⟨68677621816067738789049161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45785081210711825859366107 68677621816067738789049161)
    ·
      refine ⟨51508216362050804091786871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68677621816067738789049161 51508216362050804091786871)
      ·
        refine ⟨77262324543076206137680307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51508216362050804091786871 77262324543076206137680307)
        ·
          refine ⟨115893486814614309206520461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77262324543076206137680307 115893486814614309206520461)
          ·
            refine ⟨43460057555480365952445173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115893486814614309206520461 43460057555480365952445173)
            ·
              refine ⟨4074380395826284308041735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43460057555480365952445173 4074380395826284308041735)
              ·
                refine ⟨6111570593739426462062603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4074380395826284308041735 6111570593739426462062603)
                ·
                  refine ⟨9167355890609139693093905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6111570593739426462062603 9167355890609139693093905)
                  ·
                    refine ⟨6875516917956854769820429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9167355890609139693093905 6875516917956854769820429)
                    ·
                      refine ⟨2578318844233820538682661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6875516917956854769820429 2578318844233820538682661)
                      ·
                        rfl

theorem cell23_5021258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 5, 1, 1, 2, 3].length) (baseStart_5021258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021258 prefixEnd_5021258 := by exact prefixLift 5021258
  have htrace : WordTrace (prefixWord ++ tailWord_5021258) baseStart_5021258 baseEnd_5021258 := by
    simpa [prefixWord, tailWord_5021258, baseEnd_5021258] using wordTrace_append hprefix tailTrace_5021258
  have hstable : (prefixWord ++ tailWord_5021258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021258).length < 2 ^ (prefixWord ++ tailWord_5021258).sum := by decide
  have hdescent : baseEnd_5021258 < baseStart_5021258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021261 : List Nat := [1, 6, 1, 1, 4, 10]
def baseStart_5021261 : Nat := 118140960795 + 5021261 * 2 ^ 59
def prefixEnd_5021261 : Nat := 4983230072969 + 3 ^ 40 * 5021261 * 2
def baseEnd_5021261 : Nat := 10610371953398288176729

theorem tailTrace_5021261 : CollatzResearch.WordTrace tailWord_5021261 prefixEnd_5021261 10610371953398288176729 := by
  unfold tailWord_5021261
  simp only [CollatzResearch.WordTrace]
  refine ⟨183140434261836434949823637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122093622841224289966549091 183140434261836434949823637)
  ·
    refine ⟨8584707856023582888272983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 183140434261836434949823637 8584707856023582888272983)
    ·
      refine ⟨12877061784035374332409475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8584707856023582888272983 12877061784035374332409475)
      ·
        refine ⟨19315592676053061498614213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12877061784035374332409475 19315592676053061498614213)
        ·
          refine ⟨3621673626759949030990165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19315592676053061498614213 3621673626759949030990165)
          ·
            refine ⟨10610371953398288176729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3621673626759949030990165 10610371953398288176729)
            ·
              rfl

theorem cell23_5021261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 4, 10].length) (baseStart_5021261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021261 prefixEnd_5021261 := by exact prefixLift 5021261
  have htrace : WordTrace (prefixWord ++ tailWord_5021261) baseStart_5021261 baseEnd_5021261 := by
    simpa [prefixWord, tailWord_5021261, baseEnd_5021261] using wordTrace_append hprefix tailTrace_5021261
  have hstable : (prefixWord ++ tailWord_5021261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021261).length < 2 ^ (prefixWord ++ tailWord_5021261).sum := by decide
  have hdescent : baseEnd_5021261 < baseStart_5021261 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021281 : List Nat := [1, 2, 3, 1, 1, 3, 1, 1, 5, 3, 2]
def baseStart_5021281 : Nat := 118140960795 + 5021281 * 2 ^ 59
def prefixEnd_5021281 : Nat := 4983230072969 + 3 ^ 40 * 5021281 * 2
def baseEnd_5021281 : Nat := 2578330654288873948695055

theorem tailTrace_5021281 : CollatzResearch.WordTrace tailWord_5021281 prefixEnd_5021281 2578330654288873948695055 := by
  unfold tailWord_5021281
  simp only [CollatzResearch.WordTrace]
  refine ⟨183141163721763978365551697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122094109147842652243701131 183141163721763978365551697)
  ·
    refine ⟨137355872791322983774163773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183141163721763978365551697 137355872791322983774163773)
    ·
      refine ⟨51508452296746118915311415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137355872791322983774163773 51508452296746118915311415)
      ·
        refine ⟨77262678445119178372967123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51508452296746118915311415 77262678445119178372967123)
        ·
          refine ⟨115894017667678767559450685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77262678445119178372967123 115894017667678767559450685)
          ·
            refine ⟨43460256625379537834794007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115894017667678767559450685 43460256625379537834794007)
            ·
              refine ⟨65190384938069306752191011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43460256625379537834794007 65190384938069306752191011)
              ·
                refine ⟨97785577407103960128286517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65190384938069306752191011 97785577407103960128286517)
                ·
                  refine ⟨9167397881915996262026861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 97785577407103960128286517 9167397881915996262026861)
                  ·
                    refine ⟨3437774205718498598260073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9167397881915996262026861 3437774205718498598260073)
                    ·
                      refine ⟨2578330654288873948695055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3437774205718498598260073 2578330654288873948695055)
                      ·
                        rfl

theorem cell23_5021281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 1, 1, 5, 3, 2].length) (baseStart_5021281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021281 prefixEnd_5021281 := by exact prefixLift 5021281
  have htrace : WordTrace (prefixWord ++ tailWord_5021281) baseStart_5021281 baseEnd_5021281 := by
    simpa [prefixWord, tailWord_5021281, baseEnd_5021281] using wordTrace_append hprefix tailTrace_5021281
  have hstable : (prefixWord ++ tailWord_5021281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021281).length < 2 ^ (prefixWord ++ tailWord_5021281).sum := by decide
  have hdescent : baseEnd_5021281 < baseStart_5021281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021288 : List Nat := [2, 1, 4, 3, 1, 2, 2, 1, 1, 3, 3]
def baseStart_5021288 : Nat := 118140960795 + 5021288 * 2 ^ 59
def prefixEnd_5021288 : Nat := 4983230072969 + 3 ^ 40 * 5021288 * 2
def baseEnd_5021288 : Nat := 2578334248653455421307523

theorem tailTrace_5021288 : CollatzResearch.WordTrace tailWord_5021288 prefixEnd_5021288 2578334248653455421307523 := by
  unfold tailWord_5021288
  simp only [CollatzResearch.WordTrace]
  refine ⟨91570709516369309280528259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122094279355159079040704345 91570709516369309280528259)
  ·
    refine ⟨137356064274553963920792389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91570709516369309280528259 137356064274553963920792389)
    ·
      refine ⟨25754262051478868235148573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137356064274553963920792389 25754262051478868235148573)
      ·
        refine ⟨9657848269304575588180715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25754262051478868235148573 9657848269304575588180715)
        ·
          refine ⟨14486772403956863382271073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9657848269304575588180715 14486772403956863382271073)
          ·
            refine ⟨10865079302967647536703305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14486772403956863382271073 10865079302967647536703305)
            ·
              refine ⟨8148809477225735652527479, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10865079302967647536703305 8148809477225735652527479)
              ·
                refine ⟨12223214215838603478791219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8148809477225735652527479 12223214215838603478791219)
                ·
                  refine ⟨18334821323757905218186829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12223214215838603478791219 18334821323757905218186829)
                  ·
                    refine ⟨6875557996409214456820061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18334821323757905218186829 6875557996409214456820061)
                    ·
                      refine ⟨2578334248653455421307523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6875557996409214456820061 2578334248653455421307523)
                      ·
                        rfl

theorem cell23_5021288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_5021288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021288 prefixEnd_5021288 := by exact prefixLift 5021288
  have htrace : WordTrace (prefixWord ++ tailWord_5021288) baseStart_5021288 baseEnd_5021288 := by
    simpa [prefixWord, tailWord_5021288, baseEnd_5021288] using wordTrace_append hprefix tailTrace_5021288
  have hstable : (prefixWord ++ tailWord_5021288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021288).length < 2 ^ (prefixWord ++ tailWord_5021288).sum := by decide
  have hdescent : baseEnd_5021288 < baseStart_5021288 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021298 : List Nat := [3, 2, 1, 2, 3, 1, 2, 1, 3, 3, 2]
def baseStart_5021298 : Nat := 118140960795 + 5021298 * 2 ^ 59
def prefixEnd_5021298 : Nat := 4983230072969 + 3 ^ 40 * 5021298 * 2
def baseEnd_5021298 : Nat := 2578339383460000382182477

theorem tailTrace_5021298 : CollatzResearch.WordTrace tailWord_5021298 prefixEnd_5021298 2578339383460000382182477 := by
  unfold tailWord_5021298
  simp only [CollatzResearch.WordTrace]
  refine ⟨45785445940675597567230137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122094522508468260179280365 45785445940675597567230137)
  ·
    refine ⟨34339084455506698175422603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45785445940675597567230137 34339084455506698175422603)
    ·
      refine ⟨51508626683260047263133905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34339084455506698175422603 51508626683260047263133905)
      ·
        refine ⟨38631470012445035447350429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51508626683260047263133905 38631470012445035447350429)
        ·
          refine ⟨14486801254666888292756411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38631470012445035447350429 14486801254666888292756411)
          ·
            refine ⟨21730201882000332439134617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14486801254666888292756411 21730201882000332439134617)
            ·
              refine ⟨16297651411500249329350963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21730201882000332439134617 16297651411500249329350963)
              ·
                refine ⟨24446477117250373994026445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16297651411500249329350963 24446477117250373994026445)
                ·
                  refine ⟨9167428918968890247759917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24446477117250373994026445 9167428918968890247759917)
                  ·
                    refine ⟨3437785844613333842909969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9167428918968890247759917 3437785844613333842909969)
                    ·
                      refine ⟨2578339383460000382182477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3437785844613333842909969 2578339383460000382182477)
                      ·
                        rfl

theorem cell23_5021298_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_5021298 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021298 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021298 prefixEnd_5021298 := by exact prefixLift 5021298
  have htrace : WordTrace (prefixWord ++ tailWord_5021298) baseStart_5021298 baseEnd_5021298 := by
    simpa [prefixWord, tailWord_5021298, baseEnd_5021298] using wordTrace_append hprefix tailTrace_5021298
  have hstable : (prefixWord ++ tailWord_5021298).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021298).length < 2 ^ (prefixWord ++ tailWord_5021298).sum := by decide
  have hdescent : baseEnd_5021298 < baseStart_5021298 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021298) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021324 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 4, 2, 4]
def baseStart_5021324 : Nat := 118140960795 + 5021324 * 2 ^ 59
def prefixEnd_5021324 : Nat := 4983230072969 + 3 ^ 40 * 5021324 * 2
def baseEnd_5021324 : Nat := 2578352733957017280457357

theorem tailTrace_5021324 : CollatzResearch.WordTrace tailWord_5021324 prefixEnd_5021324 2578352733957017280457357 := by
  unfold tailWord_5021324
  simp only [CollatzResearch.WordTrace]
  refine ⟨91571366030304098354683513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122095154707072131139578017 91571366030304098354683513)
  ·
    refine ⟨68678524522728073766012635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91571366030304098354683513 68678524522728073766012635)
    ·
      refine ⟨103017786784092110649018953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68678524522728073766012635 103017786784092110649018953)
      ·
        refine ⟨77263340088069082986764215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103017786784092110649018953 77263340088069082986764215)
        ·
          refine ⟨115895010132103624480146323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77263340088069082986764215 115895010132103624480146323)
          ·
            refine ⟨173842515198155436720219485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115895010132103624480146323 173842515198155436720219485)
            ·
              refine ⟨65190943199308288770082307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173842515198155436720219485 65190943199308288770082307)
              ·
                refine ⟨97786414798962433155123461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65190943199308288770082307 97786414798962433155123461)
                ·
                  refine ⟨18334952774805456216585649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97786414798962433155123461 18334952774805456216585649)
                  ·
                    refine ⟨13751214581104092162439237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18334952774805456216585649 13751214581104092162439237)
                    ·
                      refine ⟨2578352733957017280457357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13751214581104092162439237 2578352733957017280457357)
                      ·
                        rfl

theorem cell23_5021324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 4, 2, 4].length) (baseStart_5021324 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021324 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021324 prefixEnd_5021324 := by exact prefixLift 5021324
  have htrace : WordTrace (prefixWord ++ tailWord_5021324) baseStart_5021324 baseEnd_5021324 := by
    simpa [prefixWord, tailWord_5021324, baseEnd_5021324] using wordTrace_append hprefix tailTrace_5021324
  have hstable : (prefixWord ++ tailWord_5021324).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021324).length < 2 ^ (prefixWord ++ tailWord_5021324).sum := by decide
  have hdescent : baseEnd_5021324 < baseStart_5021324 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021345 : List Nat := [1, 2, 3, 3, 2, 3, 1, 1, 1, 4, 2]
def baseStart_5021345 : Nat := 118140960795 + 5021345 * 2 ^ 59
def prefixEnd_5021345 : Nat := 4983230072969 + 3 ^ 40 * 5021345 * 2
def baseEnd_5021345 : Nat := 2578363517050761698294761

theorem tailTrace_5021345 : CollatzResearch.WordTrace tailWord_5021345 prefixEnd_5021345 2578363517050761698294761 := by
  unfold tailWord_5021345
  simp only [CollatzResearch.WordTrace]
  refine ⟨183143497993532117295881489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122095665329021411530587659 183143497993532117295881489)
  ·
    refine ⟨137357623495149087971911117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183143497993532117295881489 137357623495149087971911117)
    ·
      refine ⟨51509108810680907989466669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137357623495149087971911117 51509108810680907989466669)
      ·
        refine ⟨19315915804005340496050001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51509108810680907989466669 19315915804005340496050001)
        ·
          refine ⟨14486936853004005372037501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19315915804005340496050001 14486936853004005372037501)
          ·
            refine ⟨5432601319876502014514063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14486936853004005372037501 5432601319876502014514063)
            ·
              refine ⟨8148901979814753021771095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5432601319876502014514063 8148901979814753021771095)
              ·
                refine ⟨12223352969722129532656643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8148901979814753021771095 12223352969722129532656643)
                ·
                  refine ⟨18335029454583194298984965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12223352969722129532656643 18335029454583194298984965)
                  ·
                    refine ⟨3437818022734348931059681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18335029454583194298984965 3437818022734348931059681)
                    ·
                      refine ⟨2578363517050761698294761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3437818022734348931059681 2578363517050761698294761)
                      ·
                        rfl

theorem cell23_5021345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_5021345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021345 prefixEnd_5021345 := by exact prefixLift 5021345
  have htrace : WordTrace (prefixWord ++ tailWord_5021345) baseStart_5021345 baseEnd_5021345 := by
    simpa [prefixWord, tailWord_5021345, baseEnd_5021345] using wordTrace_append hprefix tailTrace_5021345
  have hstable : (prefixWord ++ tailWord_5021345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021345).length < 2 ^ (prefixWord ++ tailWord_5021345).sum := by decide
  have hdescent : baseEnd_5021345 < baseStart_5021345 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021415 : List Nat := [1, 1, 5, 4, 1, 1, 2, 1, 2, 5]
def baseStart_5021415 : Nat := 118140960795 + 5021415 * 2 ^ 59
def prefixEnd_5021415 : Nat := 4983230072969 + 3 ^ 40 * 5021415 * 2
def baseEnd_5021415 : Nat := 859466486898858808139813

theorem tailTrace_5021415 : CollatzResearch.WordTrace tailWord_5021415 prefixEnd_5021415 859466486898858808139813 := by
  unfold tailWord_5021415
  simp only [CollatzResearch.WordTrace]
  refine ⟨183146051103278519250929699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122097367402185679500619799 183146051103278519250929699)
  ·
    refine ⟨274719076654917778876394549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183146051103278519250929699 274719076654917778876394549)
    ·
      refine ⟨25754913436398541769661989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 274719076654917778876394549 25754913436398541769661989)
      ·
        refine ⟨4829046269324726581811623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25754913436398541769661989 4829046269324726581811623)
        ·
          refine ⟨7243569403987089872717435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4829046269324726581811623 7243569403987089872717435)
          ·
            refine ⟨10865354105980634809076153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7243569403987089872717435 10865354105980634809076153)
            ·
              refine ⟨8149015579485476106807115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10865354105980634809076153 8149015579485476106807115)
              ·
                refine ⟨12223523369228214160210673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8149015579485476106807115 12223523369228214160210673)
                ·
                  refine ⟨9167642526921160620158005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12223523369228214160210673 9167642526921160620158005)
                  ·
                    refine ⟨859466486898858808139813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9167642526921160620158005 859466486898858808139813)
                    ·
                      rfl

theorem cell23_5021415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 1, 2, 1, 2, 5].length) (baseStart_5021415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021415 prefixEnd_5021415 := by exact prefixLift 5021415
  have htrace : WordTrace (prefixWord ++ tailWord_5021415) baseStart_5021415 baseEnd_5021415 := by
    simpa [prefixWord, tailWord_5021415, baseEnd_5021415] using wordTrace_append hprefix tailTrace_5021415
  have hstable : (prefixWord ++ tailWord_5021415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021415).length < 2 ^ (prefixWord ++ tailWord_5021415).sum := by decide
  have hdescent : baseEnd_5021415 < baseStart_5021415 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021424 : List Nat := [2, 1, 1, 1, 3, 1, 2, 4, 8]
def baseStart_5021424 : Nat := 118140960795 + 5021424 * 2 ^ 59
def prefixEnd_5021424 : Nat := 4983230072969 + 3 ^ 40 * 5021424 * 2
def baseEnd_5021424 : Nat := 286489342446940765467433

theorem tailTrace_5021424 : CollatzResearch.WordTrace tailWord_5021424 prefixEnd_5021424 286489342446940765467433 := by
  unfold tailWord_5021424
  simp only [CollatzResearch.WordTrace]
  refine ⟨91573189680122956894003663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122097586240163942525338217 91573189680122956894003663)
  ·
    refine ⟨137359784520184435341005495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91573189680122956894003663 137359784520184435341005495)
    ·
      refine ⟨206039676780276653011508243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137359784520184435341005495 206039676780276653011508243)
      ·
        refine ⟨309059515170414979517262365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206039676780276653011508243 309059515170414979517262365)
        ·
          refine ⟨115897318188905617318973387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 309059515170414979517262365 115897318188905617318973387)
          ·
            refine ⟨173845977283358425978460081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115897318188905617318973387 173845977283358425978460081)
            ·
              refine ⟨130384482962518819483845061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173845977283358425978460081 130384482962518819483845061)
              ·
                refine ⟨24447090555472278653220949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130384482962518819483845061 24447090555472278653220949)
                ·
                  refine ⟨286489342446940765467433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 24447090555472278653220949 286489342446940765467433)
                  ·
                    rfl

theorem cell23_5021424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 2, 4, 8].length) (baseStart_5021424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021424 prefixEnd_5021424 := by exact prefixLift 5021424
  have htrace : WordTrace (prefixWord ++ tailWord_5021424) baseStart_5021424 baseEnd_5021424 := by
    simpa [prefixWord, tailWord_5021424, baseEnd_5021424] using wordTrace_append hprefix tailTrace_5021424
  have hstable : (prefixWord ++ tailWord_5021424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021424).length < 2 ^ (prefixWord ++ tailWord_5021424).sum := by decide
  have hdescent : baseEnd_5021424 < baseStart_5021424 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021441 : List Nat := [1, 2, 4, 1, 1, 1, 3, 4, 6]
def baseStart_5021441 : Nat := 118140960795 + 5021441 * 2 ^ 59
def prefixEnd_5021441 : Nat := 4983230072969 + 3 ^ 40 * 5021441 * 2
def baseEnd_5021441 : Nat := 286490312354843702521591

theorem tailTrace_5021441 : CollatzResearch.WordTrace tailWord_5021441 prefixEnd_5021441 286490312354843702521591 := by
  unfold tailWord_5021441
  simp only [CollatzResearch.WordTrace]
  refine ⟨183146999401184325691376177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122097999600789550460917451 183146999401184325691376177)
  ·
    refine ⟨137360249550888244268532133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183146999401184325691376177 137360249550888244268532133)
    ·
      refine ⟨25755046790791545800349775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137360249550888244268532133 25755046790791545800349775)
      ·
        refine ⟨38632570186187318700524663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25755046790791545800349775 38632570186187318700524663)
        ·
          refine ⟨57948855279280978050786995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38632570186187318700524663 57948855279280978050786995)
          ·
            refine ⟨86923282918921467076180493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57948855279280978050786995 86923282918921467076180493)
            ·
              refine ⟨32596231094595550153567685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86923282918921467076180493 32596231094595550153567685)
              ·
                refine ⟨6111793330236665653793941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32596231094595550153567685 6111793330236665653793941)
                ·
                  refine ⟨286490312354843702521591, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6111793330236665653793941 286490312354843702521591)
                  ·
                    rfl

theorem cell23_5021441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 3, 4, 6].length) (baseStart_5021441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021441 prefixEnd_5021441 := by exact prefixLift 5021441
  have htrace : WordTrace (prefixWord ++ tailWord_5021441) baseStart_5021441 baseEnd_5021441 := by
    simpa [prefixWord, tailWord_5021441, baseEnd_5021441] using wordTrace_append hprefix tailTrace_5021441
  have hstable : (prefixWord ++ tailWord_5021441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021441).length < 2 ^ (prefixWord ++ tailWord_5021441).sum := by decide
  have hdescent : baseEnd_5021441 < baseStart_5021441 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021446 : List Nat := [6, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3]
def baseStart_5021446 : Nat := 118140960795 + 5021446 * 2 ^ 59
def prefixEnd_5021446 : Nat := 4983230072969 + 3 ^ 40 * 5021446 * 2
def baseEnd_5021446 : Nat := 2578415378596865803131797

theorem tailTrace_5021446 : CollatzResearch.WordTrace tailWord_5021446 prefixEnd_5021446 2578415378596865803131797 := by
  unfold tailWord_5021446
  simp only [CollatzResearch.WordTrace]
  refine ⟨5723349430192694110790881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 122098121177444141030205461 5723349430192694110790881)
  ·
    refine ⟨4292512072644520583093161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5723349430192694110790881 4292512072644520583093161)
    ·
      refine ⟨3219384054483390437319871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4292512072644520583093161 3219384054483390437319871)
      ·
        refine ⟨4829076081725085655979807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3219384054483390437319871 4829076081725085655979807)
        ·
          refine ⟨7243614122587628483969711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4829076081725085655979807 7243614122587628483969711)
          ·
            refine ⟨10865421183881442725954567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7243614122587628483969711 10865421183881442725954567)
            ·
              refine ⟨16298131775822164088931851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10865421183881442725954567 16298131775822164088931851)
              ·
                refine ⟨24447197663733246133397777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16298131775822164088931851 24447197663733246133397777)
                ·
                  refine ⟨18335398247799934600048333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24447197663733246133397777 18335398247799934600048333)
                  ·
                    refine ⟨6875774342924975475018125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18335398247799934600048333 6875774342924975475018125)
                    ·
                      refine ⟨2578415378596865803131797, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6875774342924975475018125 2578415378596865803131797)
                      ·
                        rfl

theorem cell23_5021446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3].length) (baseStart_5021446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021446 prefixEnd_5021446 := by exact prefixLift 5021446
  have htrace : WordTrace (prefixWord ++ tailWord_5021446) baseStart_5021446 baseEnd_5021446 := by
    simpa [prefixWord, tailWord_5021446, baseEnd_5021446] using wordTrace_append hprefix tailTrace_5021446
  have hstable : (prefixWord ++ tailWord_5021446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021446).length < 2 ^ (prefixWord ++ tailWord_5021446).sum := by decide
  have hdescent : baseEnd_5021446 < baseStart_5021446 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021471 : List Nat := [1, 1, 2, 4, 2, 1, 1, 3, 3, 5]
def baseStart_5021471 : Nat := 118140960795 + 5021471 * 2 ^ 59
def prefixEnd_5021471 : Nat := 4983230072969 + 3 ^ 40 * 5021471 * 2
def baseEnd_5021471 : Nat := 859476071871076068439727

theorem tailTrace_5021471 : CollatzResearch.WordTrace tailWord_5021471 prefixEnd_5021471 859476071871076068439727 := by
  unfold tailWord_5021471
  simp only [CollatzResearch.WordTrace]
  refine ⟨183148093591075640814968267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122098729060717093876645511 183148093591075640814968267)
  ·
    refine ⟨274722140386613461222452401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183148093591075640814968267 274722140386613461222452401)
    ·
      refine ⟨206041605289960095916839301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274722140386613461222452401 206041605289960095916839301)
      ·
        refine ⟨38632800991867517984407369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 206041605289960095916839301 38632800991867517984407369)
        ·
          refine ⟨28974600743900638488305527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38632800991867517984407369 28974600743900638488305527)
          ·
            refine ⟨43461901115850957732458291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28974600743900638488305527 43461901115850957732458291)
            ·
              refine ⟨65192851673776436598687437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43461901115850957732458291 65192851673776436598687437)
              ·
                refine ⟨24447319377666163724507789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65192851673776436598687437 24447319377666163724507789)
                ·
                  refine ⟨9167744766624811396690421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24447319377666163724507789 9167744766624811396690421)
                  ·
                    refine ⟨859476071871076068439727, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9167744766624811396690421 859476071871076068439727)
                    ·
                      rfl

theorem cell23_5021471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 3, 3, 5].length) (baseStart_5021471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021471 prefixEnd_5021471 := by exact prefixLift 5021471
  have htrace : WordTrace (prefixWord ++ tailWord_5021471) baseStart_5021471 baseEnd_5021471 := by
    simpa [prefixWord, tailWord_5021471, baseEnd_5021471] using wordTrace_append hprefix tailTrace_5021471
  have hstable : (prefixWord ++ tailWord_5021471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021471).length < 2 ^ (prefixWord ++ tailWord_5021471).sum := by decide
  have hdescent : baseEnd_5021471 < baseStart_5021471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021502 : List Nat := [4, 2, 1, 2, 2, 2, 2, 1, 3, 1, 3]
def baseStart_5021502 : Nat := 118140960795 + 5021502 * 2 ^ 59
def prefixEnd_5021502 : Nat := 4983230072969 + 3 ^ 40 * 5021502 * 2
def baseEnd_5021502 : Nat := 2578444133513517584031539

theorem tailTrace_5021502 : CollatzResearch.WordTrace tailWord_5021502 prefixEnd_5021502 2578444133513517584031539 := by
  unfold tailWord_5021502
  simp only [CollatzResearch.WordTrace]
  refine ⟨22893653031745416638668345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122099482835975555406231173 22893653031745416638668345)
  ·
    refine ⟨17170239773809062479001259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22893653031745416638668345 17170239773809062479001259)
    ·
      refine ⟨25755359660713593718501889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17170239773809062479001259 25755359660713593718501889)
      ·
        refine ⟨19316519745535195288876417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25755359660713593718501889 19316519745535195288876417)
        ·
          refine ⟨14487389809151396466657313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19316519745535195288876417 14487389809151396466657313)
          ·
            refine ⟨10865542356863547349992985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14487389809151396466657313 10865542356863547349992985)
            ·
              refine ⟨8149156767647660512494739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10865542356863547349992985 8149156767647660512494739)
              ·
                refine ⟨12223735151471490768742109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8149156767647660512494739 12223735151471490768742109)
                ·
                  refine ⟨4583900681801809038278291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12223735151471490768742109 4583900681801809038278291)
                  ·
                    refine ⟨6875851022702713557417437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4583900681801809038278291 6875851022702713557417437)
                    ·
                      refine ⟨2578444133513517584031539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6875851022702713557417437 2578444133513517584031539)
                      ·
                        rfl

theorem cell23_5021502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 1, 3, 1, 3].length) (baseStart_5021502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021502 prefixEnd_5021502 := by exact prefixLift 5021502
  have htrace : WordTrace (prefixWord ++ tailWord_5021502) baseStart_5021502 baseEnd_5021502 := by
    simpa [prefixWord, tailWord_5021502, baseEnd_5021502] using wordTrace_append hprefix tailTrace_5021502
  have hstable : (prefixWord ++ tailWord_5021502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021502).length < 2 ^ (prefixWord ++ tailWord_5021502).sum := by decide
  have hdescent : baseEnd_5021502 < baseStart_5021502 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021511 : List Nat := [1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 5]
def baseStart_5021511 : Nat := 118140960795 + 5021511 * 2 ^ 59
def prefixEnd_5021511 : Nat := 4983230072969 + 3 ^ 40 * 5021511 * 2
def baseEnd_5021511 : Nat := 2578448754839408048818997

theorem tailTrace_5021511 : CollatzResearch.WordTrace tailWord_5021511 prefixEnd_5021511 2578448754839408048818997 := by
  unfold tailWord_5021511
  simp only [CollatzResearch.WordTrace]
  refine ⟨183149552510930727646424387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122099701673953818430949591 183149552510930727646424387)
  ·
    refine ⟨274724328766396091469636581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183149552510930727646424387 274724328766396091469636581)
    ·
      refine ⟨51510811643699267150556859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 274724328766396091469636581 51510811643699267150556859)
      ·
        refine ⟨77266217465548900725835289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51510811643699267150556859 77266217465548900725835289)
        ·
          refine ⟨57949663099161675544376467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77266217465548900725835289 57949663099161675544376467)
          ·
            refine ⟨86924494648742513316564701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57949663099161675544376467 86924494648742513316564701)
            ·
              refine ⟨32596685493278442493711763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86924494648742513316564701 32596685493278442493711763)
              ·
                refine ⟨48895028239917663740567645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32596685493278442493711763 48895028239917663740567645)
                ·
                  refine ⟨18335635589969123902712867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48895028239917663740567645 18335635589969123902712867)
                  ·
                    refine ⟨27503453384953685854069301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18335635589969123902712867 27503453384953685854069301)
                    ·
                      refine ⟨2578448754839408048818997, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27503453384953685854069301 2578448754839408048818997)
                      ·
                        rfl

theorem cell23_5021511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 1, 5].length) (baseStart_5021511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021511 prefixEnd_5021511 := by exact prefixLift 5021511
  have htrace : WordTrace (prefixWord ++ tailWord_5021511) baseStart_5021511 baseEnd_5021511 := by
    simpa [prefixWord, tailWord_5021511, baseEnd_5021511] using wordTrace_append hprefix tailTrace_5021511
  have hstable : (prefixWord ++ tailWord_5021511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021511).length < 2 ^ (prefixWord ++ tailWord_5021511).sum := by decide
  have hdescent : baseEnd_5021511 < baseStart_5021511 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021525 : List Nat := [1, 3, 2, 2, 2, 3, 2, 2, 1, 1, 4]
def baseStart_5021525 : Nat := 118140960795 + 5021525 * 2 ^ 59
def prefixEnd_5021525 : Nat := 4983230072969 + 3 ^ 40 * 5021525 * 2
def baseEnd_5021525 : Nat := 2578455943568570994043933

theorem tailTrace_5021525 : CollatzResearch.WordTrace tailWord_5021525 prefixEnd_5021525 2578455943568570994043933 := by
  unfold tailWord_5021525
  simp only [CollatzResearch.WordTrace]
  refine ⟨183150063132880008037434029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122100042088586672024956019 183150063132880008037434029)
  ·
    refine ⟨68681273674830003014037761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183150063132880008037434029 68681273674830003014037761)
    ·
      refine ⟨51510955256122502260528321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68681273674830003014037761 51510955256122502260528321)
      ·
        refine ⟨38633216442091876695396241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51510955256122502260528321 38633216442091876695396241)
        ·
          refine ⟨28974912331568907521547181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38633216442091876695396241 28974912331568907521547181)
          ·
            refine ⟨10865592124338340320580193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28974912331568907521547181 10865592124338340320580193)
            ·
              refine ⟨8149194093253755240435145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10865592124338340320580193 8149194093253755240435145)
              ·
                refine ⟨6111895569940316430326359, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8149194093253755240435145 6111895569940316430326359)
                ·
                  refine ⟨9167843354910474645489539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6111895569940316430326359 9167843354910474645489539)
                  ·
                    refine ⟨13751765032365711968234309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9167843354910474645489539 13751765032365711968234309)
                    ·
                      refine ⟨2578455943568570994043933, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13751765032365711968234309 2578455943568570994043933)
                      ·
                        rfl

theorem cell23_5021525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_5021525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021525 prefixEnd_5021525 := by exact prefixLift 5021525
  have htrace : WordTrace (prefixWord ++ tailWord_5021525) baseStart_5021525 baseEnd_5021525 := by
    simpa [prefixWord, tailWord_5021525, baseEnd_5021525] using wordTrace_append hprefix tailTrace_5021525
  have hstable : (prefixWord ++ tailWord_5021525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021525).length < 2 ^ (prefixWord ++ tailWord_5021525).sum := by decide
  have hdescent : baseEnd_5021525 < baseStart_5021525 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021561 : List Nat := [1, 2, 1, 3, 2, 2, 2, 1, 2, 7]
def baseStart_5021561 : Nat := 118140960795 + 5021561 * 2 ^ 59
def prefixEnd_5021561 : Nat := 4983230072969 + 3 ^ 40 * 5021561 * 2
def baseEnd_5021561 : Nat := 859491476290710951064589

theorem tailTrace_5021561 : CollatzResearch.WordTrace tailWord_5021561 prefixEnd_5021561 859491476290710951064589 := by
  unfold tailWord_5021561
  simp only [CollatzResearch.WordTrace]
  refine ⟨183151376160749586185744537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122100917440499724123829691 183151376160749586185744537)
  ·
    refine ⟨137363532120562189639308403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183151376160749586185744537 137363532120562189639308403)
    ·
      refine ⟨206045298180843284458962605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137363532120562189639308403 206045298180843284458962605)
      ·
        refine ⟨77266986817816231672110977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206045298180843284458962605 77266986817816231672110977)
        ·
          refine ⟨57950240113362173754083233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77266986817816231672110977 57950240113362173754083233)
          ·
            refine ⟨43462680085021630315562425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57950240113362173754083233 43462680085021630315562425)
            ·
              refine ⟨32597010063766222736671819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43462680085021630315562425 32597010063766222736671819)
              ·
                refine ⟨48895515095649334105007729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32597010063766222736671819 48895515095649334105007729)
                ·
                  refine ⟨36671636321737000578755797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48895515095649334105007729 36671636321737000578755797)
                  ·
                    refine ⟨859491476290710951064589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36671636321737000578755797 859491476290710951064589)
                    ·
                      rfl

theorem cell23_5021561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 2, 1, 2, 7].length) (baseStart_5021561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021561 prefixEnd_5021561 := by exact prefixLift 5021561
  have htrace : WordTrace (prefixWord ++ tailWord_5021561) baseStart_5021561 baseEnd_5021561 := by
    simpa [prefixWord, tailWord_5021561, baseEnd_5021561] using wordTrace_append hprefix tailTrace_5021561
  have hstable : (prefixWord ++ tailWord_5021561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021561).length < 2 ^ (prefixWord ++ tailWord_5021561).sum := by decide
  have hdescent : baseEnd_5021561 < baseStart_5021561 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021592 : List Nat := [2, 1, 2, 6, 1, 1, 1, 2, 1, 3, 3]
def baseStart_5021592 : Nat := 118140960795 + 5021592 * 2 ^ 59
def prefixEnd_5021592 : Nat := 4983230072969 + 3 ^ 40 * 5021592 * 2
def baseEnd_5021592 : Nat := 2578490346772422231906125

theorem tailTrace_5021592 : CollatzResearch.WordTrace tailWord_5021592 prefixEnd_5021592 2578490346772422231906125 := by
  unfold tailWord_5021592
  simp only [CollatzResearch.WordTrace]
  refine ⟨91576253411818639240061515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122101671215758185653415353 91576253411818639240061515)
  ·
    refine ⟨137364380117727958860092273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91576253411818639240061515 137364380117727958860092273)
    ·
      refine ⟨103023285088295969145069205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137364380117727958860092273 103023285088295969145069205)
      ·
        refine ⟨4829216488513873553675119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 103023285088295969145069205 4829216488513873553675119)
        ·
          refine ⟨7243824732770810330512679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4829216488513873553675119 7243824732770810330512679)
          ·
            refine ⟨10865737099156215495769019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7243824732770810330512679 10865737099156215495769019)
            ·
              refine ⟨16298605648734323243653529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10865737099156215495769019 16298605648734323243653529)
              ·
                refine ⟨12223954236550742432740147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16298605648734323243653529 12223954236550742432740147)
                ·
                  refine ⟨18335931354826113649110221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12223954236550742432740147 18335931354826113649110221)
                  ·
                    refine ⟨6875974258059792618416333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18335931354826113649110221 6875974258059792618416333)
                    ·
                      refine ⟨2578490346772422231906125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6875974258059792618416333 2578490346772422231906125)
                      ·
                        rfl

theorem cell23_5021592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 2, 1, 3, 3].length) (baseStart_5021592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021592 prefixEnd_5021592 := by exact prefixLift 5021592
  have htrace : WordTrace (prefixWord ++ tailWord_5021592) baseStart_5021592 baseEnd_5021592 := by
    simpa [prefixWord, tailWord_5021592, baseEnd_5021592] using wordTrace_append hprefix tailTrace_5021592
  have hstable : (prefixWord ++ tailWord_5021592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021592).length < 2 ^ (prefixWord ++ tailWord_5021592).sum := by decide
  have hdescent : baseEnd_5021592 < baseStart_5021592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021632 : List Nat := [2, 1, 1, 2, 3, 2, 1, 5, 2, 2, 2]
def baseStart_5021632 : Nat := 118140960795 + 5021632 * 2 ^ 59
def prefixEnd_5021632 : Nat := 4983230072969 + 3 ^ 40 * 5021632 * 2
def baseEnd_5021632 : Nat := 2578510885998602075405941

theorem tailTrace_5021632 : CollatzResearch.WordTrace tailWord_5021632 prefixEnd_5021632 2578510885998602075405941 := by
  unfold tailWord_5021632
  simp only [CollatzResearch.WordTrace]
  refine ⟨91576982871746182655789575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122102643828994910207719433 91576982871746182655789575)
  ·
    refine ⟨137365474307619273983684363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91576982871746182655789575 137365474307619273983684363)
    ·
      refine ⟨206048211461428910975526545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137365474307619273983684363 206048211461428910975526545)
      ·
        refine ⟨154536158596071683231644909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206048211461428910975526545 154536158596071683231644909)
        ·
          refine ⟨57951059473526881211866841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154536158596071683231644909 57951059473526881211866841)
          ·
            refine ⟨43463294605145160908900131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57951059473526881211866841 43463294605145160908900131)
            ·
              refine ⟨65194941907717741363350197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43463294605145160908900131 65194941907717741363350197)
              ·
                refine ⟨6112025803848538252814081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 65194941907717741363350197 6112025803848538252814081)
                ·
                  refine ⟨4584019352886403689610561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6112025803848538252814081 4584019352886403689610561)
                  ·
                    refine ⟨3438014514664802767207921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4584019352886403689610561 3438014514664802767207921)
                    ·
                      refine ⟨2578510885998602075405941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3438014514664802767207921 2578510885998602075405941)
                      ·
                        rfl

theorem cell23_5021632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 5, 2, 2, 2].length) (baseStart_5021632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021632 prefixEnd_5021632 := by exact prefixLift 5021632
  have htrace : WordTrace (prefixWord ++ tailWord_5021632) baseStart_5021632 baseEnd_5021632 := by
    simpa [prefixWord, tailWord_5021632, baseEnd_5021632] using wordTrace_append hprefix tailTrace_5021632
  have hstable : (prefixWord ++ tailWord_5021632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021632).length < 2 ^ (prefixWord ++ tailWord_5021632).sum := by decide
  have hdescent : baseEnd_5021632 < baseStart_5021632 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021641 : List Nat := [1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 8]
def baseStart_5021641 : Nat := 118140960795 + 5021641 * 2 ^ 59
def prefixEnd_5021641 : Nat := 4983230072969 + 3 ^ 40 * 5021641 * 2
def baseEnd_5021641 : Nat := 2578515507324492540193399

theorem tailTrace_5021641 : CollatzResearch.WordTrace tailWord_5021641 prefixEnd_5021641 2578515507324492540193399 := by
  unfold tailWord_5021641
  simp only [CollatzResearch.WordTrace]
  refine ⟨183154294000459759848656777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122102862666973173232437851 183154294000459759848656777)
  ·
    refine ⟨137365720500344819886492583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183154294000459759848656777 137365720500344819886492583)
    ·
      refine ⟨206048580750517229829738875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137365720500344819886492583 206048580750517229829738875)
      ·
        refine ⟨309072871125775844744608313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206048580750517229829738875 309072871125775844744608313)
        ·
          refine ⟨231804653344331883558456235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309072871125775844744608313 231804653344331883558456235)
          ·
            refine ⟨347706980016497825337684353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231804653344331883558456235 347706980016497825337684353)
            ·
              refine ⟨260780235012373369003263265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 347706980016497825337684353 260780235012373369003263265)
              ·
                refine ⟨195585176259280026752447449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 260780235012373369003263265 195585176259280026752447449)
                ·
                  refine ⟨146688882194460020064335587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195585176259280026752447449 146688882194460020064335587)
                  ·
                    refine ⟨220033323291690030096503381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 146688882194460020064335587 220033323291690030096503381)
                    ·
                      refine ⟨2578515507324492540193399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 220033323291690030096503381 2578515507324492540193399)
                      ·
                        rfl

theorem cell23_5021641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 2, 2, 1, 8].length) (baseStart_5021641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021641 prefixEnd_5021641 := by exact prefixLift 5021641
  have htrace : WordTrace (prefixWord ++ tailWord_5021641) baseStart_5021641 baseEnd_5021641 := by
    simpa [prefixWord, tailWord_5021641, baseEnd_5021641] using wordTrace_append hprefix tailTrace_5021641
  have hstable : (prefixWord ++ tailWord_5021641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021641).length < 2 ^ (prefixWord ++ tailWord_5021641).sum := by decide
  have hdescent : baseEnd_5021641 < baseStart_5021641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021655 : List Nat := [1, 1, 3, 2, 1, 1, 6, 3, 5]
def baseStart_5021655 : Nat := 118140960795 + 5021655 * 2 ^ 59
def prefixEnd_5021655 : Nat := 4983230072969 + 3 ^ 40 * 5021655 * 2
def baseEnd_5021655 : Nat := 286502521783739498379815

theorem tailTrace_5021655 : CollatzResearch.WordTrace tailWord_5021655 prefixEnd_5021655 286502521783739498379815 := by
  unfold tailWord_5021655
  simp only [CollatzResearch.WordTrace]
  refine ⟨183154804622409040239666419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122103203081606026826444279 183154804622409040239666419)
  ·
    refine ⟨274732206933613560359499629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183154804622409040239666419 274732206933613560359499629)
    ·
      refine ⟨103024577600105085134812361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 274732206933613560359499629 103024577600105085134812361)
      ·
        refine ⟨77268433200078813851109271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103024577600105085134812361 77268433200078813851109271)
        ·
          refine ⟨115902649800118220776663907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77268433200078813851109271 115902649800118220776663907)
          ·
            refine ⟨173853974700177331164995861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115902649800118220776663907 173853974700177331164995861)
            ·
              refine ⟨8149405064070812398359181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 173853974700177331164995861 8149405064070812398359181)
              ·
                refine ⟨3056026899026554649384693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8149405064070812398359181 3056026899026554649384693)
                ·
                  refine ⟨286502521783739498379815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3056026899026554649384693 286502521783739498379815)
                  ·
                    rfl

theorem cell23_5021655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 6, 3, 5].length) (baseStart_5021655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021655 prefixEnd_5021655 := by exact prefixLift 5021655
  have htrace : WordTrace (prefixWord ++ tailWord_5021655) baseStart_5021655 baseEnd_5021655 := by
    simpa [prefixWord, tailWord_5021655, baseEnd_5021655] using wordTrace_append hprefix tailTrace_5021655
  have hstable : (prefixWord ++ tailWord_5021655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021655).length < 2 ^ (prefixWord ++ tailWord_5021655).sum := by decide
  have hdescent : baseEnd_5021655 < baseStart_5021655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021660 : List Nat := [2, 2, 6, 1, 2, 1, 1, 2, 2, 1, 3]
def baseStart_5021660 : Nat := 118140960795 + 5021660 * 2 ^ 59
def prefixEnd_5021660 : Nat := 4983230072969 + 3 ^ 40 * 5021660 * 2
def baseEnd_5021660 : Nat := 2578525263456927965855813

theorem tailTrace_5021660 : CollatzResearch.WordTrace tailWord_5021660 prefixEnd_5021660 2578525263456927965855813 := by
  unfold tailWord_5021660
  simp only [CollatzResearch.WordTrace]
  refine ⟨91577493493695463046799217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122103324658260617395732289 91577493493695463046799217)
  ·
    refine ⟨68683120120271597285099413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91577493493695463046799217 68683120120271597285099413)
    ·
      refine ⟨3219521255637731122739035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68683120120271597285099413 3219521255637731122739035)
      ·
        refine ⟨4829281883456596684108553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3219521255637731122739035 4829281883456596684108553)
        ·
          refine ⟨3621961412592447513081415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4829281883456596684108553 3621961412592447513081415)
          ·
            refine ⟨5432942118888671269622123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3621961412592447513081415 5432942118888671269622123)
            ·
              refine ⟨8149413178333006904433185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5432942118888671269622123 8149413178333006904433185)
              ·
                refine ⟨6112059883749755178324889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8149413178333006904433185 6112059883749755178324889)
                ·
                  refine ⟨4584044912812316383743667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6112059883749755178324889 4584044912812316383743667)
                  ·
                    refine ⟨6876067369218474575615501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4584044912812316383743667 6876067369218474575615501)
                    ·
                      refine ⟨2578525263456927965855813, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6876067369218474575615501 2578525263456927965855813)
                      ·
                        rfl

theorem cell23_5021660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_5021660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021660 prefixEnd_5021660 := by exact prefixLift 5021660
  have htrace : WordTrace (prefixWord ++ tailWord_5021660) baseStart_5021660 baseEnd_5021660 := by
    simpa [prefixWord, tailWord_5021660, baseEnd_5021660] using wordTrace_append hprefix tailTrace_5021660
  have hstable : (prefixWord ++ tailWord_5021660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021660).length < 2 ^ (prefixWord ++ tailWord_5021660).sum := by decide
  have hdescent : baseEnd_5021660 < baseStart_5021660 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021666 : List Nat := [3, 3, 3, 1, 2, 1, 1, 1, 4, 2, 2]
def baseStart_5021666 : Nat := 118140960795 + 5021666 * 2 ^ 59
def prefixEnd_5021666 : Nat := 4983230072969 + 3 ^ 40 * 5021666 * 2
def baseEnd_5021666 : Nat := 2578528344340854942380785

theorem tailTrace_5021666 : CollatzResearch.WordTrace tailWord_5021666 prefixEnd_5021666 2578528344340854942380785 := by
  unfold tailWord_5021666
  simp only [CollatzResearch.WordTrace]
  refine ⟨45788801456342297279579213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122103470550246126078877901 45788801456342297279579213)
  ·
    refine ⟨17170800546128361479842205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45788801456342297279579213 17170800546128361479842205)
    ·
      refine ⟨6439050204798135554940827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17170800546128361479842205 6439050204798135554940827)
      ·
        refine ⟨9658575307197203332411241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6439050204798135554940827 9658575307197203332411241)
        ·
          refine ⟨7243931480397902499308431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9658575307197203332411241 7243931480397902499308431)
          ·
            refine ⟨10865897220596853748962647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7243931480397902499308431 10865897220596853748962647)
            ·
              refine ⟨16298845830895280623443971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10865897220596853748962647 16298845830895280623443971)
              ·
                refine ⟨24448268746342920935165957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16298845830895280623443971 24448268746342920935165957)
                ·
                  refine ⟨4584050389939297675343617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24448268746342920935165957 4584050389939297675343617)
                  ·
                    refine ⟨3438037792454473256507713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4584050389939297675343617 3438037792454473256507713)
                    ·
                      refine ⟨2578528344340854942380785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3438037792454473256507713 2578528344340854942380785)
                      ·
                        rfl

theorem cell23_5021666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 1, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_5021666 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021666 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021666 prefixEnd_5021666 := by exact prefixLift 5021666
  have htrace : WordTrace (prefixWord ++ tailWord_5021666) baseStart_5021666 baseEnd_5021666 := by
    simpa [prefixWord, tailWord_5021666, baseEnd_5021666] using wordTrace_append hprefix tailTrace_5021666
  have hstable : (prefixWord ++ tailWord_5021666).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021666).length < 2 ^ (prefixWord ++ tailWord_5021666).sum := by decide
  have hdescent : baseEnd_5021666 < baseStart_5021666 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021668 : List Nat := [2, 3, 1, 1, 1, 1, 4, 1, 4, 5]
def baseStart_5021668 : Nat := 118140960795 + 5021668 * 2 ^ 59
def prefixEnd_5021668 : Nat := 4983230072969 + 3 ^ 40 * 5021668 * 2
def baseEnd_5021668 : Nat := 859509790434054644851925

theorem tailTrace_5021668 : CollatzResearch.WordTrace tailWord_5021668 prefixEnd_5021668 859509790434054644851925 := by
  unfold tailWord_5021668
  simp only [CollatzResearch.WordTrace]
  refine ⟨91577639385680971729944829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122103519180907962306593105 91577639385680971729944829)
  ·
    refine ⟨34341614769630364398729311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91577639385680971729944829 34341614769630364398729311)
    ·
      refine ⟨51512422154445546598093967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34341614769630364398729311 51512422154445546598093967)
      ·
        refine ⟨77268633231668319897140951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51512422154445546598093967 77268633231668319897140951)
        ·
          refine ⟨115902949847502479845711427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77268633231668319897140951 115902949847502479845711427)
          ·
            refine ⟨173854424771253719768567141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115902949847502479845711427 173854424771253719768567141)
            ·
              refine ⟨32597704644610072456606339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 173854424771253719768567141 32597704644610072456606339)
              ·
                refine ⟨48896556966915108684909509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32597704644610072456606339 48896556966915108684909509)
                ·
                  refine ⟨9168104431296582878420533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48896556966915108684909509 9168104431296582878420533)
                  ·
                    refine ⟨859509790434054644851925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9168104431296582878420533 859509790434054644851925)
                    ·
                      rfl

theorem cell23_5021668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 4, 1, 4, 5].length) (baseStart_5021668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021668 prefixEnd_5021668 := by exact prefixLift 5021668
  have htrace : WordTrace (prefixWord ++ tailWord_5021668) baseStart_5021668 baseEnd_5021668 := by
    simpa [prefixWord, tailWord_5021668, baseEnd_5021668] using wordTrace_append hprefix tailTrace_5021668
  have hstable : (prefixWord ++ tailWord_5021668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021668).length < 2 ^ (prefixWord ++ tailWord_5021668).sum := by decide
  have hdescent : baseEnd_5021668 < baseStart_5021668 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021688 : List Nat := [2, 1, 2, 1, 1, 3, 3, 2, 1, 3, 4]
def baseStart_5021688 : Nat := 118140960795 + 5021688 * 2 ^ 59
def prefixEnd_5021688 : Nat := 4983230072969 + 3 ^ 40 * 5021688 * 2
def baseEnd_5021688 : Nat := 2578539640915253856305683

theorem tailTrace_5021688 : CollatzResearch.WordTrace tailWord_5021688 prefixEnd_5021688 2578539640915253856305683 := by
  unfold tailWord_5021688
  simp only [CollatzResearch.WordTrace]
  refine ⟨91578004115644743437808859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122104005487526324583745145 91578004115644743437808859)
  ·
    refine ⟨137367006173467115156713289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91578004115644743437808859 137367006173467115156713289)
    ·
      refine ⟨103025254630100336367534967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137367006173467115156713289 103025254630100336367534967)
      ·
        refine ⟨154537881945150504551302451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103025254630100336367534967 154537881945150504551302451)
        ·
          refine ⟨231806822917725756826953677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154537881945150504551302451 231806822917725756826953677)
          ·
            refine ⟨86927558594147158810107629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 231806822917725756826953677 86927558594147158810107629)
            ·
              refine ⟨32597834472805184553790361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86927558594147158810107629 32597834472805184553790361)
              ·
                refine ⟨24448375854603888415342771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32597834472805184553790361 24448375854603888415342771)
                ·
                  refine ⟨36672563781905832623014157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24448375854603888415342771 36672563781905832623014157)
                  ·
                    refine ⟨13752211418214687233630309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36672563781905832623014157 13752211418214687233630309)
                    ·
                      refine ⟨2578539640915253856305683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13752211418214687233630309 2578539640915253856305683)
                      ·
                        rfl

theorem cell23_5021688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 1, 3, 4].length) (baseStart_5021688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021688 prefixEnd_5021688 := by exact prefixLift 5021688
  have htrace : WordTrace (prefixWord ++ tailWord_5021688) baseStart_5021688 baseEnd_5021688 := by
    simpa [prefixWord, tailWord_5021688, baseEnd_5021688] using wordTrace_append hprefix tailTrace_5021688
  have hstable : (prefixWord ++ tailWord_5021688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021688).length < 2 ^ (prefixWord ++ tailWord_5021688).sum := by decide
  have hdescent : baseEnd_5021688 < baseStart_5021688 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021745 : List Nat := [1, 2, 2, 3, 1, 4, 1, 3, 6]
def baseStart_5021745 : Nat := 118140960795 + 5021745 * 2 ^ 59
def prefixEnd_5021745 : Nat := 4983230072969 + 3 ^ 40 * 5021745 * 2
def baseEnd_5021745 : Nat := 286507656590284459254769

theorem tailTrace_5021745 : CollatzResearch.WordTrace tailWord_5021745 prefixEnd_5021745 286507656590284459254769 := by
  unfold tailWord_5021745
  simp only [CollatzResearch.WordTrace]
  refine ⟨183158087192082985610442689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122105391461388657073628459 183158087192082985610442689)
  ·
    refine ⟨137368565394062239207832017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183158087192082985610442689 137368565394062239207832017)
    ·
      refine ⟨103026424045546679405874013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137368565394062239207832017 103026424045546679405874013)
      ·
        refine ⟨38634909017080004777202755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103026424045546679405874013 38634909017080004777202755)
        ·
          refine ⟨57952363525620007165804133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38634909017080004777202755 57952363525620007165804133)
          ·
            refine ⟨10866068161053751343588275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57952363525620007165804133 10866068161053751343588275)
            ·
              refine ⟨16299102241580627015382413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10866068161053751343588275 16299102241580627015382413)
              ·
                refine ⟨6112163340592735130768405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16299102241580627015382413 6112163340592735130768405)
                ·
                  refine ⟨286507656590284459254769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6112163340592735130768405 286507656590284459254769)
                  ·
                    rfl

theorem cell23_5021745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 4, 1, 3, 6].length) (baseStart_5021745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021745 prefixEnd_5021745 := by exact prefixLift 5021745
  have htrace : WordTrace (prefixWord ++ tailWord_5021745) baseStart_5021745 baseEnd_5021745 := by
    simpa [prefixWord, tailWord_5021745, baseEnd_5021745] using wordTrace_append hprefix tailTrace_5021745
  have hstable : (prefixWord ++ tailWord_5021745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021745).length < 2 ^ (prefixWord ++ tailWord_5021745).sum := by decide
  have hdescent : baseEnd_5021745 < baseStart_5021745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021766 : List Nat := [6, 1, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_5021766 : Nat := 118140960795 + 5021766 * 2 ^ 59
def prefixEnd_5021766 : Nat := 4983230072969 + 3 ^ 40 * 5021766 * 2
def baseEnd_5021766 : Nat := 859526564135434850376775

theorem tailTrace_5021766 : CollatzResearch.WordTrace tailWord_5021766 prefixEnd_5021766 859526564135434850376775 := by
  unfold tailWord_5021766
  simp only [CollatzResearch.WordTrace]
  refine ⟨5723714160156465818654911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 122105902083337937464638101 5723714160156465818654911)
  ·
    refine ⟨8585571240234698727982367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5723714160156465818654911 8585571240234698727982367)
    ·
      refine ⟨12878356860352048091973551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8585571240234698727982367 12878356860352048091973551)
      ·
        refine ⟨19317535290528072137960327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12878356860352048091973551 19317535290528072137960327)
        ·
          refine ⟨28976302935792108206940491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19317535290528072137960327 28976302935792108206940491)
          ·
            refine ⟨43464454403688162310410737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28976302935792108206940491 43464454403688162310410737)
            ·
              refine ⟨32598340802766121732808053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43464454403688162310410737 32598340802766121732808053)
              ·
                refine ⟨3056094450259323912450755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32598340802766121732808053 3056094450259323912450755)
                ·
                  refine ⟨4584141675388985868676133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3056094450259323912450755 4584141675388985868676133)
                  ·
                    refine ⟨859526564135434850376775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4584141675388985868676133 859526564135434850376775)
                    ·
                      rfl

theorem cell23_5021766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_5021766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021766 prefixEnd_5021766 := by exact prefixLift 5021766
  have htrace : WordTrace (prefixWord ++ tailWord_5021766) baseStart_5021766 baseEnd_5021766 := by
    simpa [prefixWord, tailWord_5021766, baseEnd_5021766] using wordTrace_append hprefix tailTrace_5021766
  have hstable : (prefixWord ++ tailWord_5021766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021766).length < 2 ^ (prefixWord ++ tailWord_5021766).sum := by decide
  have hdescent : baseEnd_5021766 < baseStart_5021766 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021768 : List Nat := [2, 1, 3, 1, 1, 1, 2, 1, 2, 4, 5]
def baseStart_5021768 : Nat := 118140960795 + 5021768 * 2 ^ 59
def prefixEnd_5021768 : Nat := 4983230072969 + 3 ^ 40 * 5021768 * 2
def baseEnd_5021768 : Nat := 2578580719367613543305315

theorem tailTrace_5021768 : CollatzResearch.WordTrace tailWord_5021768 prefixEnd_5021768 2578580719367613543305315 := by
  unfold tailWord_5021768
  simp only [CollatzResearch.WordTrace]
  refine ⟨91579463035499830269264979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122105950713999773692353305 91579463035499830269264979)
  ·
    refine ⟨137369194553249745403897469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91579463035499830269264979 137369194553249745403897469)
    ·
      refine ⟨51513447957468654526461551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137369194553249745403897469 51513447957468654526461551)
      ·
        refine ⟨77270171936202981789692327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51513447957468654526461551 77270171936202981789692327)
        ·
          refine ⟨115905257904304472684538491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77270171936202981789692327 115905257904304472684538491)
          ·
            refine ⟨173857886856456709026807737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115905257904304472684538491 173857886856456709026807737)
            ·
              refine ⟨130393415142342531770105803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173857886856456709026807737 130393415142342531770105803)
              ·
                refine ⟨195590122713513797655158705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130393415142342531770105803 195590122713513797655158705)
                ·
                  refine ⟨146692592035135348241369029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195590122713513797655158705 146692592035135348241369029)
                  ·
                    refine ⟨27504861006587877795256693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 146692592035135348241369029 27504861006587877795256693)
                    ·
                      refine ⟨2578580719367613543305315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27504861006587877795256693 2578580719367613543305315)
                      ·
                        rfl

theorem cell23_5021768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 2, 4, 5].length) (baseStart_5021768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021768 prefixEnd_5021768 := by exact prefixLift 5021768
  have htrace : WordTrace (prefixWord ++ tailWord_5021768) baseStart_5021768 baseEnd_5021768 := by
    simpa [prefixWord, tailWord_5021768, baseEnd_5021768] using wordTrace_append hprefix tailTrace_5021768
  have hstable : (prefixWord ++ tailWord_5021768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021768).length < 2 ^ (prefixWord ++ tailWord_5021768).sum := by decide
  have hdescent : baseEnd_5021768 < baseStart_5021768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021795 : List Nat := [1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 4]
def baseStart_5021795 : Nat := 118140960795 + 5021795 * 2 ^ 59
def prefixEnd_5021795 : Nat := 4983230072969 + 3 ^ 40 * 5021795 * 2
def baseEnd_5021795 : Nat := 2578594583345284937667691

theorem tailTrace_5021795 : CollatzResearch.WordTrace tailWord_5021795 prefixEnd_5021795 2578594583345284937667691 := by
  unfold tailWord_5021795
  simp only [CollatzResearch.WordTrace]
  refine ⟨183159910841901844149762839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122106607227934562766508559 183159910841901844149762839)
  ·
    refine ⟨274739866262852766224644259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183159910841901844149762839 274739866262852766224644259)
    ·
      refine ⟨412109799394279149336966389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274739866262852766224644259 412109799394279149336966389)
      ·
        refine ⟨38635293693213670250340599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 412109799394279149336966389 38635293693213670250340599)
        ·
          refine ⟨57952940539820505375510899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38635293693213670250340599 57952940539820505375510899)
          ·
            refine ⟨86929410809730758063266349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57952940539820505375510899 86929410809730758063266349)
            ·
              refine ⟨32598529053649034273724881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86929410809730758063266349 32598529053649034273724881)
              ·
                refine ⟨24448896790236775705293661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32598529053649034273724881 24448896790236775705293661)
                ·
                  refine ⟨9168336296338790889485123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24448896790236775705293661 9168336296338790889485123)
                  ·
                    refine ⟨13752504444508186334227685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9168336296338790889485123 13752504444508186334227685)
                    ·
                      refine ⟨2578594583345284937667691, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13752504444508186334227685 2578594583345284937667691)
                      ·
                        rfl

theorem cell23_5021795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 3, 2, 3, 1, 4].length) (baseStart_5021795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021795 prefixEnd_5021795 := by exact prefixLift 5021795
  have htrace : WordTrace (prefixWord ++ tailWord_5021795) baseStart_5021795 baseEnd_5021795 := by
    simpa [prefixWord, tailWord_5021795, baseEnd_5021795] using wordTrace_append hprefix tailTrace_5021795
  have hstable : (prefixWord ++ tailWord_5021795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021795).length < 2 ^ (prefixWord ++ tailWord_5021795).sum := by decide
  have hdescent : baseEnd_5021795 < baseStart_5021795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021829 : List Nat := [1, 3, 1, 1, 5, 1, 4, 1, 1, 1, 4]
def baseStart_5021829 : Nat := 118140960795 + 5021829 * 2 ^ 59
def prefixEnd_5021829 : Nat := 4983230072969 + 3 ^ 40 * 5021829 * 2
def baseEnd_5021829 : Nat := 2578612041687537804642535

theorem tailTrace_5021829 : CollatzResearch.WordTrace tailWord_5021829 prefixEnd_5021829 2578612041687537804642535 := by
  unfold tailWord_5021829
  simp only [CollatzResearch.WordTrace]
  refine ⟨183161150923778667956500541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122107433949185778637667027 183161150923778667956500541)
  ·
    refine ⟨68685431596417000483687703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183161150923778667956500541 68685431596417000483687703)
    ·
      refine ⟨103028147394625500725531555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68685431596417000483687703 103028147394625500725531555)
      ·
        refine ⟨154542221091938251088297333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103028147394625500725531555 154542221091938251088297333)
        ·
          refine ⟨14488333227369211039527875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 154542221091938251088297333 14488333227369211039527875)
          ·
            refine ⟨21732499841053816559291813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14488333227369211039527875 21732499841053816559291813)
            ·
              refine ⟨4074843720197590604867215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21732499841053816559291813 4074843720197590604867215)
              ·
                refine ⟨6112265580296385907300823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4074843720197590604867215 6112265580296385907300823)
                ·
                  refine ⟨9168398370444578860951235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6112265580296385907300823 9168398370444578860951235)
                  ·
                    refine ⟨13752597555666868291426853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9168398370444578860951235 13752597555666868291426853)
                    ·
                      refine ⟨2578612041687537804642535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13752597555666868291426853 2578612041687537804642535)
                      ·
                        rfl

theorem cell23_5021829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 1, 4, 1, 1, 1, 4].length) (baseStart_5021829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021829 prefixEnd_5021829 := by exact prefixLift 5021829
  have htrace : WordTrace (prefixWord ++ tailWord_5021829) baseStart_5021829 baseEnd_5021829 := by
    simpa [prefixWord, tailWord_5021829, baseEnd_5021829] using wordTrace_append hprefix tailTrace_5021829
  have hstable : (prefixWord ++ tailWord_5021829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021829).length < 2 ^ (prefixWord ++ tailWord_5021829).sum := by decide
  have hdescent : baseEnd_5021829 < baseStart_5021829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021869 : List Nat := [1, 5, 2, 1, 2, 3, 2, 7]
def baseStart_5021869 : Nat := 118140960795 + 5021869 * 2 ^ 59
def prefixEnd_5021869 : Nat := 4983230072969 + 3 ^ 40 * 5021869 * 2
def baseEnd_5021869 : Nat := 95504910404211764746013

theorem tailTrace_5021869 : CollatzResearch.WordTrace tailWord_5021869 prefixEnd_5021869 95504910404211764746013 := by
  unfold tailWord_5021869
  simp only [CollatzResearch.WordTrace]
  refine ⟨183162609843633754787956661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122108406562422503191971107 183162609843633754787956661)
  ·
    refine ⟨17171494672840664511370937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 183162609843633754787956661 17171494672840664511370937)
    ·
      refine ⟨12878621004630498383528203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17171494672840664511370937 12878621004630498383528203)
      ·
        refine ⟨19317931506945747575292305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12878621004630498383528203 19317931506945747575292305)
        ·
          refine ⟨14488448630209310681469229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19317931506945747575292305 14488448630209310681469229)
          ·
            refine ⟨5433168236328491505550961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14488448630209310681469229 5433168236328491505550961)
            ·
              refine ⟨4074876177246368629163221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5433168236328491505550961 4074876177246368629163221)
              ·
                refine ⟨95504910404211764746013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4074876177246368629163221 95504910404211764746013)
                ·
                  rfl

theorem cell23_5021869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 2, 7].length) (baseStart_5021869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021869 prefixEnd_5021869 := by exact prefixLift 5021869
  have htrace : WordTrace (prefixWord ++ tailWord_5021869) baseStart_5021869 baseEnd_5021869 := by
    simpa [prefixWord, tailWord_5021869, baseEnd_5021869] using wordTrace_append hprefix tailTrace_5021869
  have hstable : (prefixWord ++ tailWord_5021869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021869).length < 2 ^ (prefixWord ++ tailWord_5021869).sum := by decide
  have hdescent : baseEnd_5021869 < baseStart_5021869 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5021885 : List Nat := [1, 4, 1, 2, 1, 1, 1, 2, 1, 5, 4]
def baseStart_5021885 : Nat := 118140960795 + 5021885 * 2 ^ 59
def prefixEnd_5021885 : Nat := 4983230072969 + 3 ^ 40 * 5021885 * 2
def baseEnd_5021885 : Nat := 2578640796604189585542277

theorem tailTrace_5021885 : CollatzResearch.WordTrace tailWord_5021885 prefixEnd_5021885 2578640796604189585542277 := by
  unfold tailWord_5021885
  simp only [CollatzResearch.WordTrace]
  refine ⟨183163193411575789520539109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122108795607717193013692739 183163193411575789520539109)
  ·
    refine ⟨34343098764670460535101083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183163193411575789520539109 34343098764670460535101083)
    ·
      refine ⟨51514648147005690802651625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34343098764670460535101083 51514648147005690802651625)
      ·
        refine ⟨38635986110254268101988719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51514648147005690802651625 38635986110254268101988719)
        ·
          refine ⟨57953979165381402152983079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38635986110254268101988719 57953979165381402152983079)
          ·
            refine ⟨86930968748072103229474619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57953979165381402152983079 86930968748072103229474619)
            ·
              refine ⟨130396453122108154844211929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86930968748072103229474619 130396453122108154844211929)
              ·
                refine ⟨97797339841581116133158947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130396453122108154844211929 97797339841581116133158947)
                ·
                  refine ⟨146696009762371674199738421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97797339841581116133158947 146696009762371674199738421)
                  ·
                    refine ⟨13752750915222344456225477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 146696009762371674199738421 13752750915222344456225477)
                    ·
                      refine ⟨2578640796604189585542277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13752750915222344456225477 2578640796604189585542277)
                      ·
                        rfl

theorem cell23_5021885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_5021885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5021885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5021885 prefixEnd_5021885 := by exact prefixLift 5021885
  have htrace : WordTrace (prefixWord ++ tailWord_5021885) baseStart_5021885 baseEnd_5021885 := by
    simpa [prefixWord, tailWord_5021885, baseEnd_5021885] using wordTrace_append hprefix tailTrace_5021885
  have hstable : (prefixWord ++ tailWord_5021885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5021885).length < 2 ^ (prefixWord ++ tailWord_5021885).sum := by decide
  have hdescent : baseEnd_5021885 < baseStart_5021885 := by decide
  rcases family_descends (prefixWord ++ tailWord_5021885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022042 : List Nat := [3, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3]
def baseStart_5022042 : Nat := 118140960795 + 5022042 * 2 ^ 59
def prefixEnd_5022042 : Nat := 4983230072969 + 3 ^ 40 * 5022042 * 2
def baseEnd_5022042 : Nat := 2578721413066945471279055

theorem tailTrace_5022042 : CollatzResearch.WordTrace tailWord_5022042 prefixEnd_5022042 2578721413066945471279055 := by
  unfold tailWord_5022042
  simp only [CollatzResearch.WordTrace]
  refine ⟨45792229918001751333501095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122112613114671336889336253 45792229918001751333501095)
  ·
    refine ⟨68688344877002627000251643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45792229918001751333501095 68688344877002627000251643)
    ·
      refine ⟨103032517315503940500377465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68688344877002627000251643 103032517315503940500377465)
      ·
        refine ⟨77274387986627955375283099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103032517315503940500377465 77274387986627955375283099)
        ·
          refine ⟨115911581979941933062924649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77274387986627955375283099 115911581979941933062924649)
          ·
            refine ⟨86933686484956449797193487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115911581979941933062924649 86933686484956449797193487)
            ·
              refine ⟨130400529727434674695790231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86933686484956449797193487 130400529727434674695790231)
              ·
                refine ⟨195600794591152012043685347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130400529727434674695790231 195600794591152012043685347)
                ·
                  refine ⟨293401191886728018065528021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 195600794591152012043685347 293401191886728018065528021)
                  ·
                    refine ⟨6876590434845187923410813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 293401191886728018065528021 6876590434845187923410813)
                    ·
                      refine ⟨2578721413066945471279055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6876590434845187923410813 2578721413066945471279055)
                      ·
                        rfl

theorem cell23_5022042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 1, 1, 1, 7, 3].length) (baseStart_5022042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022042 prefixEnd_5022042 := by exact prefixLift 5022042
  have htrace : WordTrace (prefixWord ++ tailWord_5022042) baseStart_5022042 baseEnd_5022042 := by
    simpa [prefixWord, tailWord_5022042, baseEnd_5022042] using wordTrace_append hprefix tailTrace_5022042
  have hstable : (prefixWord ++ tailWord_5022042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022042).length < 2 ^ (prefixWord ++ tailWord_5022042).sum := by decide
  have hdescent : baseEnd_5022042 < baseStart_5022042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022053 : List Nat := [1, 3, 1, 3, 1, 5, 1, 3, 1, 4]
def baseStart_5022053 : Nat := 118140960795 + 5022053 * 2 ^ 59
def prefixEnd_5022053 : Nat := 4983230072969 + 3 ^ 40 * 5022053 * 2
def baseEnd_5022053 : Nat := 859575687118048309413835

theorem tailTrace_5022053 : CollatzResearch.WordTrace tailWord_5022053 prefixEnd_5022053 859575687118048309413835 := by
  unfold tailWord_5022053
  simp only [CollatzResearch.WordTrace]
  refine ⟨183169320874967154212654813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122112880583311436141769875 183169320874967154212654813)
  ·
    refine ⟨68688495328112682829745555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183169320874967154212654813 68688495328112682829745555)
    ·
      refine ⟨103032742992169024244618333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68688495328112682829745555 103032742992169024244618333)
      ·
        refine ⟨38637278622063384091731875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103032742992169024244618333 38637278622063384091731875)
        ·
          refine ⟨57955917933095076137597813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38637278622063384091731875 57955917933095076137597813)
          ·
            refine ⟨5433367306227663387899795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57955917933095076137597813 5433367306227663387899795)
            ·
              refine ⟨8150050959341495081849693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5433367306227663387899795 8150050959341495081849693)
              ·
                refine ⟨3056269109753060655693635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8150050959341495081849693 3056269109753060655693635)
                ·
                  refine ⟨4584403664629590983540453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3056269109753060655693635 4584403664629590983540453)
                  ·
                    refine ⟨859575687118048309413835, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4584403664629590983540453 859575687118048309413835)
                    ·
                      rfl

theorem cell23_5022053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 3, 1, 4].length) (baseStart_5022053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022053 prefixEnd_5022053 := by exact prefixLift 5022053
  have htrace : WordTrace (prefixWord ++ tailWord_5022053) baseStart_5022053 baseEnd_5022053 := by
    simpa [prefixWord, tailWord_5022053, baseEnd_5022053] using wordTrace_append hprefix tailTrace_5022053
  have hstable : (prefixWord ++ tailWord_5022053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022053).length < 2 ^ (prefixWord ++ tailWord_5022053).sum := by decide
  have hdescent : baseEnd_5022053 < baseStart_5022053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022070 : List Nat := [5, 1, 1, 4, 1, 2, 1, 1, 3, 4]
def baseStart_5022070 : Nat := 118140960795 + 5022070 * 2 ^ 59
def prefixEnd_5022070 : Nat := 4983230072969 + 3 ^ 40 * 5022070 * 2
def baseEnd_5022070 : Nat := 859578596841757120576309

theorem tailTrace_5022070 : CollatzResearch.WordTrace tailWord_5022070 prefixEnd_5022070 859578596841757120576309 := by
  unfold tailWord_5022070
  simp only [CollatzResearch.WordTrace]
  refine ⟨11448121307244097882251479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122113293943937044077349109 11448121307244097882251479)
  ·
    refine ⟨17172181960866146823377219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11448121307244097882251479 17172181960866146823377219)
    ·
      refine ⟨25758272941299220235065829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17172181960866146823377219 25758272941299220235065829)
      ·
        refine ⟨4829676176493603794074843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25758272941299220235065829 4829676176493603794074843)
        ·
          refine ⟨7244514264740405691112265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4829676176493603794074843 7244514264740405691112265)
          ·
            refine ⟨5433385698555304268334199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7244514264740405691112265 5433385698555304268334199)
            ·
              refine ⟨8150078547832956402501299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5433385698555304268334199 8150078547832956402501299)
              ·
                refine ⟨12225117821749434603751949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8150078547832956402501299 12225117821749434603751949)
                ·
                  refine ⟨4584419183156037976406981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12225117821749434603751949 4584419183156037976406981)
                  ·
                    refine ⟨859578596841757120576309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4584419183156037976406981 859578596841757120576309)
                    ·
                      rfl

theorem cell23_5022070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 4, 1, 2, 1, 1, 3, 4].length) (baseStart_5022070 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022070 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022070 prefixEnd_5022070 := by exact prefixLift 5022070
  have htrace : WordTrace (prefixWord ++ tailWord_5022070) baseStart_5022070 baseEnd_5022070 := by
    simpa [prefixWord, tailWord_5022070, baseEnd_5022070] using wordTrace_append hprefix tailTrace_5022070
  have hstable : (prefixWord ++ tailWord_5022070).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022070).length < 2 ^ (prefixWord ++ tailWord_5022070).sum := by decide
  have hdescent : baseEnd_5022070 < baseStart_5022070 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022083 : List Nat := [1, 1, 1, 3, 7, 1, 2, 1, 6]
def baseStart_5022083 : Nat := 118140960795 + 5022083 * 2 ^ 59
def prefixEnd_5022083 : Nat := 4983230072969 + 3 ^ 40 * 5022083 * 2
def baseEnd_5022083 : Nat := 286526940641531090096263

theorem tailTrace_5022083 : CollatzResearch.WordTrace tailWord_5022083 prefixEnd_5022083 286526940641531090096263 := by
  unfold tailWord_5022083
  simp only [CollatzResearch.WordTrace]
  refine ⟨183170415064858469336246903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122113610043238979557497935 183170415064858469336246903)
  ·
    refine ⟨274755622597287704004370355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183170415064858469336246903 274755622597287704004370355)
    ·
      refine ⟨412133433895931556006555533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274755622597287704004370355 412133433895931556006555533)
      ·
        refine ⟨154550037710974333502458325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 412133433895931556006555533 154550037710974333502458325)
        ·
          refine ⟨3622266508850960941463867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 154550037710974333502458325 3622266508850960941463867)
          ·
            refine ⟨5433399763276441412195801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3622266508850960941463867 5433399763276441412195801)
            ·
              refine ⟨4075049822457331059146851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5433399763276441412195801 4075049822457331059146851)
              ·
                refine ⟨6112574733685996588720277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4075049822457331059146851 6112574733685996588720277)
                ·
                  refine ⟨286526940641531090096263, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6112574733685996588720277 286526940641531090096263)
                  ·
                    rfl

theorem cell23_5022083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 7, 1, 2, 1, 6].length) (baseStart_5022083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022083 prefixEnd_5022083 := by exact prefixLift 5022083
  have htrace : WordTrace (prefixWord ++ tailWord_5022083) baseStart_5022083 baseEnd_5022083 := by
    simpa [prefixWord, tailWord_5022083, baseEnd_5022083] using wordTrace_append hprefix tailTrace_5022083
  have hstable : (prefixWord ++ tailWord_5022083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022083).length < 2 ^ (prefixWord ++ tailWord_5022083).sum := by decide
  have hdescent : baseEnd_5022083 < baseStart_5022083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022156 : List Nat := [2, 2, 1, 4, 3, 1, 3, 7]
def baseStart_5022156 : Nat := 118140960795 + 5022156 * 2 ^ 59
def prefixEnd_5022156 : Nat := 4983230072969 + 3 ^ 40 * 5022156 * 2
def baseEnd_5022156 : Nat := 95510368513391037972353

theorem tailTrace_5022156 : CollatzResearch.WordTrace tailWord_5022156 prefixEnd_5022156 95510368513391037972353 := by
  unfold tailWord_5022156
  simp only [CollatzResearch.WordTrace]
  refine ⟨91586538796797001401827161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122115385062396001869102881 91586538796797001401827161)
  ·
    refine ⟨68689904097597751051370371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91586538796797001401827161 68689904097597751051370371)
    ·
      refine ⟨103034856146396626577055557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68689904097597751051370371 103034856146396626577055557)
      ·
        refine ⟨19319035527449367483197917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103034856146396626577055557 19319035527449367483197917)
        ·
          refine ⟨7244638322793512806199219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19319035527449367483197917 7244638322793512806199219)
          ·
            refine ⟨10866957484190269209298829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7244638322793512806199219 10866957484190269209298829)
            ·
              refine ⟨4075109056571350953487061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10866957484190269209298829 4075109056571350953487061)
              ·
                refine ⟨95510368513391037972353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4075109056571350953487061 95510368513391037972353)
                ·
                  rfl

theorem cell23_5022156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 3, 7].length) (baseStart_5022156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022156 prefixEnd_5022156 := by exact prefixLift 5022156
  have htrace : WordTrace (prefixWord ++ tailWord_5022156) baseStart_5022156 baseEnd_5022156 := by
    simpa [prefixWord, tailWord_5022156, baseEnd_5022156] using wordTrace_append hprefix tailTrace_5022156
  have hstable : (prefixWord ++ tailWord_5022156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022156).length < 2 ^ (prefixWord ++ tailWord_5022156).sum := by decide
  have hdescent : baseEnd_5022156 < baseStart_5022156 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022259 : List Nat := [1, 1, 1, 2, 4, 2, 1, 2, 4, 5]
def baseStart_5022259 : Nat := 118140960795 + 5022259 * 2 ^ 59
def prefixEnd_5022259 : Nat := 4983230072969 + 3 ^ 40 * 5022259 * 2
def baseEnd_5022259 : Nat := 859610946122990374088519

theorem tailTrace_5022259 : CollatzResearch.WordTrace tailWord_5022259 prefixEnd_5022259 859610946122990374088519 := by
  unfold tailWord_5022259
  simp only [CollatzResearch.WordTrace]
  refine ⟨183176834312220851394653831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122117889541480567596435887 183176834312220851394653831)
  ·
    refine ⟨274765251468331277091980747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183176834312220851394653831 274765251468331277091980747)
    ·
      refine ⟨412147877202496915637971121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274765251468331277091980747 412147877202496915637971121)
      ·
        refine ⟨309110907901872686728478341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412147877202496915637971121 309110907901872686728478341)
        ·
          refine ⟨57958295231601128761589689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 309110907901872686728478341 57958295231601128761589689)
          ·
            refine ⟨43468721423700846571192267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57958295231601128761589689 43468721423700846571192267)
            ·
              refine ⟨65203082135551269856788401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43468721423700846571192267 65203082135551269856788401)
              ·
                refine ⟨48902311601663452392591301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65203082135551269856788401 48902311601663452392591301)
                ·
                  refine ⟨9169183425311897323610869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48902311601663452392591301 9169183425311897323610869)
                  ·
                    refine ⟨859610946122990374088519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9169183425311897323610869 859610946122990374088519)
                    ·
                      rfl

theorem cell23_5022259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 2, 4, 5].length) (baseStart_5022259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022259 prefixEnd_5022259 := by exact prefixLift 5022259
  have htrace : WordTrace (prefixWord ++ tailWord_5022259) baseStart_5022259 baseEnd_5022259 := by
    simpa [prefixWord, tailWord_5022259, baseEnd_5022259] using wordTrace_append hprefix tailTrace_5022259
  have hstable : (prefixWord ++ tailWord_5022259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022259).length < 2 ^ (prefixWord ++ tailWord_5022259).sum := by decide
  have hdescent : baseEnd_5022259 < baseStart_5022259 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022296 : List Nat := [2, 1, 2, 2, 1, 2, 4, 2, 2, 1, 4]
def baseStart_5022296 : Nat := 118140960795 + 5022296 * 2 ^ 59
def prefixEnd_5022296 : Nat := 4983230072969 + 3 ^ 40 * 5022296 * 2
def baseEnd_5022296 : Nat := 2578851837153187477502887

theorem tailTrace_5022296 : CollatzResearch.WordTrace tailWord_5022296 prefixEnd_5022296 2578851837153187477502887 := by
  unfold tailWord_5022296
  simp only [CollatzResearch.WordTrace]
  refine ⟨91589091906543403356875371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122118789208724537809167161 91589091906543403356875371)
  ·
    refine ⟨137383637859815105035313057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91589091906543403356875371 137383637859815105035313057)
    ·
      refine ⟨103037728394861328776484793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137383637859815105035313057 103037728394861328776484793)
      ·
        refine ⟨77278296296145996582363595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103037728394861328776484793 77278296296145996582363595)
        ·
          refine ⟨115917444444218994873545393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77278296296145996582363595 115917444444218994873545393)
          ·
            refine ⟨86938083333164246155159045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115917444444218994873545393 86938083333164246155159045)
            ·
              refine ⟨16300890624968296154092321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86938083333164246155159045 16300890624968296154092321)
              ·
                refine ⟨12225667968726222115569241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16300890624968296154092321 12225667968726222115569241)
                ·
                  refine ⟨9169250976544666586676931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12225667968726222115569241 9169250976544666586676931)
                  ·
                    refine ⟨13753876464816999880015397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9169250976544666586676931 13753876464816999880015397)
                    ·
                      refine ⟨2578851837153187477502887, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13753876464816999880015397 2578851837153187477502887)
                      ·
                        rfl

theorem cell23_5022296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 2, 2, 1, 4].length) (baseStart_5022296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022296 prefixEnd_5022296 := by exact prefixLift 5022296
  have htrace : WordTrace (prefixWord ++ tailWord_5022296) baseStart_5022296 baseEnd_5022296 := by
    simpa [prefixWord, tailWord_5022296, baseEnd_5022296] using wordTrace_append hprefix tailTrace_5022296
  have hstable : (prefixWord ++ tailWord_5022296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022296).length < 2 ^ (prefixWord ++ tailWord_5022296).sum := by decide
  have hdescent : baseEnd_5022296 < baseStart_5022296 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022316 : List Nat := [2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 3]
def baseStart_5022316 : Nat := 118140960795 + 5022316 * 2 ^ 59
def prefixEnd_5022316 : Nat := 4983230072969 + 3 ^ 40 * 5022316 * 2
def baseEnd_5022316 : Nat := 2578862106766277399252795

theorem tailTrace_5022316 : CollatzResearch.WordTrace tailWord_5022316 prefixEnd_5022316 2578862106766277399252795 := by
  unfold tailWord_5022316
  simp only [CollatzResearch.WordTrace]
  refine ⟨91589456636507175064739401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122119275515342900086319201 91589456636507175064739401)
  ·
    refine ⟨68692092477380381298554551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91589456636507175064739401 68692092477380381298554551)
    ·
      refine ⟨103038138716070571947831827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68692092477380381298554551 103038138716070571947831827)
      ·
        refine ⟨154557208074105857921747741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103038138716070571947831827 154557208074105857921747741)
        ·
          refine ⟨57958953027789696720655403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154557208074105857921747741 57958953027789696720655403)
          ·
            refine ⟨86938429541684545080983105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57958953027789696720655403 86938429541684545080983105)
            ·
              refine ⟨65203822156263408810737329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86938429541684545080983105 65203822156263408810737329)
              ·
                refine ⟨48902866617197556608052997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65203822156263408810737329 48902866617197556608052997)
                ·
                  refine ⟨9169287490724541864009937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48902866617197556608052997 9169287490724541864009937)
                  ·
                    refine ⟨6876965618043406398007453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9169287490724541864009937 6876965618043406398007453)
                    ·
                      refine ⟨2578862106766277399252795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6876965618043406398007453 2578862106766277399252795)
                      ·
                        rfl

theorem cell23_5022316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 4, 2, 3].length) (baseStart_5022316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022316 prefixEnd_5022316 := by exact prefixLift 5022316
  have htrace : WordTrace (prefixWord ++ tailWord_5022316) baseStart_5022316 baseEnd_5022316 := by
    simpa [prefixWord, tailWord_5022316, baseEnd_5022316] using wordTrace_append hprefix tailTrace_5022316
  have hstable : (prefixWord ++ tailWord_5022316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022316).length < 2 ^ (prefixWord ++ tailWord_5022316).sum := by decide
  have hdescent : baseEnd_5022316 < baseStart_5022316 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022333 : List Nat := [1, 4, 1, 1, 5, 1, 1, 1, 1, 4, 3]
def baseStart_5022333 : Nat := 118140960795 + 5022333 * 2 ^ 59
def prefixEnd_5022333 : Nat := 4983230072969 + 3 ^ 40 * 5022333 * 2
def baseEnd_5022333 : Nat := 2578870835937403832740217

theorem tailTrace_5022333 : CollatzResearch.WordTrace tailWord_5022333 prefixEnd_5022333 2578870835937403832740217 := by
  unfold tailWord_5022333
  simp only [CollatzResearch.WordTrace]
  refine ⟨183179533313952762032847653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122119688875968508021898435 183179533313952762032847653)
  ·
    refine ⟨34346162496366142881158935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183179533313952762032847653 34346162496366142881158935)
    ·
      refine ⟨51519243744549214321738403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34346162496366142881158935 51519243744549214321738403)
      ·
        refine ⟨77278865616823821482607605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51519243744549214321738403 77278865616823821482607605)
        ·
          refine ⟨7244893651577233263994463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77278865616823821482607605 7244893651577233263994463)
          ·
            refine ⟨10867340477365849895991695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7244893651577233263994463 10867340477365849895991695)
            ·
              refine ⟨16301010716048774843987543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10867340477365849895991695 16301010716048774843987543)
              ·
                refine ⟨24451516074073162265981315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16301010716048774843987543 24451516074073162265981315)
                ·
                  refine ⟨36677274111109743398971973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24451516074073162265981315 36677274111109743398971973)
                  ·
                    refine ⟨6876988895833076887307245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36677274111109743398971973 6876988895833076887307245)
                    ·
                      refine ⟨2578870835937403832740217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6876988895833076887307245 2578870835937403832740217)
                      ·
                        rfl

theorem cell23_5022333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 5, 1, 1, 1, 1, 4, 3].length) (baseStart_5022333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022333 prefixEnd_5022333 := by exact prefixLift 5022333
  have htrace : WordTrace (prefixWord ++ tailWord_5022333) baseStart_5022333 baseEnd_5022333 := by
    simpa [prefixWord, tailWord_5022333, baseEnd_5022333] using wordTrace_append hprefix tailTrace_5022333
  have hstable : (prefixWord ++ tailWord_5022333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022333).length < 2 ^ (prefixWord ++ tailWord_5022333).sum := by decide
  have hdescent : baseEnd_5022333 < baseStart_5022333 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022340 : List Nat := [2, 3, 2, 1, 3, 1, 1, 5, 1, 4]
def baseStart_5022340 : Nat := 118140960795 + 5022340 * 2 ^ 59
def prefixEnd_5022340 : Nat := 4983230072969 + 3 ^ 40 * 5022340 * 2
def baseEnd_5022340 : Nat := 859624810100661768450895

theorem tailTrace_5022340 : CollatzResearch.WordTrace tailWord_5022340 prefixEnd_5022340 859624810100661768450895 := by
  unfold tailWord_5022340
  simp only [CollatzResearch.WordTrace]
  refine ⟨91589894312463701114176237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122119859083284934818901649 91589894312463701114176237)
  ·
    refine ⟨34346210367173887917816089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91589894312463701114176237 34346210367173887917816089)
    ·
      refine ⟨25759657775380415938362067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34346210367173887917816089 25759657775380415938362067)
      ·
        refine ⟨38639486663070623907543101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25759657775380415938362067 38639486663070623907543101)
        ·
          refine ⟨14489807498651483965328663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38639486663070623907543101 14489807498651483965328663)
          ·
            refine ⟨21734711247977225947992995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14489807498651483965328663 21734711247977225947992995)
            ·
              refine ⟨32602066871965838921989493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21734711247977225947992995 32602066871965838921989493)
              ·
                refine ⟨3056443769246797398936515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32602066871965838921989493 3056443769246797398936515)
                ·
                  refine ⟨4584665653870196098404773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3056443769246797398936515 4584665653870196098404773)
                  ·
                    refine ⟨859624810100661768450895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4584665653870196098404773 859624810100661768450895)
                    ·
                      rfl

theorem cell23_5022340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 5, 1, 4].length) (baseStart_5022340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022340 prefixEnd_5022340 := by exact prefixLift 5022340
  have htrace : WordTrace (prefixWord ++ tailWord_5022340) baseStart_5022340 baseEnd_5022340 := by
    simpa [prefixWord, tailWord_5022340, baseEnd_5022340] using wordTrace_append hprefix tailTrace_5022340
  have hstable : (prefixWord ++ tailWord_5022340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022340).length < 2 ^ (prefixWord ++ tailWord_5022340).sum := by decide
  have hdescent : baseEnd_5022340 < baseStart_5022340 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022383 : List Nat := [1, 1, 2, 1, 2, 6, 2, 2, 1, 5]
def baseStart_5022383 : Nat := 118140960795 + 5022383 * 2 ^ 59
def prefixEnd_5022383 : Nat := 4983230072969 + 3 ^ 40 * 5022383 * 2
def baseEnd_5022383 : Nat := 859632169990042879038329

theorem tailTrace_5022383 : CollatzResearch.WordTrace tailWord_5022383 prefixEnd_5022383 859632169990042879038329 := by
  unfold tailWord_5022383
  simp only [CollatzResearch.WordTrace]
  refine ⟨183181356963771620572167803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122120904642514413714778535 183181356963771620572167803)
  ·
    refine ⟨274772035445657430858251705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183181356963771620572167803 274772035445657430858251705)
    ·
      refine ⟨206079026584243073143688779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274772035445657430858251705 206079026584243073143688779)
      ·
        refine ⟨309118539876364609715533169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206079026584243073143688779 309118539876364609715533169)
        ·
          refine ⟨231838904907273457286649877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309118539876364609715533169 231838904907273457286649877)
          ·
            refine ⟨10867448667528443310311713, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 231838904907273457286649877 10867448667528443310311713)
            ·
              refine ⟨8150586500646332482733785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10867448667528443310311713 8150586500646332482733785)
              ·
                refine ⟨6112939875484749362050339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8150586500646332482733785 6112939875484749362050339)
                ·
                  refine ⟨9169409813227124043075509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6112939875484749362050339 9169409813227124043075509)
                  ·
                    refine ⟨859632169990042879038329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9169409813227124043075509 859632169990042879038329)
                    ·
                      rfl

theorem cell23_5022383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 2, 2, 1, 5].length) (baseStart_5022383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022383 prefixEnd_5022383 := by exact prefixLift 5022383
  have htrace : WordTrace (prefixWord ++ tailWord_5022383) baseStart_5022383 baseEnd_5022383 := by
    simpa [prefixWord, tailWord_5022383, baseEnd_5022383] using wordTrace_append hprefix tailTrace_5022383
  have hstable : (prefixWord ++ tailWord_5022383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022383).length < 2 ^ (prefixWord ++ tailWord_5022383).sum := by decide
  have hdescent : baseEnd_5022383 < baseStart_5022383 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022396 : List Nat := [2, 2, 2, 3, 1, 1, 2, 1, 3, 6]
def baseStart_5022396 : Nat := 118140960795 + 5022396 * 2 ^ 59
def prefixEnd_5022396 : Nat := 4983230072969 + 3 ^ 40 * 5022396 * 2
def baseEnd_5022396 : Nat := 859634395072879028750809

theorem tailTrace_5022396 : CollatzResearch.WordTrace tailWord_5022396 prefixEnd_5022396 859634395072879028750809 := by
  unfold tailWord_5022396
  simp only [CollatzResearch.WordTrace]
  refine ⟨91590915556362261896195521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122121220741816349194927361 91590915556362261896195521)
  ·
    refine ⟨68693186667271696422146641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91590915556362261896195521 68693186667271696422146641)
    ·
      refine ⟨51519890000453772316609981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68693186667271696422146641 51519890000453772316609981)
      ·
        refine ⟨19319958750170164618728743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51519890000453772316609981 19319958750170164618728743)
        ·
          refine ⟨28979938125255246928093115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19319958750170164618728743 28979938125255246928093115)
          ·
            refine ⟨43469907187882870392139673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28979938125255246928093115 43469907187882870392139673)
            ·
              refine ⟨32602430390912152794104755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43469907187882870392139673 32602430390912152794104755)
              ·
                refine ⟨48903645586368229191157133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32602430390912152794104755 48903645586368229191157133)
                ·
                  refine ⟨18338867094888085946683925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48903645586368229191157133 18338867094888085946683925)
                  ·
                    refine ⟨859634395072879028750809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18338867094888085946683925 859634395072879028750809)
                    ·
                      rfl

theorem cell23_5022396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 2, 1, 3, 6].length) (baseStart_5022396 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022396 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022396 prefixEnd_5022396 := by exact prefixLift 5022396
  have htrace : WordTrace (prefixWord ++ tailWord_5022396) baseStart_5022396 baseEnd_5022396 := by
    simpa [prefixWord, tailWord_5022396, baseEnd_5022396] using wordTrace_append hprefix tailTrace_5022396
  have hstable : (prefixWord ++ tailWord_5022396).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022396).length < 2 ^ (prefixWord ++ tailWord_5022396).sum := by decide
  have hdescent : baseEnd_5022396 < baseStart_5022396 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022397 : List Nat := [1, 4, 1, 2, 1, 3, 3, 3, 1, 1, 3]
def baseStart_5022397 : Nat := 118140960795 + 5022397 * 2 ^ 59
def prefixEnd_5022397 : Nat := 4983230072969 + 3 ^ 40 * 5022397 * 2
def baseEnd_5022397 : Nat := 2578903698699291582339923

theorem tailTrace_5022397 : CollatzResearch.WordTrace tailWord_5022397 prefixEnd_5022397 2578903698699291582339923 := by
  unfold tailWord_5022397
  simp only [CollatzResearch.WordTrace]
  refine ⟨183181867585720900963177445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122121245057147267308784963 183181867585720900963177445)
  ·
    refine ⟨34346600172322668930595771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 183181867585720900963177445 34346600172322668930595771)
    ·
      refine ⟨51519900258484003395893657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34346600172322668930595771 51519900258484003395893657)
      ·
        refine ⟨38639925193863002546920243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51519900258484003395893657 38639925193863002546920243)
        ·
          refine ⟨57959887790794503820380365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38639925193863002546920243 57959887790794503820380365)
          ·
            refine ⟨21734957921547938932642637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57959887790794503820380365 21734957921547938932642637)
            ·
              refine ⟨8150609220580477099740989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21734957921547938932642637 8150609220580477099740989)
              ·
                refine ⟨3056478457717678912402871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8150609220580477099740989 3056478457717678912402871)
                ·
                  refine ⟨4584717686576518368604307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3056478457717678912402871 4584717686576518368604307)
                  ·
                    refine ⟨6877076529864777552906461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4584717686576518368604307 6877076529864777552906461)
                    ·
                      refine ⟨2578903698699291582339923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6877076529864777552906461 2578903698699291582339923)
                      ·
                        rfl

theorem cell23_5022397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_5022397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022397 prefixEnd_5022397 := by exact prefixLift 5022397
  have htrace : WordTrace (prefixWord ++ tailWord_5022397) baseStart_5022397 baseEnd_5022397 := by
    simpa [prefixWord, tailWord_5022397, baseEnd_5022397] using wordTrace_append hprefix tailTrace_5022397
  have hstable : (prefixWord ++ tailWord_5022397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022397).length < 2 ^ (prefixWord ++ tailWord_5022397).sum := by decide
  have hdescent : baseEnd_5022397 < baseStart_5022397 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022414 : List Nat := [4, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3]
def baseStart_5022414 : Nat := 118140960795 + 5022414 * 2 ^ 59
def prefixEnd_5022414 : Nat := 4983230072969 + 3 ^ 40 * 5022414 * 2
def baseEnd_5022414 : Nat := 2578912427870418015827345

theorem tailTrace_5022414 : CollatzResearch.WordTrace tailWord_5022414 prefixEnd_5022414 2578912427870418015827345 := by
  unfold tailWord_5022414
  simp only [CollatzResearch.WordTrace]
  refine ⟨22897810953332414108318287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122121658417772875244364197 22897810953332414108318287)
  ·
    refine ⟨34346716429998621162477431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22897810953332414108318287 34346716429998621162477431)
    ·
      refine ⟨51520074644997931743716147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34346716429998621162477431 51520074644997931743716147)
      ·
        refine ⟨77280111967496897615574221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51520074644997931743716147 77280111967496897615574221)
        ·
          refine ⟨28980041987811336605840333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 77280111967496897615574221 28980041987811336605840333)
          ·
            refine ⟨10867515745429251227190125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28980041987811336605840333 10867515745429251227190125)
            ·
              refine ⟨4075318404535969210196297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10867515745429251227190125 4075318404535969210196297)
              ·
                refine ⟨3056488803401976907647223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4075318404535969210196297 3056488803401976907647223)
                ·
                  refine ⟨4584733205102965361470835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3056488803401976907647223 4584733205102965361470835)
                  ·
                    refine ⟨6877099807654448042206253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4584733205102965361470835 6877099807654448042206253)
                    ·
                      refine ⟨2578912427870418015827345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6877099807654448042206253 2578912427870418015827345)
                      ·
                        rfl

theorem cell23_5022414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 3, 3, 2, 1, 1, 3].length) (baseStart_5022414 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022414 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022414 prefixEnd_5022414 := by exact prefixLift 5022414
  have htrace : WordTrace (prefixWord ++ tailWord_5022414) baseStart_5022414 baseEnd_5022414 := by
    simpa [prefixWord, tailWord_5022414, baseEnd_5022414] using wordTrace_append hprefix tailTrace_5022414
  have hstable : (prefixWord ++ tailWord_5022414).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022414).length < 2 ^ (prefixWord ++ tailWord_5022414).sum := by decide
  have hdescent : baseEnd_5022414 < baseStart_5022414 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022426 : List Nat := [3, 1, 1, 2, 2, 2, 4, 8]
def baseStart_5022426 : Nat := 118140960795 + 5022426 * 2 ^ 59
def prefixEnd_5022426 : Nat := 4983230072969 + 3 ^ 40 * 5022426 * 2
def baseEnd_5022426 : Nat := 95515503319935998847307

theorem tailTrace_5022426 : CollatzResearch.WordTrace tailWord_5022426 prefixEnd_5022426 95515503319935998847307 := by
  unfold tailWord_5022426
  simp only [CollatzResearch.WordTrace]
  refine ⟨45795731325653959728995783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122121950201743892610655421 45795731325653959728995783)
  ·
    refine ⟨68693596988480939593493675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45795731325653959728995783 68693596988480939593493675)
    ·
      refine ⟨103040395482721409390240513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68693596988480939593493675 103040395482721409390240513)
      ·
        refine ⟨77280296612041057042680385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103040395482721409390240513 77280296612041057042680385)
        ·
          refine ⟨57960222459030792782010289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77280296612041057042680385 57960222459030792782010289)
          ·
            refine ⟨43470166844273094586507717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57960222459030792782010289 43470166844273094586507717)
            ·
              refine ⟨8150656283301205234970197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43470166844273094586507717 8150656283301205234970197)
              ·
                refine ⟨95515503319935998847307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8150656283301205234970197 95515503319935998847307)
                ·
                  rfl

theorem cell23_5022426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 8].length) (baseStart_5022426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022426 prefixEnd_5022426 := by exact prefixLift 5022426
  have htrace : WordTrace (prefixWord ++ tailWord_5022426) baseStart_5022426 baseEnd_5022426 := by
    simpa [prefixWord, tailWord_5022426, baseEnd_5022426] using wordTrace_append hprefix tailTrace_5022426
  have hstable : (prefixWord ++ tailWord_5022426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022426).length < 2 ^ (prefixWord ++ tailWord_5022426).sum := by decide
  have hdescent : baseEnd_5022426 < baseStart_5022426 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022440 : List Nat := [2, 1, 4, 1, 4, 1, 1, 1, 3, 2, 3]
def baseStart_5022440 : Nat := 118140960795 + 5022440 * 2 ^ 59
def prefixEnd_5022440 : Nat := 4983230072969 + 3 ^ 40 * 5022440 * 2
def baseEnd_5022440 : Nat := 2578925778367434914102225

theorem tailTrace_5022440 : CollatzResearch.WordTrace tailWord_5022440 prefixEnd_5022440 2578925778367434914102225 := by
  unfold tailWord_5022440
  simp only [CollatzResearch.WordTrace]
  refine ⟨91591717962282559653496387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122122290616376746204661849 91591717962282559653496387)
  ·
    refine ⟨137387576943423839480244581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91591717962282559653496387 137387576943423839480244581)
    ·
      refine ⟨25760170676891969902545859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137387576943423839480244581 25760170676891969902545859)
      ·
        refine ⟨38640256015337954853818789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25760170676891969902545859 38640256015337954853818789)
        ·
          refine ⟨7245048002875866535091023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38640256015337954853818789 7245048002875866535091023)
          ·
            refine ⟨10867572004313799802636535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7245048002875866535091023 10867572004313799802636535)
            ·
              refine ⟨16301358006470699703954803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10867572004313799802636535 16301358006470699703954803)
              ·
                refine ⟨24452037009706049555932205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16301358006470699703954803 24452037009706049555932205)
                ·
                  refine ⟨9169513878639768583474577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24452037009706049555932205 9169513878639768583474577)
                  ·
                    refine ⟨6877135408979826437605933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9169513878639768583474577 6877135408979826437605933)
                    ·
                      refine ⟨2578925778367434914102225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6877135408979826437605933 2578925778367434914102225)
                      ·
                        rfl

theorem cell23_5022440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 1, 3, 2, 3].length) (baseStart_5022440 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022440 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022440 prefixEnd_5022440 := by exact prefixLift 5022440
  have htrace : WordTrace (prefixWord ++ tailWord_5022440) baseStart_5022440 baseEnd_5022440 := by
    simpa [prefixWord, tailWord_5022440, baseEnd_5022440] using wordTrace_append hprefix tailTrace_5022440
  have hstable : (prefixWord ++ tailWord_5022440).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022440).length < 2 ^ (prefixWord ++ tailWord_5022440).sum := by decide
  have hdescent : baseEnd_5022440 < baseStart_5022440 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022454 : List Nat := [5, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2]
def baseStart_5022454 : Nat := 118140960795 + 5022454 * 2 ^ 59
def prefixEnd_5022454 : Nat := 4983230072969 + 3 ^ 40 * 5022454 * 2
def baseEnd_5022454 : Nat := 2578932967096597859327161

theorem tailTrace_5022454 : CollatzResearch.WordTrace tailWord_5022454 prefixEnd_5022454 2578932967096597859327161 := by
  unfold tailWord_5022454
  simp only [CollatzResearch.WordTrace]
  refine ⟨11448996659157149981125151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122122631031009599798668277 11448996659157149981125151)
  ·
    refine ⟨17173494988735724971687727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11448996659157149981125151 17173494988735724971687727)
    ·
      refine ⟨25760242483103587457531591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17173494988735724971687727 25760242483103587457531591)
      ·
        refine ⟨38640363724655381186297387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25760242483103587457531591 38640363724655381186297387)
        ·
          refine ⟨57960545586983071779446081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38640363724655381186297387 57960545586983071779446081)
          ·
            refine ⟨43470409190237303834584561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57960545586983071779446081 43470409190237303834584561)
            ·
              refine ⟨32602806892677977875938421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43470409190237303834584561 32602806892677977875938421)
              ·
                refine ⟨3056513146188560425869227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32602806892677977875938421 3056513146188560425869227)
                ·
                  refine ⟨4584769719282840638803841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3056513146188560425869227 4584769719282840638803841)
                  ·
                    refine ⟨3438577289462130479102881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4584769719282840638803841 3438577289462130479102881)
                    ·
                      refine ⟨2578932967096597859327161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3438577289462130479102881 2578932967096597859327161)
                      ·
                        rfl

theorem cell23_5022454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_5022454 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022454 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022454 prefixEnd_5022454 := by exact prefixLift 5022454
  have htrace : WordTrace (prefixWord ++ tailWord_5022454) baseStart_5022454 baseEnd_5022454 := by
    simpa [prefixWord, tailWord_5022454, baseEnd_5022454] using wordTrace_append hprefix tailTrace_5022454
  have hstable : (prefixWord ++ tailWord_5022454).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022454).length < 2 ^ (prefixWord ++ tailWord_5022454).sum := by decide
  have hdescent : baseEnd_5022454 < baseStart_5022454 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022471 : List Nat := [1, 1, 4, 4, 1, 1, 4, 2, 1, 2, 2]
def baseStart_5022471 : Nat := 118140960795 + 5022471 * 2 ^ 59
def prefixEnd_5022471 : Nat := 4983230072969 + 3 ^ 40 * 5022471 * 2
def baseEnd_5022471 : Nat := 2578941696267724292814583

theorem tailTrace_5022471 : CollatzResearch.WordTrace tailWord_5022471 prefixEnd_5022471 2578941696267724292814583 := by
  unfold tailWord_5022471
  simp only [CollatzResearch.WordTrace]
  refine ⟨183184566587452811601371267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122123044391635207734247511 183184566587452811601371267)
  ·
    refine ⟨274776849881179217402056901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183184566587452811601371267 274776849881179217402056901)
    ·
      refine ⟨51520659352721103262885669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 274776849881179217402056901 51520659352721103262885669)
      ·
        refine ⟨9660123628635206861791063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51520659352721103262885669 9660123628635206861791063)
        ·
          refine ⟨14490185442952810292686595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9660123628635206861791063 14490185442952810292686595)
          ·
            refine ⟨21735278164429215439029893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14490185442952810292686595 21735278164429215439029893)
            ·
              refine ⟨4075364655830477894818105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21735278164429215439029893 4075364655830477894818105)
              ·
                refine ⟨3056523491872858421113579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4075364655830477894818105 3056523491872858421113579)
                ·
                  refine ⟨4584785237809287631670369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3056523491872858421113579 4584785237809287631670369)
                  ·
                    refine ⟨3438588928356965723752777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4584785237809287631670369 3438588928356965723752777)
                    ·
                      refine ⟨2578941696267724292814583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3438588928356965723752777 2578941696267724292814583)
                      ·
                        rfl

theorem cell23_5022471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 4, 2, 1, 2, 2].length) (baseStart_5022471 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022471 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022471 prefixEnd_5022471 := by exact prefixLift 5022471
  have htrace : WordTrace (prefixWord ++ tailWord_5022471) baseStart_5022471 baseEnd_5022471 := by
    simpa [prefixWord, tailWord_5022471, baseEnd_5022471] using wordTrace_append hprefix tailTrace_5022471
  have hstable : (prefixWord ++ tailWord_5022471).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022471).length < 2 ^ (prefixWord ++ tailWord_5022471).sum := by decide
  have hdescent : baseEnd_5022471 < baseStart_5022471 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022527 : List Nat := [1, 1, 2, 2, 5, 2, 1, 1, 4, 2, 2]
def baseStart_5022527 : Nat := 118140960795 + 5022527 * 2 ^ 59
def prefixEnd_5022527 : Nat := 4983230072969 + 3 ^ 40 * 5022527 * 2
def baseEnd_5022527 : Nat := 2578970451184376073714325

theorem tailTrace_5022527 : CollatzResearch.WordTrace tailWord_5022527 prefixEnd_5022527 2578970451184376073714325 := by
  unfold tailWord_5022527
  simp only [CollatzResearch.WordTrace]
  refine ⟨183186609075249933165409835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122124406050166622110273223 183186609075249933165409835)
  ·
    refine ⟨274779913612874899748114753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183186609075249933165409835 274779913612874899748114753)
    ·
      refine ⟨206084935209656174811086065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274779913612874899748114753 206084935209656174811086065)
      ·
        refine ⟨154563701407242131108314549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206084935209656174811086065 154563701407242131108314549)
        ·
          refine ⟨14490347006928949791404489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 154563701407242131108314549 14490347006928949791404489)
          ·
            refine ⟨10867760255196712343553367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14490347006928949791404489 10867760255196712343553367)
            ·
              refine ⟨16301640382795068515330051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10867760255196712343553367 16301640382795068515330051)
              ·
                refine ⟨24452460574192602772995077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16301640382795068515330051 24452460574192602772995077)
                ·
                  refine ⟨4584836357661113019936577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24452460574192602772995077 4584836357661113019936577)
                  ·
                    refine ⟨3438627268245834764952433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4584836357661113019936577 3438627268245834764952433)
                    ·
                      refine ⟨2578970451184376073714325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3438627268245834764952433 2578970451184376073714325)
                      ·
                        rfl

theorem cell23_5022527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 5, 2, 1, 1, 4, 2, 2].length) (baseStart_5022527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022527 prefixEnd_5022527 := by exact prefixLift 5022527
  have htrace : WordTrace (prefixWord ++ tailWord_5022527) baseStart_5022527 baseEnd_5022527 := by
    simpa [prefixWord, tailWord_5022527, baseEnd_5022527] using wordTrace_append hprefix tailTrace_5022527
  have hstable : (prefixWord ++ tailWord_5022527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022527).length < 2 ^ (prefixWord ++ tailWord_5022527).sum := by decide
  have hdescent : baseEnd_5022527 < baseStart_5022527 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022563 : List Nat := [1, 1, 1, 5, 3, 1, 2, 1, 1, 7]
def baseStart_5022563 : Nat := 118140960795 + 5022563 * 2 ^ 59
def prefixEnd_5022563 : Nat := 4983230072969 + 3 ^ 40 * 5022563 * 2
def baseEnd_5022563 : Nat := 859662978829312644288053

theorem tailTrace_5022563 : CollatzResearch.WordTrace tailWord_5022563 prefixEnd_5022563 859662978829312644288053 := by
  unfold tailWord_5022563
  simp only [CollatzResearch.WordTrace]
  refine ⟨183187922103119511313720343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122125281402079674209146895 183187922103119511313720343)
  ·
    refine ⟨274781883154679266970580515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183187922103119511313720343 274781883154679266970580515)
    ·
      refine ⟨412172824732018900455870773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274781883154679266970580515 412172824732018900455870773)
      ·
        refine ⟨38641202318626771917737885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 412172824732018900455870773 38641202318626771917737885)
        ·
          refine ⟨14490450869485039469151707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38641202318626771917737885 14490450869485039469151707)
          ·
            refine ⟨21735676304227559203727561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14490450869485039469151707 21735676304227559203727561)
            ·
              refine ⟨16301757228170669402795671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21735676304227559203727561 16301757228170669402795671)
              ·
                refine ⟨24452635842256004104193507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16301757228170669402795671 24452635842256004104193507)
                ·
                  refine ⟨36678953763384006156290261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24452635842256004104193507 36678953763384006156290261)
                  ·
                    refine ⟨859662978829312644288053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36678953763384006156290261 859662978829312644288053)
                    ·
                      rfl

theorem cell23_5022563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 2, 1, 1, 7].length) (baseStart_5022563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022563 prefixEnd_5022563 := by exact prefixLift 5022563
  have htrace : WordTrace (prefixWord ++ tailWord_5022563) baseStart_5022563 baseEnd_5022563 := by
    simpa [prefixWord, tailWord_5022563, baseEnd_5022563] using wordTrace_append hprefix tailTrace_5022563
  have hstable : (prefixWord ++ tailWord_5022563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022563).length < 2 ^ (prefixWord ++ tailWord_5022563).sum := by decide
  have hdescent : baseEnd_5022563 < baseStart_5022563 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022567 : List Nat := [1, 1, 5, 1, 2, 4, 1, 3, 5]
def baseStart_5022567 : Nat := 118140960795 + 5022567 * 2 ^ 59
def prefixEnd_5022567 : Nat := 4983230072969 + 3 ^ 40 * 5022567 * 2
def baseEnd_5022567 : Nat := 286554554490061768579349

theorem tailTrace_5022567 : CollatzResearch.WordTrace tailWord_5022567 prefixEnd_5022567 286554554490061768579349 := by
  unfold tailWord_5022567
  simp only [CollatzResearch.WordTrace]
  refine ⟨183188067995105019996865955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122125378663403346664577303 183188067995105019996865955)
  ·
    refine ⟨274782101992657529995298933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183188067995105019996865955 274782101992657529995298933)
    ·
      refine ⟨25760822061811643437059275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 274782101992657529995298933 25760822061811643437059275)
      ·
        refine ⟨38641233092717465155588913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25760822061811643437059275 38641233092717465155588913)
        ·
          refine ⟨28980924819538098866691685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38641233092717465155588913 28980924819538098866691685)
          ·
            refine ⟨5433923403663393537504691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28980924819538098866691685 5433923403663393537504691)
            ·
              refine ⟨8150885105495090306257037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5433923403663393537504691 8150885105495090306257037)
              ·
                refine ⟨3056581914560658864846389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8150885105495090306257037 3056581914560658864846389)
                ·
                  refine ⟨286554554490061768579349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3056581914560658864846389 286554554490061768579349)
                  ·
                    rfl

theorem cell23_5022567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 1, 3, 5].length) (baseStart_5022567 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022567 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022567 prefixEnd_5022567 := by exact prefixLift 5022567
  have htrace : WordTrace (prefixWord ++ tailWord_5022567) baseStart_5022567 baseEnd_5022567 := by
    simpa [prefixWord, tailWord_5022567, baseEnd_5022567] using wordTrace_append hprefix tailTrace_5022567
  have hstable : (prefixWord ++ tailWord_5022567).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022567).length < 2 ^ (prefixWord ++ tailWord_5022567).sum := by decide
  have hdescent : baseEnd_5022567 < baseStart_5022567 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022573 : List Nat := [1, 5, 1, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_5022573 : Nat := 118140960795 + 5022573 * 2 ^ 59
def prefixEnd_5022573 : Nat := 4983230072969 + 3 ^ 40 * 5022573 * 2
def baseEnd_5022573 : Nat := 2578994071294482893739113

theorem tailTrace_5022573 : CollatzResearch.WordTrace tailWord_5022573 prefixEnd_5022573 2578994071294482893739113 := by
  unfold tailWord_5022573
  simp only [CollatzResearch.WordTrace]
  refine ⟨183188286833083283021584373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122125524555388855347722915 183188286833083283021584373)
  ·
    refine ⟨17173901890601557783273535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 183188286833083283021584373 17173901890601557783273535)
    ·
      refine ⟨25760852835902336674910303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17173901890601557783273535 25760852835902336674910303)
      ·
        refine ⟨38641279253853505012365455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25760852835902336674910303 38641279253853505012365455)
        ·
          refine ⟨57961918880780257518548183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38641279253853505012365455 57961918880780257518548183)
          ·
            refine ⟨86942878321170386277822275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57961918880780257518548183 86942878321170386277822275)
            ·
              refine ⟨130414317481755579416733413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86942878321170386277822275 130414317481755579416733413)
              ·
                refine ⟨24452684527829171140637515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130414317481755579416733413 24452684527829171140637515)
                ·
                  refine ⟨36679026791743756710956273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24452684527829171140637515 36679026791743756710956273)
                  ·
                    refine ⟨27509270093807817533217205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36679026791743756710956273 27509270093807817533217205)
                    ·
                      refine ⟨2578994071294482893739113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27509270093807817533217205 2578994071294482893739113)
                      ·
                        rfl

theorem cell23_5022573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_5022573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022573 prefixEnd_5022573 := by exact prefixLift 5022573
  have htrace : WordTrace (prefixWord ++ tailWord_5022573) baseStart_5022573 baseEnd_5022573 := by
    simpa [prefixWord, tailWord_5022573, baseEnd_5022573] using wordTrace_append hprefix tailTrace_5022573
  have hstable : (prefixWord ++ tailWord_5022573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022573).length < 2 ^ (prefixWord ++ tailWord_5022573).sum := by decide
  have hdescent : baseEnd_5022573 < baseStart_5022573 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022603 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 3, 4, 3]
def baseStart_5022603 : Nat := 118140960795 + 5022603 * 2 ^ 59
def prefixEnd_5022603 : Nat := 4983230072969 + 3 ^ 40 * 5022603 * 2
def baseEnd_5022603 : Nat := 2579009475714117776363975

theorem tailTrace_5022603 : CollatzResearch.WordTrace tailWord_5022603 prefixEnd_5022603 2579009475714117776363975 := by
  unfold tailWord_5022603
  simp only [CollatzResearch.WordTrace]
  refine ⟨183189381022974598145176463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122126254015316398763450975 183189381022974598145176463)
  ·
    refine ⟨274784071534461897217764695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183189381022974598145176463 274784071534461897217764695)
    ·
      refine ⟨412176107301692845826647043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274784071534461897217764695 412176107301692845826647043)
      ·
        refine ⟨618264160952539268739970565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412176107301692845826647043 618264160952539268739970565)
        ·
          refine ⟨115924530178601112888744481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 618264160952539268739970565 115924530178601112888744481)
          ·
            refine ⟨86943397633950834666558361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115924530178601112888744481 86943397633950834666558361)
            ·
              refine ⟨65207548225463125999918771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86943397633950834666558361 65207548225463125999918771)
              ·
                refine ⟨97811322338194688999878157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65207548225463125999918771 97811322338194688999878157)
                ·
                  refine ⟨36679245876823008374954309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97811322338194688999878157 36679245876823008374954309)
                  ·
                    refine ⟨6877358601904314070303933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36679245876823008374954309 6877358601904314070303933)
                    ·
                      refine ⟨2579009475714117776363975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6877358601904314070303933 2579009475714117776363975)
                      ·
                        rfl

theorem cell23_5022603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 3, 4, 3].length) (baseStart_5022603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022603 prefixEnd_5022603 := by exact prefixLift 5022603
  have htrace : WordTrace (prefixWord ++ tailWord_5022603) baseStart_5022603 baseEnd_5022603 := by
    simpa [prefixWord, tailWord_5022603, baseEnd_5022603] using wordTrace_append hprefix tailTrace_5022603
  have hstable : (prefixWord ++ tailWord_5022603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022603).length < 2 ^ (prefixWord ++ tailWord_5022603).sum := by decide
  have hdescent : baseEnd_5022603 < baseStart_5022603 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022614 : List Nat := [5, 3, 1, 1, 1, 1, 1, 3, 2, 5]
def baseStart_5022614 : Nat := 118140960795 + 5022614 * 2 ^ 59
def prefixEnd_5022614 : Nat := 4983230072969 + 3 ^ 40 * 5022614 * 2
def baseEnd_5022614 : Nat := 859671708000439077775475

theorem tailTrace_5022614 : CollatzResearch.WordTrace tailWord_5022614 prefixEnd_5022614 859671708000439077775475 := by
  unfold tailWord_5022614
  simp only [CollatzResearch.WordTrace]
  refine ⟨11449361389120921688989181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122126521483956498015884597 11449361389120921688989181)
  ·
    refine ⟨4293510520920345633370943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11449361389120921688989181 4293510520920345633370943)
    ·
      refine ⟨6440265781380518450056415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4293510520920345633370943 6440265781380518450056415)
      ·
        refine ⟨9660398672070777675084623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6440265781380518450056415 9660398672070777675084623)
        ·
          refine ⟨14490598008106166512626935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9660398672070777675084623 14490598008106166512626935)
          ·
            refine ⟨21735897012159249768940403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14490598008106166512626935 21735897012159249768940403)
            ·
              refine ⟨32603845518238874653410605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21735897012159249768940403 32603845518238874653410605)
              ·
                refine ⟨12226442069339577995028977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32603845518238874653410605 12226442069339577995028977)
                ·
                  refine ⟨9169831552004683496271733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12226442069339577995028977 9169831552004683496271733)
                  ·
                    refine ⟨859671708000439077775475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9169831552004683496271733 859671708000439077775475)
                    ·
                      rfl

theorem cell23_5022614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 1, 3, 2, 5].length) (baseStart_5022614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022614 prefixEnd_5022614 := by exact prefixLift 5022614
  have htrace : WordTrace (prefixWord ++ tailWord_5022614) baseStart_5022614 baseEnd_5022614 := by
    simpa [prefixWord, tailWord_5022614, baseEnd_5022614] using wordTrace_append hprefix tailTrace_5022614
  have hstable : (prefixWord ++ tailWord_5022614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022614).length < 2 ^ (prefixWord ++ tailWord_5022614).sum := by decide
  have hdescent : baseEnd_5022614 < baseStart_5022614 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022667 : List Nat := [1, 1, 1, 1, 3, 6, 1, 2, 3, 1, 3]
def baseStart_5022667 : Nat := 118140960795 + 5022667 * 2 ^ 59
def prefixEnd_5022667 : Nat := 4983230072969 + 3 ^ 40 * 5022667 * 2
def baseEnd_5022667 : Nat := 2579042338476005525963681

theorem tailTrace_5022667 : CollatzResearch.WordTrace tailWord_5022667 prefixEnd_5022667 2579042338476005525963681 := by
  unfold tailWord_5022667
  simp only [CollatzResearch.WordTrace]
  refine ⟨183191715294742737075506255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122127810196495158050337503 183191715294742737075506255)
  ·
    refine ⟨274787572942114105613259383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183191715294742737075506255 274787572942114105613259383)
    ·
      refine ⟨412181359413171158419889075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274787572942114105613259383 412181359413171158419889075)
      ·
        refine ⟨618272039119756737629833613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 412181359413171158419889075 618272039119756737629833613)
        ·
          refine ⟨231852014669908776611187605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 618272039119756737629833613 231852014669908776611187605)
          ·
            refine ⟨10868063187651973903649419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 231852014669908776611187605 10868063187651973903649419)
            ·
              refine ⟨16302094781477960855474129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10868063187651973903649419 16302094781477960855474129)
              ·
                refine ⟨12226571086108470641605597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16302094781477960855474129 12226571086108470641605597)
                ·
                  refine ⟨4584964157290676490602099, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12226571086108470641605597 4584964157290676490602099)
                  ·
                    refine ⟨6877446235936014735903149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4584964157290676490602099 6877446235936014735903149)
                    ·
                      refine ⟨2579042338476005525963681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6877446235936014735903149 2579042338476005525963681)
                      ·
                        rfl

theorem cell23_5022667_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 6, 1, 2, 3, 1, 3].length) (baseStart_5022667 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022667 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022667 prefixEnd_5022667 := by exact prefixLift 5022667
  have htrace : WordTrace (prefixWord ++ tailWord_5022667) baseStart_5022667 baseEnd_5022667 := by
    simpa [prefixWord, tailWord_5022667, baseEnd_5022667] using wordTrace_append hprefix tailTrace_5022667
  have hstable : (prefixWord ++ tailWord_5022667).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022667).length < 2 ^ (prefixWord ++ tailWord_5022667).sum := by decide
  have hdescent : baseEnd_5022667 < baseStart_5022667 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022667) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022670 : List Nat := [4, 1, 1, 1, 2, 3, 2, 1, 3, 5]
def baseStart_5022670 : Nat := 118140960795 + 5022670 * 2 ^ 59
def prefixEnd_5022670 : Nat := 4983230072969 + 3 ^ 40 * 5022670 * 2
def baseEnd_5022670 : Nat := 859681292972656338075389

theorem tailTrace_5022670 : CollatzResearch.WordTrace tailWord_5022670 prefixEnd_5022670 859681292972656338075389 := by
  unfold tailWord_5022670
  simp only [CollatzResearch.WordTrace]
  refine ⟨22898978089216483573483183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122127883142487912391910309 22898978089216483573483183)
  ·
    refine ⟨34348467133824725360224775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22898978089216483573483183 34348467133824725360224775)
    ·
      refine ⟨51522700700737088040337163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34348467133824725360224775 51522700700737088040337163)
      ·
        refine ⟨77284051051105632060505745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51522700700737088040337163 77284051051105632060505745)
        ·
          refine ⟨57963038288329224045379309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77284051051105632060505745 57963038288329224045379309)
          ·
            refine ⟨21736139358123459017017241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57963038288329224045379309 21736139358123459017017241)
            ·
              refine ⟨16302104518592594262762931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21736139358123459017017241 16302104518592594262762931)
              ·
                refine ⟨24453156777888891394144397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16302104518592594262762931 24453156777888891394144397)
                ·
                  refine ⟨9169933791708334272804149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24453156777888891394144397 9169933791708334272804149)
                  ·
                    refine ⟨859681292972656338075389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9169933791708334272804149 859681292972656338075389)
                    ·
                      rfl

theorem cell23_5022670_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 1, 3, 5].length) (baseStart_5022670 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022670 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022670 prefixEnd_5022670 := by exact prefixLift 5022670
  have htrace : WordTrace (prefixWord ++ tailWord_5022670) baseStart_5022670 baseEnd_5022670 := by
    simpa [prefixWord, tailWord_5022670, baseEnd_5022670] using wordTrace_append hprefix tailTrace_5022670
  have hstable : (prefixWord ++ tailWord_5022670).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022670).length < 2 ^ (prefixWord ++ tailWord_5022670).sum := by decide
  have hdescent : baseEnd_5022670 < baseStart_5022670 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022670) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022687 : List Nat := [1, 1, 2, 3, 5, 1, 1, 3, 1, 5]
def baseStart_5022687 : Nat := 118140960795 + 5022687 * 2 ^ 59
def prefixEnd_5022687 : Nat := 4983230072969 + 3 ^ 40 * 5022687 * 2
def baseEnd_5022687 : Nat := 859684202696365149237863

theorem tailTrace_5022687 : CollatzResearch.WordTrace tailWord_5022687 prefixEnd_5022687 859684202696365149237863 := by
  unfold tailWord_5022687
  simp only [CollatzResearch.WordTrace]
  refine ⟨183192444754670280491234315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122128296503113520327489543 183192444754670280491234315)
  ·
    refine ⟨274788667132005420736851473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183192444754670280491234315 274788667132005420736851473)
    ·
      refine ⟨206091500349004065552638605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274788667132005420736851473 206091500349004065552638605)
      ·
        refine ⟨77284312630876524582239477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206091500349004065552638605 77284312630876524582239477)
        ·
          refine ⟨7245404309144674179584951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 77284312630876524582239477 7245404309144674179584951)
          ·
            refine ⟨10868106463717011269377427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7245404309144674179584951 10868106463717011269377427)
            ·
              refine ⟨16302159695575516904066141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10868106463717011269377427 16302159695575516904066141)
              ·
                refine ⟨6113309885840818839024803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16302159695575516904066141 6113309885840818839024803)
                ·
                  refine ⟨9169964828761228258537205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6113309885840818839024803 9169964828761228258537205)
                  ·
                    refine ⟨859684202696365149237863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9169964828761228258537205 859684202696365149237863)
                    ·
                      rfl

theorem cell23_5022687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 1, 1, 3, 1, 5].length) (baseStart_5022687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022687 prefixEnd_5022687 := by exact prefixLift 5022687
  have htrace : WordTrace (prefixWord ++ tailWord_5022687) baseStart_5022687 baseEnd_5022687 := by
    simpa [prefixWord, tailWord_5022687, baseEnd_5022687] using wordTrace_append hprefix tailTrace_5022687
  have hstable : (prefixWord ++ tailWord_5022687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022687).length < 2 ^ (prefixWord ++ tailWord_5022687).sum := by decide
  have hdescent : baseEnd_5022687 < baseStart_5022687 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022713 : List Nat := [1, 2, 1, 3, 1, 3, 2, 10]
def baseStart_5022713 : Nat := 118140960795 + 5022713 * 2 ^ 59
def prefixEnd_5022713 : Nat := 4983230072969 + 3 ^ 40 * 5022713 * 2
def baseEnd_5022713 : Nat := 95520961429115272073647

theorem tailTrace_5022713 : CollatzResearch.WordTrace tailWord_5022713 prefixEnd_5022713 95520961429115272073647 := by
  unfold tailWord_5022713
  simp only [CollatzResearch.WordTrace]
  refine ⟨183193393052576086931680793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122128928701717391287787195 183193393052576086931680793)
  ·
    refine ⟨137395044789432065198760595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183193393052576086931680793 137395044789432065198760595)
    ·
      refine ⟨206092567184148097798140893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137395044789432065198760595 206092567184148097798140893)
      ·
        refine ⟨77284712694055536674302835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206092567184148097798140893 77284712694055536674302835)
        ·
          refine ⟨115927069041083305011454253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77284712694055536674302835 115927069041083305011454253)
          ·
            refine ⟨43472650890406239379295345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115927069041083305011454253 43472650890406239379295345)
            ·
              refine ⟨32604488167804679534471509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43472650890406239379295345 32604488167804679534471509)
              ·
                refine ⟨95520961429115272073647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 32604488167804679534471509 95520961429115272073647)
                ·
                  rfl

theorem cell23_5022713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 10].length) (baseStart_5022713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022713 prefixEnd_5022713 := by exact prefixLift 5022713
  have htrace : WordTrace (prefixWord ++ tailWord_5022713) baseStart_5022713 baseEnd_5022713 := by
    simpa [prefixWord, tailWord_5022713, baseEnd_5022713] using wordTrace_append hprefix tailTrace_5022713
  have hstable : (prefixWord ++ tailWord_5022713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022713).length < 2 ^ (prefixWord ++ tailWord_5022713).sum := by decide
  have hdescent : baseEnd_5022713 < baseStart_5022713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022730 : List Nat := [3, 1, 2, 2, 3, 2, 1, 9]
def baseStart_5022730 : Nat := 118140960795 + 5022730 * 2 ^ 59
def prefixEnd_5022730 : Nat := 4983230072969 + 3 ^ 40 * 5022730 * 2
def baseEnd_5022730 : Nat := 95521284731749584425033

theorem tailTrace_5022730 : CollatzResearch.WordTrace tailWord_5022730 prefixEnd_5022730 95521284731749584425033 := by
  unfold tailWord_5022730
  simp only [CollatzResearch.WordTrace]
  refine ⟨45798503273378624708762411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122129342062342999223366429 45798503273378624708762411)
  ·
    refine ⟨68697754910067937063143617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45798503273378624708762411 68697754910067937063143617)
    ·
      refine ⟨51523316182550952797357713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68697754910067937063143617 51523316182550952797357713)
      ·
        refine ⟨38642487136913214598018285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51523316182550952797357713 38642487136913214598018285)
        ·
          refine ⟨14490932676342455474256857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38642487136913214598018285 14490932676342455474256857)
          ·
            refine ⟨10868199507256841605692643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14490932676342455474256857 10868199507256841605692643)
            ·
              refine ⟨16302299260885262408538965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10868199507256841605692643 16302299260885262408538965)
              ·
                refine ⟨95521284731749584425033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 16302299260885262408538965 95521284731749584425033)
                ·
                  rfl

theorem cell23_5022730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 9].length) (baseStart_5022730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022730 prefixEnd_5022730 := by exact prefixLift 5022730
  have htrace : WordTrace (prefixWord ++ tailWord_5022730) baseStart_5022730 baseEnd_5022730 := by
    simpa [prefixWord, tailWord_5022730, baseEnd_5022730] using wordTrace_append hprefix tailTrace_5022730
  have hstable : (prefixWord ++ tailWord_5022730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022730).length < 2 ^ (prefixWord ++ tailWord_5022730).sum := by decide
  have hdescent : baseEnd_5022730 < baseStart_5022730 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022757 : List Nat := [1, 3, 1, 2, 2, 2, 1, 3, 4, 1, 3]
def baseStart_5022757 : Nat := 118140960795 + 5022757 * 2 ^ 59
def prefixEnd_5022757 : Nat := 4983230072969 + 3 ^ 40 * 5022757 * 2
def baseEnd_5022757 : Nat := 2579088551734910173838267

theorem tailTrace_5022757 : CollatzResearch.WordTrace tailWord_5022757 prefixEnd_5022757 2579088551734910173838267 := by
  unfold tailWord_5022757
  simp only [CollatzResearch.WordTrace]
  refine ⟨183194997864416682446282525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122129998576277788297521683 183194997864416682446282525)
  ·
    refine ⟨68698124199156255917355947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183194997864416682446282525 68698124199156255917355947)
    ·
      refine ⟨103047186298734383876033921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68698124199156255917355947 103047186298734383876033921)
      ·
        refine ⟨77285389724050787907025441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103047186298734383876033921 77285389724050787907025441)
        ·
          refine ⟨57964042293038090930269081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77285389724050787907025441 57964042293038090930269081)
          ·
            refine ⟨43473031719778568197701811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57964042293038090930269081 43473031719778568197701811)
            ·
              refine ⟨65209547579667852296552717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43473031719778568197701811 65209547579667852296552717)
              ·
                refine ⟨24453580342375444611207269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 65209547579667852296552717 24453580342375444611207269)
                ·
                  refine ⟨4585046314195395864601363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24453580342375444611207269 4585046314195395864601363)
                  ·
                    refine ⟨6877569471293093796902045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4585046314195395864601363 6877569471293093796902045)
                    ·
                      refine ⟨2579088551734910173838267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6877569471293093796902045 2579088551734910173838267)
                      ·
                        rfl

theorem cell23_5022757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 3, 4, 1, 3].length) (baseStart_5022757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022757 prefixEnd_5022757 := by exact prefixLift 5022757
  have htrace : WordTrace (prefixWord ++ tailWord_5022757) baseStart_5022757 baseEnd_5022757 := by
    simpa [prefixWord, tailWord_5022757, baseEnd_5022757] using wordTrace_append hprefix tailTrace_5022757
  have hstable : (prefixWord ++ tailWord_5022757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022757).length < 2 ^ (prefixWord ++ tailWord_5022757).sum := by decide
  have hdescent : baseEnd_5022757 < baseStart_5022757 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022800 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 3]
def baseStart_5022800 : Nat := 118140960795 + 5022800 * 2 ^ 59
def prefixEnd_5022800 : Nat := 4983230072969 + 3 ^ 40 * 5022800 * 2
def baseEnd_5022800 : Nat := 2579110631403053505600569

theorem tailTrace_5022800 : CollatzResearch.WordTrace tailWord_5022800 prefixEnd_5022800 2579110631403053505600569 := by
  unfold tailWord_5022800
  simp only [CollatzResearch.WordTrace]
  refine ⟨91598283101630450395048927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122131044135507267193398569 91598283101630450395048927)
  ·
    refine ⟨137397424652445675592573391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91598283101630450395048927 137397424652445675592573391)
    ·
      refine ⟨206096136978668513388860087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137397424652445675592573391 206096136978668513388860087)
      ·
        refine ⟨309144205468002770083290131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206096136978668513388860087 309144205468002770083290131)
        ·
          refine ⟨463716308202004155124935197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309144205468002770083290131 463716308202004155124935197)
          ·
            refine ⟨173893615575751558171850699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 463716308202004155124935197 173893615575751558171850699)
            ·
              refine ⟨260840423363627337257776049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173893615575751558171850699 260840423363627337257776049)
              ·
                refine ⟨195630317522720502943332037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 260840423363627337257776049 195630317522720502943332037)
                ·
                  refine ⟨36680684535510094301874757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 195630317522720502943332037 36680684535510094301874757)
                  ·
                    refine ⟨6877628350408142681601517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36680684535510094301874757 6877628350408142681601517)
                    ·
                      refine ⟨2579110631403053505600569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6877628350408142681601517 2579110631403053505600569)
                      ·
                        rfl

theorem cell23_5022800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 4, 4, 3].length) (baseStart_5022800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022800 prefixEnd_5022800 := by exact prefixLift 5022800
  have htrace : WordTrace (prefixWord ++ tailWord_5022800) baseStart_5022800 baseEnd_5022800 := by
    simpa [prefixWord, tailWord_5022800, baseEnd_5022800] using wordTrace_append hprefix tailTrace_5022800
  have hstable : (prefixWord ++ tailWord_5022800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022800).length < 2 ^ (prefixWord ++ tailWord_5022800).sum := by decide
  have hdescent : baseEnd_5022800 < baseStart_5022800 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022820 : List Nat := [2, 3, 1, 1, 2, 1, 1, 5, 7]
def baseStart_5022820 : Nat := 118140960795 + 5022820 * 2 ^ 59
def prefixEnd_5022820 : Nat := 4983230072969 + 3 ^ 40 * 5022820 * 2
def baseEnd_5022820 : Nat := 286568989001793714150053

theorem tailTrace_5022820 : CollatzResearch.WordTrace tailWord_5022820 prefixEnd_5022820 286568989001793714150053 := by
  unfold tailWord_5022820
  simp only [CollatzResearch.WordTrace]
  refine ⟨91598647831594222102912957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122131530442125629470550609 91598647831594222102912957)
  ·
    refine ⟨34349492936847833288592359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91598647831594222102912957 34349492936847833288592359)
    ·
      refine ⟨51524239405271749932888539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34349492936847833288592359 51524239405271749932888539)
      ·
        refine ⟨77286359107907624899332809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51524239405271749932888539 77286359107907624899332809)
        ·
          refine ⟨57964769330930718674499607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77286359107907624899332809 57964769330930718674499607)
          ·
            refine ⟨86947153996396078011749411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57964769330930718674499607 86947153996396078011749411)
            ·
              refine ⟨130420730994594117017624117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86947153996396078011749411 130420730994594117017624117)
              ·
                refine ⟨12226943530743198470402261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 130420730994594117017624117 12226943530743198470402261)
                ·
                  refine ⟨286568989001793714150053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12226943530743198470402261 286568989001793714150053)
                  ·
                    rfl

theorem cell23_5022820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 5, 7].length) (baseStart_5022820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022820 prefixEnd_5022820 := by exact prefixLift 5022820
  have htrace : WordTrace (prefixWord ++ tailWord_5022820) baseStart_5022820 baseEnd_5022820 := by
    simpa [prefixWord, tailWord_5022820, baseEnd_5022820] using wordTrace_append hprefix tailTrace_5022820
  have hstable : (prefixWord ++ tailWord_5022820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022820).length < 2 ^ (prefixWord ++ tailWord_5022820).sum := by decide
  have hdescent : baseEnd_5022820 < baseStart_5022820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022824 : List Nat := [2, 1, 4, 4, 1, 1, 1, 1, 2, 6]
def baseStart_5022824 : Nat := 118140960795 + 5022824 * 2 ^ 59
def prefixEnd_5022824 : Nat := 4983230072969 + 3 ^ 40 * 5022824 * 2
def baseEnd_5022824 : Nat := 859707651646253803900153

theorem tailTrace_5022824 : CollatzResearch.WordTrace tailWord_5022824 prefixEnd_5022824 859707651646253803900153 := by
  unfold tailWord_5022824
  simp only [CollatzResearch.WordTrace]
  refine ⟨91598720777586976444485763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122131627703449301925981017 91598720777586976444485763)
  ·
    refine ⟨137398081166380464666728645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91598720777586976444485763 137398081166380464666728645)
    ·
      refine ⟨25762140218696337125011621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137398081166380464666728645 25762140218696337125011621)
      ·
        refine ⟨4830401291005563210939679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25762140218696337125011621 4830401291005563210939679)
        ·
          refine ⟨7245601936508344816409519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4830401291005563210939679 7245601936508344816409519)
          ·
            refine ⟨10868402904762517224614279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7245601936508344816409519 10868402904762517224614279)
            ·
              refine ⟨16302604357143775836921419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10868402904762517224614279 16302604357143775836921419)
              ·
                refine ⟨24453906535715663755382129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16302604357143775836921419 24453906535715663755382129)
                ·
                  refine ⟨18340429901786747816536597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24453906535715663755382129 18340429901786747816536597)
                  ·
                    refine ⟨859707651646253803900153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18340429901786747816536597 859707651646253803900153)
                    ·
                      rfl

theorem cell23_5022824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 1, 2, 6].length) (baseStart_5022824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022824 prefixEnd_5022824 := by exact prefixLift 5022824
  have htrace : WordTrace (prefixWord ++ tailWord_5022824) baseStart_5022824 baseEnd_5022824 := by
    simpa [prefixWord, tailWord_5022824, baseEnd_5022824] using wordTrace_append hprefix tailTrace_5022824
  have hstable : (prefixWord ++ tailWord_5022824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022824).length < 2 ^ (prefixWord ++ tailWord_5022824).sum := by decide
  have hdescent : baseEnd_5022824 < baseStart_5022824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022860 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 3, 2, 5]
def baseStart_5022860 : Nat := 118140960795 + 5022860 * 2 ^ 59
def prefixEnd_5022860 : Nat := 4983230072969 + 3 ^ 40 * 5022860 * 2
def baseEnd_5022860 : Nat := 2579141440242323270850293

theorem tailTrace_5022860 : CollatzResearch.WordTrace tailWord_5022860 prefixEnd_5022860 2579141440242323270850293 := by
  unfold tailWord_5022860
  simp only [CollatzResearch.WordTrace]
  refine ⟨91599377291521765518641017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122132503055362354024854689 91599377291521765518641017)
  ·
    refine ⟨68699532968641324138980763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91599377291521765518641017 68699532968641324138980763)
    ·
      refine ⟨103049299452961986208471145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68699532968641324138980763 103049299452961986208471145)
      ·
        refine ⟨77286974589721489656353359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103049299452961986208471145 77286974589721489656353359)
        ·
          refine ⟨115930461884582234484530039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77286974589721489656353359 115930461884582234484530039)
          ·
            refine ⟨173895692826873351726795059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115930461884582234484530039 173895692826873351726795059)
            ·
              refine ⟨260843539240310027590192589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173895692826873351726795059 260843539240310027590192589)
              ·
                refine ⟨97816327215116260346322221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 260843539240310027590192589 97816327215116260346322221)
                ·
                  refine ⟨36681122705668597629870833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97816327215116260346322221 36681122705668597629870833)
                  ·
                    refine ⟨27510842029251448222403125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36681122705668597629870833 27510842029251448222403125)
                    ·
                      refine ⟨2579141440242323270850293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27510842029251448222403125 2579141440242323270850293)
                      ·
                        rfl

theorem cell23_5022860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 3, 2, 5].length) (baseStart_5022860 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022860 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022860 prefixEnd_5022860 := by exact prefixLift 5022860
  have htrace : WordTrace (prefixWord ++ tailWord_5022860) baseStart_5022860 baseEnd_5022860 := by
    simpa [prefixWord, tailWord_5022860, baseEnd_5022860] using wordTrace_append hprefix tailTrace_5022860
  have hstable : (prefixWord ++ tailWord_5022860).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022860).length < 2 ^ (prefixWord ++ tailWord_5022860).sum := by decide
  have hdescent : baseEnd_5022860 < baseStart_5022860 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022944 : List Nat := [2, 1, 1, 3, 1, 4, 4, 1, 6]
def baseStart_5022944 : Nat := 118140960795 + 5022944 * 2 ^ 59
def prefixEnd_5022944 : Nat := 4983230072969 + 3 ^ 40 * 5022944 * 2
def baseEnd_5022944 : Nat := 286576063624144549133323

theorem tailTrace_5022944 : CollatzResearch.WordTrace tailWord_5022944 prefixEnd_5022944 286576063624144549133323 := by
  unfold tailWord_5022944
  simp only [CollatzResearch.WordTrace]
  refine ⟨91600909157369606691669943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122134545543159475588893257 91600909157369606691669943)
  ·
    refine ⟨137401363736054410037504915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91600909157369606691669943 137401363736054410037504915)
    ·
      refine ⟨206102045604081615056257373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137401363736054410037504915 206102045604081615056257373)
      ·
        refine ⟨77288267101530605646096515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206102045604081615056257373 77288267101530605646096515)
        ·
          refine ⟨115932400652295908469144773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77288267101530605646096515 115932400652295908469144773)
          ·
            refine ⟨21737325122305482837964645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115932400652295908469144773 21737325122305482837964645)
            ·
              refine ⟨4075748460432278032118371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21737325122305482837964645 4075748460432278032118371)
              ·
                refine ⟨6113622690648417048177557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4075748460432278032118371 6113622690648417048177557)
                ·
                  refine ⟨286576063624144549133323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 6113622690648417048177557 286576063624144549133323)
                  ·
                    rfl

theorem cell23_5022944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 4, 1, 6].length) (baseStart_5022944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022944 prefixEnd_5022944 := by exact prefixLift 5022944
  have htrace : WordTrace (prefixWord ++ tailWord_5022944) baseStart_5022944 baseEnd_5022944 := by
    simpa [prefixWord, tailWord_5022944, baseEnd_5022944] using wordTrace_append hprefix tailTrace_5022944
  have hstable : (prefixWord ++ tailWord_5022944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022944).length < 2 ^ (prefixWord ++ tailWord_5022944).sum := by decide
  have hdescent : baseEnd_5022944 < baseStart_5022944 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022988 : List Nat := [2, 2, 1, 2, 2, 4, 1, 4, 1, 1, 3]
def baseStart_5022988 : Nat := 118140960795 + 5022988 * 2 ^ 59
def prefixEnd_5022988 : Nat := 4983230072969 + 3 ^ 40 * 5022988 * 2
def baseEnd_5022988 : Nat := 2579207165766098770049705

theorem tailTrace_5022988 : CollatzResearch.WordTrace tailWord_5022988 prefixEnd_5022988 2579207165766098770049705 := by
  unfold tailWord_5022988
  simp only [CollatzResearch.WordTrace]
  refine ⟨91601711563289904448970809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122135615417719872598627745 91601711563289904448970809)
  ·
    refine ⟨68701283672467428336728107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91601711563289904448970809 68701283672467428336728107)
    ·
      refine ⟨103051925508701142505092161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68701283672467428336728107 103051925508701142505092161)
      ·
        refine ⟨77288944131525856878819121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103051925508701142505092161 77288944131525856878819121)
        ·
          refine ⟨57966708098644392659114341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77288944131525856878819121 57966708098644392659114341)
          ·
            refine ⟨10868757768495823623583939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57966708098644392659114341 10868757768495823623583939)
            ·
              refine ⟨16303136652743735435375909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10868757768495823623583939 16303136652743735435375909)
              ·
                refine ⟨3056838122389450394132983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16303136652743735435375909 3056838122389450394132983)
                ·
                  refine ⟨4585257183584175591199475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3056838122389450394132983 4585257183584175591199475)
                  ·
                    refine ⟨6877885775376263386799213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4585257183584175591199475 6877885775376263386799213)
                    ·
                      refine ⟨2579207165766098770049705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6877885775376263386799213 2579207165766098770049705)
                      ·
                        rfl

theorem cell23_5022988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 4, 1, 4, 1, 1, 3].length) (baseStart_5022988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022988 prefixEnd_5022988 := by exact prefixLift 5022988
  have htrace : WordTrace (prefixWord ++ tailWord_5022988) baseStart_5022988 baseEnd_5022988 := by
    simpa [prefixWord, tailWord_5022988, baseEnd_5022988] using wordTrace_append hprefix tailTrace_5022988
  have hstable : (prefixWord ++ tailWord_5022988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022988).length < 2 ^ (prefixWord ++ tailWord_5022988).sum := by decide
  have hdescent : baseEnd_5022988 < baseStart_5022988 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5022997 : List Nat := [1, 3, 2, 1, 2, 1, 1, 3, 3, 1, 5]
def baseStart_5022997 : Nat := 118140960795 + 5022997 * 2 ^ 59
def prefixEnd_5022997 : Nat := 4983230072969 + 3 ^ 40 * 5022997 * 2
def baseEnd_5022997 : Nat := 2579211787091989234837163

theorem tailTrace_5022997 : CollatzResearch.WordTrace tailWord_5022997 prefixEnd_5022997 2579211787091989234837163 := by
  unfold tailWord_5022997
  simp only [CollatzResearch.WordTrace]
  refine ⟨183203751383547203435019245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122135834255698135623346163 183203751383547203435019245)
  ·
    refine ⟨68701406768830201288132217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183203751383547203435019245 68701406768830201288132217)
    ·
      refine ⟨51526055076622650966099163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68701406768830201288132217 51526055076622650966099163)
      ·
        refine ⟨77289082614933976449148745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51526055076622650966099163 77289082614933976449148745)
        ·
          refine ⟨57966811961200482336861559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77289082614933976449148745 57966811961200482336861559)
          ·
            refine ⟨86950217941800723505292339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57966811961200482336861559 86950217941800723505292339)
            ·
              refine ⟨130425326912701085257938509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86950217941800723505292339 130425326912701085257938509)
              ·
                refine ⟨48909497592262906971726941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130425326912701085257938509 48909497592262906971726941)
                ·
                  refine ⟨18341061597098590114397603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48909497592262906971726941 18341061597098590114397603)
                  ·
                    refine ⟨27511592395647885171596405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18341061597098590114397603 27511592395647885171596405)
                    ·
                      refine ⟨2579211787091989234837163, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27511592395647885171596405 2579211787091989234837163)
                      ·
                        rfl

theorem cell23_5022997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_5022997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5022997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5022997 prefixEnd_5022997 := by exact prefixLift 5022997
  have htrace : WordTrace (prefixWord ++ tailWord_5022997) baseStart_5022997 baseEnd_5022997 := by
    simpa [prefixWord, tailWord_5022997, baseEnd_5022997] using wordTrace_append hprefix tailTrace_5022997
  have hstable : (prefixWord ++ tailWord_5022997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5022997).length < 2 ^ (prefixWord ++ tailWord_5022997).sum := by decide
  have hdescent : baseEnd_5022997 < baseStart_5022997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5022997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023011 : List Nat := [1, 1, 1, 4, 2, 3, 1, 1, 5, 2, 2]
def baseStart_5023011 : Nat := 118140960795 + 5023011 * 2 ^ 59
def prefixEnd_5023011 : Nat := 4983230072969 + 3 ^ 40 * 5023011 * 2
def baseEnd_5023011 : Nat := 2579218975821152180062099

theorem tailTrace_5023011 : CollatzResearch.WordTrace tailWord_5023011 prefixEnd_5023011 2579218975821152180062099 := by
  unfold tailWord_5023011
  simp only [CollatzResearch.WordTrace]
  refine ⟨183204262005496483826028887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122136174670330989217352591 183204262005496483826028887)
  ·
    refine ⟨274806393008244725739043331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183204262005496483826028887 274806393008244725739043331)
    ·
      refine ⟨412209589512367088608564997, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274806393008244725739043331 412209589512367088608564997)
      ·
        refine ⟨77289298033568829114105937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 412209589512367088608564997 77289298033568829114105937)
        ·
          refine ⟨57966973525176621835579453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77289298033568829114105937 57966973525176621835579453)
          ·
            refine ⟨21737615071941233188342295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57966973525176621835579453 21737615071941233188342295)
            ·
              refine ⟨32606422607911849782513443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21737615071941233188342295 32606422607911849782513443)
              ·
                refine ⟨48909633911867774673770165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32606422607911849782513443 48909633911867774673770165)
                ·
                  refine ⟨4585278179237603875665953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48909633911867774673770165 4585278179237603875665953)
                  ·
                    refine ⟨3438958634428202906749465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4585278179237603875665953 3438958634428202906749465)
                    ·
                      refine ⟨2579218975821152180062099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3438958634428202906749465 2579218975821152180062099)
                      ·
                        rfl

theorem cell23_5023011_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 1, 1, 5, 2, 2].length) (baseStart_5023011 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023011 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023011 prefixEnd_5023011 := by exact prefixLift 5023011
  have htrace : WordTrace (prefixWord ++ tailWord_5023011) baseStart_5023011 baseEnd_5023011 := by
    simpa [prefixWord, tailWord_5023011, baseEnd_5023011] using wordTrace_append hprefix tailTrace_5023011
  have hstable : (prefixWord ++ tailWord_5023011).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023011).length < 2 ^ (prefixWord ++ tailWord_5023011).sum := by decide
  have hdescent : baseEnd_5023011 < baseStart_5023011 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023011) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023021 : List Nat := [1, 5, 3, 1, 1, 1, 2, 2, 1, 6]
def baseStart_5023021 : Nat := 118140960795 + 5023021 * 2 ^ 59
def prefixEnd_5023021 : Nat := 4983230072969 + 3 ^ 40 * 5023021 * 2
def baseEnd_5023021 : Nat := 859741370209232380312351

theorem tailTrace_5023021 : CollatzResearch.WordTrace tailWord_5023021 prefixEnd_5023021 859741370209232380312351 := by
  unfold tailWord_5023021
  simp only [CollatzResearch.WordTrace]
  refine ⟨183204626735460255533892917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122136417823640170355928611 183204626735460255533892917)
  ·
    refine ⟨17175433756449398956302461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 183204626735460255533892917 17175433756449398956302461)
    ·
      refine ⟨6440787658668524608613423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17175433756449398956302461 6440787658668524608613423)
      ·
        refine ⟨9661181488002786912920135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6440787658668524608613423 9661181488002786912920135)
        ·
          refine ⟨14491772232004180369380203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9661181488002786912920135 14491772232004180369380203)
          ·
            refine ⟨21737658348006270554070305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14491772232004180369380203 21737658348006270554070305)
            ·
              refine ⟨16303243761004702915552729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21737658348006270554070305 16303243761004702915552729)
              ·
                refine ⟨12227432820753527186664547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16303243761004702915552729 12227432820753527186664547)
                ·
                  refine ⟨18341149231130290779996821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12227432820753527186664547 18341149231130290779996821)
                  ·
                    refine ⟨859741370209232380312351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 18341149231130290779996821 859741370209232380312351)
                    ·
                      rfl

theorem cell23_5023021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 1, 2, 2, 1, 6].length) (baseStart_5023021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023021 prefixEnd_5023021 := by exact prefixLift 5023021
  have htrace : WordTrace (prefixWord ++ tailWord_5023021) baseStart_5023021 baseEnd_5023021 := by
    simpa [prefixWord, tailWord_5023021, baseEnd_5023021] using wordTrace_append hprefix tailTrace_5023021
  have hstable : (prefixWord ++ tailWord_5023021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023021).length < 2 ^ (prefixWord ++ tailWord_5023021).sum := by decide
  have hdescent : baseEnd_5023021 < baseStart_5023021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023028 : List Nat := [2, 5, 1, 1, 1, 1, 1, 2, 5, 2, 2]
def baseStart_5023028 : Nat := 118140960795 + 5023028 * 2 ^ 59
def prefixEnd_5023028 : Nat := 4983230072969 + 3 ^ 40 * 5023028 * 2
def baseEnd_5023028 : Nat := 2579227704992278613549521

theorem tailTrace_5023028 : CollatzResearch.WordTrace tailWord_5023028 prefixEnd_5023028 2579227704992278613549521 := by
  unfold tailWord_5023028
  simp only [CollatzResearch.WordTrace]
  refine ⟨91602441023217447864698869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122136588030956597152931825 91602441023217447864698869)
  ·
    refine ⟨8587728845926635737315519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 91602441023217447864698869 8587728845926635737315519)
    ·
      refine ⟨12881593268889953605973279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8587728845926635737315519 12881593268889953605973279)
      ·
        refine ⟨19322389903334930408959919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12881593268889953605973279 19322389903334930408959919)
        ·
          refine ⟨28983584855002395613439879, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19322389903334930408959919 28983584855002395613439879)
          ·
            refine ⟨43475377282503593420159819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28983584855002395613439879 43475377282503593420159819)
            ·
              refine ⟨65213065923755390130239729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43475377282503593420159819 65213065923755390130239729)
              ·
                refine ⟨48909799442816542597679797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65213065923755390130239729 48909799442816542597679797)
                ·
                  refine ⟨4585293697764050868532481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48909799442816542597679797 4585293697764050868532481)
                  ·
                    refine ⟨3438970273323038151399361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4585293697764050868532481 3438970273323038151399361)
                    ·
                      refine ⟨2579227704992278613549521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3438970273323038151399361 2579227704992278613549521)
                      ·
                        rfl

theorem cell23_5023028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 1, 2, 5, 2, 2].length) (baseStart_5023028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023028 prefixEnd_5023028 := by exact prefixLift 5023028
  have htrace : WordTrace (prefixWord ++ tailWord_5023028) baseStart_5023028 baseEnd_5023028 := by
    simpa [prefixWord, tailWord_5023028, baseEnd_5023028] using wordTrace_append hprefix tailTrace_5023028
  have hstable : (prefixWord ++ tailWord_5023028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023028).length < 2 ^ (prefixWord ++ tailWord_5023028).sum := by decide
  have hdescent : baseEnd_5023028 < baseStart_5023028 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023061 : List Nat := [1, 3, 2, 2, 3, 1, 3, 1, 1, 3, 3]
def baseStart_5023061 : Nat := 118140960795 + 5023061 * 2 ^ 59
def prefixEnd_5023061 : Nat := 4983230072969 + 3 ^ 40 * 5023061 * 2
def baseEnd_5023061 : Nat := 2579244649853876984436869

theorem tailTrace_5023061 : CollatzResearch.WordTrace tailWord_5023061 prefixEnd_5023061 2579244649853876984436869 := by
  unfold tailWord_5023061
  simp only [CollatzResearch.WordTrace]
  refine ⟨183206085655315342365349037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122137390436876894910232691 183206085655315342365349037)
  ·
    refine ⟨68702282120743253387005889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183206085655315342365349037 68702282120743253387005889)
    ·
      refine ⟨51526711590557440040254417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68702282120743253387005889 51526711590557440040254417)
      ·
        refine ⟨38645033692918080030190813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51526711590557440040254417 38645033692918080030190813)
        ·
          refine ⟨14491887634844280011321555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38645033692918080030190813 14491887634844280011321555)
          ·
            refine ⟨21737831452266420016982333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14491887634844280011321555 21737831452266420016982333)
            ·
              refine ⟨8151686794599907506368375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21737831452266420016982333 8151686794599907506368375)
              ·
                refine ⟨12227530191899861259552563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8151686794599907506368375 12227530191899861259552563)
                ·
                  refine ⟨18341295287849791889328845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12227530191899861259552563 18341295287849791889328845)
                  ·
                    refine ⟨6877985732943671958498317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18341295287849791889328845 6877985732943671958498317)
                    ·
                      refine ⟨2579244649853876984436869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6877985732943671958498317 2579244649853876984436869)
                      ·
                        rfl

theorem cell23_5023061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_5023061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023061 prefixEnd_5023061 := by exact prefixLift 5023061
  have htrace : WordTrace (prefixWord ++ tailWord_5023061) baseStart_5023061 baseEnd_5023061 := by
    simpa [prefixWord, tailWord_5023061, baseEnd_5023061] using wordTrace_append hprefix tailTrace_5023061
  have hstable : (prefixWord ++ tailWord_5023061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023061).length < 2 ^ (prefixWord ++ tailWord_5023061).sum := by decide
  have hdescent : baseEnd_5023061 < baseStart_5023061 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023074 : List Nat := [3, 3, 2, 1, 1, 1, 1, 1, 1, 4, 5]
def baseStart_5023074 : Nat := 118140960795 + 5023074 * 2 ^ 59
def prefixEnd_5023074 : Nat := 4983230072969 + 3 ^ 40 * 5023074 * 2
def baseEnd_5023074 : Nat := 2579251325102385433574309

theorem tailTrace_5023074 : CollatzResearch.WordTrace tailWord_5023074 prefixEnd_5023074 2579251325102385433574309 := by
  unfold tailWord_5023074
  simp only [CollatzResearch.WordTrace]
  refine ⟨45801639951067061396393069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122137706536178830390381517 45801639951067061396393069)
  ·
    refine ⟨17175614981650148023647401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45801639951067061396393069 17175614981650148023647401)
    ·
      refine ⟨12881711236237611017735551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17175614981650148023647401 12881711236237611017735551)
      ·
        refine ⟨19322566854356416526603327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12881711236237611017735551 19322566854356416526603327)
        ·
          refine ⟨28983850281534624789904991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19322566854356416526603327 28983850281534624789904991)
          ·
            refine ⟨43475775422301937184857487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28983850281534624789904991 43475775422301937184857487)
            ·
              refine ⟨65213663133452905777286231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43475775422301937184857487 65213663133452905777286231)
              ·
                refine ⟨97820494700179358665929347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65213663133452905777286231 97820494700179358665929347)
                ·
                  refine ⟨146730742050269037998894021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97820494700179358665929347 146730742050269037998894021)
                  ·
                    refine ⟨27512014134425444624792629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 146730742050269037998894021 27512014134425444624792629)
                    ·
                      refine ⟨2579251325102385433574309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27512014134425444624792629 2579251325102385433574309)
                      ·
                        rfl

theorem cell23_5023074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_5023074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023074 prefixEnd_5023074 := by exact prefixLift 5023074
  have htrace : WordTrace (prefixWord ++ tailWord_5023074) baseStart_5023074 baseEnd_5023074 := by
    simpa [prefixWord, tailWord_5023074, baseEnd_5023074] using wordTrace_append hprefix tailTrace_5023074
  have hstable : (prefixWord ++ tailWord_5023074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023074).length < 2 ^ (prefixWord ++ tailWord_5023074).sum := by decide
  have hdescent : baseEnd_5023074 < baseStart_5023074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023079 : List Nat := [1, 1, 5, 1, 5, 1, 1, 3, 1, 2, 2]
def baseStart_5023079 : Nat := 118140960795 + 5023079 * 2 ^ 59
def prefixEnd_5023079 : Nat := 4983230072969 + 3 ^ 40 * 5023079 * 2
def baseEnd_5023079 : Nat := 2579253892505657914011787

theorem tailTrace_5023079 : CollatzResearch.WordTrace tailWord_5023079 prefixEnd_5023079 2579253892505657914011787 := by
  unfold tailWord_5023079
  simp only [CollatzResearch.WordTrace]
  refine ⟨183206742169250131439504291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122137828112833420959669527 183206742169250131439504291)
  ·
    refine ⟨274810113253875197159256437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183206742169250131439504291 274810113253875197159256437)
    ·
      refine ⟨25763448117550799733680291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 274810113253875197159256437 25763448117550799733680291)
      ·
        refine ⟨38645172176326199600520437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25763448117550799733680291 38645172176326199600520437)
        ·
          refine ⟨3622984891530581212548791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38645172176326199600520437 3622984891530581212548791)
          ·
            refine ⟨5434477337295871818823187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3622984891530581212548791 5434477337295871818823187)
            ·
              refine ⟨8151716005943807728234781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5434477337295871818823187 8151716005943807728234781)
              ·
                refine ⟨3056893502228927898088043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8151716005943807728234781 3056893502228927898088043)
                ·
                  refine ⟨4585340253343391847132065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3056893502228927898088043 4585340253343391847132065)
                  ·
                    refine ⟨3439005190007543885349049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4585340253343391847132065 3439005190007543885349049)
                    ·
                      refine ⟨2579253892505657914011787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3439005190007543885349049 2579253892505657914011787)
                      ·
                        rfl

theorem cell23_5023079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 1, 3, 1, 2, 2].length) (baseStart_5023079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023079 prefixEnd_5023079 := by exact prefixLift 5023079
  have htrace : WordTrace (prefixWord ++ tailWord_5023079) baseStart_5023079 baseEnd_5023079 := by
    simpa [prefixWord, tailWord_5023079, baseEnd_5023079] using wordTrace_append hprefix tailTrace_5023079
  have hstable : (prefixWord ++ tailWord_5023079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023079).length < 2 ^ (prefixWord ++ tailWord_5023079).sum := by decide
  have hdescent : baseEnd_5023079 < baseStart_5023079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023154 : List Nat := [3, 2, 1, 1, 1, 1, 2, 3, 4, 5]
def baseStart_5023154 : Nat := 118140960795 + 5023154 * 2 ^ 59
def prefixEnd_5023154 : Nat := 4983230072969 + 3 ^ 40 * 5023154 * 2
def baseEnd_5023154 : Nat := 859764134518248373524647

theorem tailTrace_5023154 : CollatzResearch.WordTrace tailWord_5023154 prefixEnd_5023154 859764134518248373524647 := by
  unfold tailWord_5023154
  simp only [CollatzResearch.WordTrace]
  refine ⟨45802369410994604812121129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122139651762652279498989677 45802369410994604812121129)
  ·
    refine ⟨34351777058245953609090847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45802369410994604812121129 34351777058245953609090847)
    ·
      refine ⟨51527665587368930413636271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34351777058245953609090847 51527665587368930413636271)
      ·
        refine ⟨77291498381053395620454407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51527665587368930413636271 77291498381053395620454407)
        ·
          refine ⟨115937247571580093430681611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77291498381053395620454407 115937247571580093430681611)
          ·
            refine ⟨173905871357370140146022417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115937247571580093430681611 173905871357370140146022417)
            ·
              refine ⟨130429403518027605109516813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 173905871357370140146022417 130429403518027605109516813)
              ·
                refine ⟨48911026319260351916068805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130429403518027605109516813 48911026319260351916068805)
                ·
                  refine ⟨9170817434861315984262901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48911026319260351916068805 9170817434861315984262901)
                  ·
                    refine ⟨859764134518248373524647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9170817434861315984262901 859764134518248373524647)
                    ·
                      rfl

theorem cell23_5023154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 3, 4, 5].length) (baseStart_5023154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023154 prefixEnd_5023154 := by exact prefixLift 5023154
  have htrace : WordTrace (prefixWord ++ tailWord_5023154) baseStart_5023154 baseEnd_5023154 := by
    simpa [prefixWord, tailWord_5023154, baseEnd_5023154] using wordTrace_append hprefix tailTrace_5023154
  have hstable : (prefixWord ++ tailWord_5023154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023154).length < 2 ^ (prefixWord ++ tailWord_5023154).sum := by decide
  have hdescent : baseEnd_5023154 < baseStart_5023154 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023204 : List Nat := [2, 3, 1, 1, 1, 1, 1, 2, 1, 6, 4]
def baseStart_5023204 : Nat := 118140960795 + 5023204 * 2 ^ 59
def prefixEnd_5023204 : Nat := 4983230072969 + 3 ^ 40 * 5023204 * 2
def baseEnd_5023204 : Nat := 2579318077587469924948711

theorem tailTrace_5023204 : CollatzResearch.WordTrace tailWord_5023204 prefixEnd_5023204 2579318077587469924948711 := by
  unfold tailWord_5023204
  simp only [CollatzResearch.WordTrace]
  refine ⟨91605650646898638893902333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122140867529198185191869777 91605650646898638893902333)
  ·
    refine ⟨34352118992586989585213375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91605650646898638893902333 34352118992586989585213375)
    ·
      refine ⟨51528178488880484377820063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34352118992586989585213375 51528178488880484377820063)
      ·
        refine ⟨77292267733320726566730095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51528178488880484377820063 77292267733320726566730095)
        ·
          refine ⟨115938401599981089850095143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77292267733320726566730095 115938401599981089850095143)
          ·
            refine ⟨173907602399971634775142715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115938401599981089850095143 173907602399971634775142715)
            ·
              refine ⟨260861403599957452162714073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173907602399971634775142715 260861403599957452162714073)
              ·
                refine ⟨195646052699968089122035555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 260861403599957452162714073 195646052699968089122035555)
                ·
                  refine ⟨293469079049952133683053333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 195646052699968089122035555 293469079049952133683053333)
                  ·
                    refine ⟨13756363080466506266393125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 293469079049952133683053333 13756363080466506266393125)
                    ·
                      refine ⟨2579318077587469924948711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13756363080466506266393125 2579318077587469924948711)
                      ·
                        rfl

theorem cell23_5023204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 2, 1, 6, 4].length) (baseStart_5023204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023204 prefixEnd_5023204 := by exact prefixLift 5023204
  have htrace : WordTrace (prefixWord ++ tailWord_5023204) baseStart_5023204 baseEnd_5023204 := by
    simpa [prefixWord, tailWord_5023204, baseEnd_5023204] using wordTrace_append hprefix tailTrace_5023204
  have hstable : (prefixWord ++ tailWord_5023204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023204).length < 2 ^ (prefixWord ++ tailWord_5023204).sum := by decide
  have hdescent : baseEnd_5023204 < baseStart_5023204 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023218 : List Nat := [3, 2, 1, 4, 1, 1, 1, 3, 3, 4]
def baseStart_5023218 : Nat := 118140960795 + 5023218 * 2 ^ 59
def prefixEnd_5023218 : Nat := 4983230072969 + 3 ^ 40 * 5023218 * 2
def baseEnd_5023218 : Nat := 859775088772210956724549

theorem tailTrace_5023218 : CollatzResearch.WordTrace tailWord_5023218 prefixEnd_5023218 859775088772210956724549 := by
  unfold tailWord_5023218
  simp only [CollatzResearch.WordTrace]
  refine ⟨45802952978936639544703577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122141207943831038785876205 45802952978936639544703577)
  ·
    refine ⟨34352214734202479658527683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45802952978936639544703577 34352214734202479658527683)
    ·
      refine ⟨51528322101303719487791525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34352214734202479658527683 51528322101303719487791525)
      ·
        refine ⟨9661560393994447403960911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51528322101303719487791525 9661560393994447403960911)
        ·
          refine ⟨14492340590991671105941367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9661560393994447403960911 14492340590991671105941367)
          ·
            refine ⟨21738510886487506658912051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14492340590991671105941367 21738510886487506658912051)
            ·
              refine ⟨32607766329731259988368077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21738510886487506658912051 32607766329731259988368077)
              ·
                refine ⟨12227912373649222495638029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32607766329731259988368077 12227912373649222495638029)
                ·
                  refine ⟨4585467140118458435864261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12227912373649222495638029 4585467140118458435864261)
                  ·
                    refine ⟨859775088772210956724549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4585467140118458435864261 859775088772210956724549)
                    ·
                      rfl

theorem cell23_5023218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 1, 3, 3, 4].length) (baseStart_5023218 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023218 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023218 prefixEnd_5023218 := by exact prefixLift 5023218
  have htrace : WordTrace (prefixWord ++ tailWord_5023218) baseStart_5023218 baseEnd_5023218 := by
    simpa [prefixWord, tailWord_5023218, baseEnd_5023218] using wordTrace_append hprefix tailTrace_5023218
  have hstable : (prefixWord ++ tailWord_5023218).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023218).length < 2 ^ (prefixWord ++ tailWord_5023218).sum := by decide
  have hdescent : baseEnd_5023218 < baseStart_5023218 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023281 : List Nat := [1, 2, 2, 3, 1, 1, 1, 4, 3, 1, 4]
def baseStart_5023281 : Nat := 118140960795 + 5023281 * 2 ^ 59
def prefixEnd_5023281 : Nat := 4983230072969 + 3 ^ 40 * 5023281 * 2
def baseEnd_5023281 : Nat := 2579357615597866123685857

theorem tailTrace_5023281 : CollatzResearch.WordTrace tailWord_5023281 prefixEnd_5023281 2579357615597866123685857 := by
  unfold tailWord_5023281
  simp only [CollatzResearch.WordTrace]
  refine ⟨183214109714518319938357697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122142739809678879958905131 183214109714518319938357697)
  ·
    refine ⟨137410582285888739953768273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183214109714518319938357697 137410582285888739953768273)
    ·
      refine ⟨103057936714416554965326205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137410582285888739953768273 103057936714416554965326205)
      ·
        refine ⟨38646726267906208111997327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103057936714416554965326205 38646726267906208111997327)
        ·
          refine ⟨57970089401859312167995991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38646726267906208111997327 57970089401859312167995991)
          ·
            refine ⟨86955134102788968251993987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57970089401859312167995991 86955134102788968251993987)
            ·
              refine ⟨130432701154183452377990981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86955134102788968251993987 130432701154183452377990981)
              ·
                refine ⟨24456131466409397320873309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 130432701154183452377990981 24456131466409397320873309)
                ·
                  refine ⟨9171049299903523995327491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24456131466409397320873309 9171049299903523995327491)
                  ·
                    refine ⟨13756573949855285992991237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9171049299903523995327491 13756573949855285992991237)
                    ·
                      refine ⟨2579357615597866123685857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13756573949855285992991237 2579357615597866123685857)
                      ·
                        rfl

theorem cell23_5023281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 1, 4, 3, 1, 4].length) (baseStart_5023281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023281 prefixEnd_5023281 := by exact prefixLift 5023281
  have htrace : WordTrace (prefixWord ++ tailWord_5023281) baseStart_5023281 baseEnd_5023281 := by
    simpa [prefixWord, tailWord_5023281, baseEnd_5023281] using wordTrace_append hprefix tailTrace_5023281
  have hstable : (prefixWord ++ tailWord_5023281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023281).length < 2 ^ (prefixWord ++ tailWord_5023281).sum := by decide
  have hdescent : baseEnd_5023281 < baseStart_5023281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023338 : List Nat := [3, 1, 3, 2, 1, 4, 1, 8]
def baseStart_5023338 : Nat := 118140960795 + 5023338 * 2 ^ 59
def prefixEnd_5023338 : Nat := 4983230072969 + 3 ^ 40 * 5023338 * 2
def baseEnd_5023338 : Nat := 95532847555376755580485

theorem tailTrace_5023338 : CollatzResearch.WordTrace tailWord_5023338 prefixEnd_5023338 95532847555376755580485 := by
  unfold tailWord_5023338
  simp only [CollatzResearch.WordTrace]
  refine ⟨45804047168827954668295667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122144125783541212448788445 45804047168827954668295667)
  ·
    refine ⟨68706070753241932002443501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45804047168827954668295667 68706070753241932002443501)
    ·
      refine ⟨25764776532465724500916313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68706070753241932002443501 25764776532465724500916313)
      ·
        refine ⟨19323582399349293375687235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25764776532465724500916313 19323582399349293375687235)
        ·
          refine ⟨28985373599023940063530853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19323582399349293375687235 28985373599023940063530853)
          ·
            refine ⟨5434757549816988761912035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28985373599023940063530853 5434757549816988761912035)
            ·
              refine ⟨8152136324725483142868053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5434757549816988761912035 8152136324725483142868053)
              ·
                refine ⟨95532847555376755580485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 8152136324725483142868053 95532847555376755580485)
                ·
                  rfl

theorem cell23_5023338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 1, 8].length) (baseStart_5023338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023338 prefixEnd_5023338 := by exact prefixLift 5023338
  have htrace : WordTrace (prefixWord ++ tailWord_5023338) baseStart_5023338 baseEnd_5023338 := by
    simpa [prefixWord, tailWord_5023338, baseEnd_5023338] using wordTrace_append hprefix tailTrace_5023338
  have hstable : (prefixWord ++ tailWord_5023338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023338).length < 2 ^ (prefixWord ++ tailWord_5023338).sum := by decide
  have hdescent : baseEnd_5023338 < baseStart_5023338 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023401 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 6, 2, 4]
def baseStart_5023401 : Nat := 118140960795 + 5023401 * 2 ^ 59
def prefixEnd_5023401 : Nat := 4983230072969 + 3 ^ 40 * 5023401 * 2
def baseEnd_5023401 : Nat := 2579419233276405654185305

theorem tailTrace_5023401 : CollatzResearch.WordTrace tailWord_5023401 prefixEnd_5023401 2579419233276405654185305 := by
  unfold tailWord_5023401
  simp only [CollatzResearch.WordTrace]
  refine ⟨183218486474083580432726057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122145657649389053621817371 183218486474083580432726057)
  ·
    refine ⟨137413864855562685324544543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183218486474083580432726057 137413864855562685324544543)
    ·
      refine ⟨206120797283344027986816815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137413864855562685324544543 206120797283344027986816815)
      ·
        refine ⟨309181195925016041980225223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206120797283344027986816815 309181195925016041980225223)
        ·
          refine ⟨463771793887524062970337835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309181195925016041980225223 463771793887524062970337835)
          ·
            refine ⟨695657690831286094455506753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 463771793887524062970337835 695657690831286094455506753)
            ·
              refine ⟨521743268123464570841630065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 695657690831286094455506753 521743268123464570841630065)
              ·
                refine ⟨391307451092598428131222549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 521743268123464570841630065 391307451092598428131222549)
                ·
                  refine ⟨18342536769965551318651057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 391307451092598428131222549 18342536769965551318651057)
                  ·
                    refine ⟨13756902577474163488988293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18342536769965551318651057 13756902577474163488988293)
                    ·
                      refine ⟨2579419233276405654185305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13756902577474163488988293 2579419233276405654185305)
                      ·
                        rfl

theorem cell23_5023401_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 6, 2, 4].length) (baseStart_5023401 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023401 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023401 prefixEnd_5023401 := by exact prefixLift 5023401
  have htrace : WordTrace (prefixWord ++ tailWord_5023401) baseStart_5023401 baseEnd_5023401 := by
    simpa [prefixWord, tailWord_5023401, baseEnd_5023401] using wordTrace_append hprefix tailTrace_5023401
  have hstable : (prefixWord ++ tailWord_5023401).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023401).length < 2 ^ (prefixWord ++ tailWord_5023401).sum := by decide
  have hdescent : baseEnd_5023401 < baseStart_5023401 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023401) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023411 : List Nat := [1, 1, 1, 2, 3, 3, 1, 4, 7]
def baseStart_5023411 : Nat := 118140960795 + 5023411 * 2 ^ 59
def prefixEnd_5023411 : Nat := 4983230072969 + 3 ^ 40 * 5023411 * 2
def baseEnd_5023411 : Nat := 286602707564772290562251

theorem tailTrace_5023411 : CollatzResearch.WordTrace tailWord_5023411 prefixEnd_5023411 286602707564772290562251 := by
  unfold tailWord_5023411
  simp only [CollatzResearch.WordTrace]
  refine ⟨183218851204047352140590087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122145900802698234760393391 183218851204047352140590087)
  ·
    refine ⟨274828276806071028210885131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183218851204047352140590087 274828276806071028210885131)
    ·
      refine ⟨412242415209106542316327697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274828276806071028210885131 412242415209106542316327697)
      ·
        refine ⟨309181811406829906737245773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412242415209106542316327697 309181811406829906737245773)
        ·
          refine ⟨115943179277561215026467165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 309181811406829906737245773 115943179277561215026467165)
          ·
            refine ⟨43478692229085455634925187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115943179277561215026467165 43478692229085455634925187)
            ·
              refine ⟨65218038343628183452387781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43478692229085455634925187 65218038343628183452387781)
              ·
                refine ⟨12228382189430284397322709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65218038343628183452387781 12228382189430284397322709)
                ·
                  refine ⟨286602707564772290562251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 12228382189430284397322709 286602707564772290562251)
                  ·
                    rfl

theorem cell23_5023411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 4, 7].length) (baseStart_5023411 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023411 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023411 prefixEnd_5023411 := by exact prefixLift 5023411
  have htrace : WordTrace (prefixWord ++ tailWord_5023411) baseStart_5023411 baseEnd_5023411 := by
    simpa [prefixWord, tailWord_5023411, baseEnd_5023411] using wordTrace_append hprefix tailTrace_5023411
  have hstable : (prefixWord ++ tailWord_5023411).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023411).length < 2 ^ (prefixWord ++ tailWord_5023411).sum := by decide
  have hdescent : baseEnd_5023411 < baseStart_5023411 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023422 : List Nat := [4, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2]
def baseStart_5023422 : Nat := 118140960795 + 5023422 * 2 ^ 59
def prefixEnd_5023422 : Nat := 4983230072969 + 3 ^ 40 * 5023422 * 2
def baseEnd_5023422 : Nat := 2579430016370150072022709

theorem tailTrace_5023422 : CollatzResearch.WordTrace tailWord_5023422 prefixEnd_5023422 2579430016370150072022709 := by
  unfold tailWord_5023422
  simp only [CollatzResearch.WordTrace]
  refine ⟨22902406550875937627405065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122146168271338334012827013 22902406550875937627405065)
  ·
    refine ⟨17176804913156953220553799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22902406550875937627405065 17176804913156953220553799)
    ·
      refine ⟨25765207369735429830830699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17176804913156953220553799 25765207369735429830830699)
      ·
        refine ⟨38647811054603144746246049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25765207369735429830830699 38647811054603144746246049)
        ·
          refine ⟨28985858290952358559684537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38647811054603144746246049 28985858290952358559684537)
          ·
            refine ⟨21739393718214268919763403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28985858290952358559684537 21739393718214268919763403)
            ·
              refine ⟨32609090577321403379645105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21739393718214268919763403 32609090577321403379645105)
              ·
                refine ⟨24456817932991052534733829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32609090577321403379645105 24456817932991052534733829)
                ·
                  refine ⟨4585653362435822350262593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24456817932991052534733829 4585653362435822350262593)
                  ·
                    refine ⟨3439240021826866762696945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4585653362435822350262593 3439240021826866762696945)
                    ·
                      refine ⟨2579430016370150072022709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3439240021826866762696945 2579430016370150072022709)
                      ·
                        rfl

theorem cell23_5023422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 1, 2, 4, 2, 2].length) (baseStart_5023422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023422 prefixEnd_5023422 := by exact prefixLift 5023422
  have htrace : WordTrace (prefixWord ++ tailWord_5023422) baseStart_5023422 baseEnd_5023422 := by
    simpa [prefixWord, tailWord_5023422, baseEnd_5023422] using wordTrace_append hprefix tailTrace_5023422
  have hstable : (prefixWord ++ tailWord_5023422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023422).length < 2 ^ (prefixWord ++ tailWord_5023422).sum := by decide
  have hdescent : baseEnd_5023422 < baseStart_5023422 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023481 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 1, 2, 9]
def baseStart_5023481 : Nat := 118140960795 + 5023481 * 2 ^ 59
def prefixEnd_5023481 : Nat := 4983230072969 + 3 ^ 40 * 5023481 * 2
def baseEnd_5023481 : Nat := 2579460311728765341184937

theorem tailTrace_5023481 : CollatzResearch.WordTrace tailWord_5023481 prefixEnd_5023481 2579460311728765341184937 := by
  unfold tailWord_5023481
  simp only [CollatzResearch.WordTrace]
  refine ⟨183221404313793754095638297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122147602875862502730425531 183221404313793754095638297)
  ·
    refine ⟨137416053235345315571728723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183221404313793754095638297 137416053235345315571728723)
    ·
      refine ⟨206124079853017973357593085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137416053235345315571728723 206124079853017973357593085)
      ·
        refine ⟨77296529944881740009097407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 206124079853017973357593085 77296529944881740009097407)
        ·
          refine ⟨115944794917322610013646111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77296529944881740009097407 115944794917322610013646111)
          ·
            refine ⟨173917192375983915020469167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115944794917322610013646111 173917192375983915020469167)
            ·
              refine ⟨260875788563975872530703751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173917192375983915020469167 260875788563975872530703751)
              ·
                refine ⟨391313682845963808796055627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260875788563975872530703751 391313682845963808796055627)
                ·
                  refine ⟨586970524268945713194083441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 391313682845963808796055627 586970524268945713194083441)
                  ·
                    refine ⟨440227893201709284895562581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 586970524268945713194083441 440227893201709284895562581)
                    ·
                      refine ⟨2579460311728765341184937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 440227893201709284895562581 2579460311728765341184937)
                      ·
                        rfl

theorem cell23_5023481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_5023481 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023481 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023481 prefixEnd_5023481 := by exact prefixLift 5023481
  have htrace : WordTrace (prefixWord ++ tailWord_5023481) baseStart_5023481 baseEnd_5023481 := by
    simpa [prefixWord, tailWord_5023481, baseEnd_5023481] using wordTrace_append hprefix tailTrace_5023481
  have hstable : (prefixWord ++ tailWord_5023481).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023481).length < 2 ^ (prefixWord ++ tailWord_5023481).sum := by decide
  have hdescent : baseEnd_5023481 < baseStart_5023481 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023488 : List Nat := [2, 1, 1, 2, 1, 1, 2, 4, 5, 4]
def baseStart_5023488 : Nat := 118140960795 + 5023488 * 2 ^ 59
def prefixEnd_5023488 : Nat := 4983230072969 + 3 ^ 40 * 5023488 * 2
def baseEnd_5023488 : Nat := 859821302031115604599135

theorem tailTrace_5023488 : CollatzResearch.WordTrace tailWord_5023488 prefixEnd_5023488 859821302031115604599135 := by
  unfold tailWord_5023488
  simp only [CollatzResearch.WordTrace]
  refine ⟨91610829812384197145571559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122147773083178929527428745 91610829812384197145571559)
  ·
    refine ⟨137416244718576295718357339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91610829812384197145571559 137416244718576295718357339)
    ·
      refine ⟨206124367077864443577536009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137416244718576295718357339 206124367077864443577536009)
      ·
        refine ⟨154593275308398332683152007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 206124367077864443577536009 154593275308398332683152007)
        ·
          refine ⟨231889912962597499024728011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154593275308398332683152007 231889912962597499024728011)
          ·
            refine ⟨347834869443896248537092017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231889912962597499024728011 347834869443896248537092017)
            ·
              refine ⟨260876152082922186402819013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 347834869443896248537092017 260876152082922186402819013)
              ·
                refine ⟨48914278515547909950528565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 260876152082922186402819013 48914278515547909950528565)
                ·
                  refine ⟨4585713610832616557862053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48914278515547909950528565 4585713610832616557862053)
                  ·
                    refine ⟨859821302031115604599135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4585713610832616557862053 859821302031115604599135)
                    ·
                      rfl

theorem cell23_5023488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 4, 5, 4].length) (baseStart_5023488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023488 prefixEnd_5023488 := by exact prefixLift 5023488
  have htrace : WordTrace (prefixWord ++ tailWord_5023488) baseStart_5023488 baseEnd_5023488 := by
    simpa [prefixWord, tailWord_5023488, baseEnd_5023488] using wordTrace_append hprefix tailTrace_5023488
  have hstable : (prefixWord ++ tailWord_5023488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023488).length < 2 ^ (prefixWord ++ tailWord_5023488).sum := by decide
  have hdescent : baseEnd_5023488 < baseStart_5023488 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023532 : List Nat := [2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 3]
def baseStart_5023532 : Nat := 118140960795 + 5023532 * 2 ^ 59
def prefixEnd_5023532 : Nat := 4983230072969 + 3 ^ 40 * 5023532 * 2
def baseEnd_5023532 : Nat := 2579486499242144641647203

theorem tailTrace_5023532 : CollatzResearch.WordTrace tailWord_5023532 prefixEnd_5023532 2579486499242144641647203 := by
  unfold tailWord_5023532
  simp only [CollatzResearch.WordTrace]
  refine ⟨91611632218304494902872425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122148842957739326537163233 91611632218304494902872425)
  ·
    refine ⟨68708724163728371177154319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91611632218304494902872425 68708724163728371177154319)
    ·
      refine ⟨103063086245592556765731479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68708724163728371177154319 103063086245592556765731479)
      ·
        refine ⟨154594629368388835148597219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103063086245592556765731479 154594629368388835148597219)
        ·
          refine ⟨231891944052583252722895829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154594629368388835148597219 231891944052583252722895829)
          ·
            refine ⟨5434967438732419985692871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 231891944052583252722895829 5434967438732419985692871)
            ·
              refine ⟨8152451158098629978539307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5434967438732419985692871 8152451158098629978539307)
              ·
                refine ⟨12228676737147944967808961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8152451158098629978539307 12228676737147944967808961)
                ·
                  refine ⟨9171507552860958725856721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12228676737147944967808961 9171507552860958725856721)
                  ·
                    refine ⟨6878630664645719044392541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9171507552860958725856721 6878630664645719044392541)
                    ·
                      refine ⟨2579486499242144641647203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6878630664645719044392541 2579486499242144641647203)
                      ·
                        rfl

theorem cell23_5023532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 2, 2, 3].length) (baseStart_5023532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023532 prefixEnd_5023532 := by exact prefixLift 5023532
  have htrace : WordTrace (prefixWord ++ tailWord_5023532) baseStart_5023532 baseEnd_5023532 := by
    simpa [prefixWord, tailWord_5023532, baseEnd_5023532] using wordTrace_append hprefix tailTrace_5023532
  have hstable : (prefixWord ++ tailWord_5023532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023532).length < 2 ^ (prefixWord ++ tailWord_5023532).sum := by decide
  have hdescent : baseEnd_5023532 < baseStart_5023532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023539 : List Nat := [1, 1, 1, 2, 7, 1, 2, 3, 1, 4]
def baseStart_5023539 : Nat := 118140960795 + 5023539 * 2 ^ 59
def prefixEnd_5023539 : Nat := 4983230072969 + 3 ^ 40 * 5023539 * 2
def baseEnd_5023539 : Nat := 859830031202242038086557

theorem tailTrace_5023539 : CollatzResearch.WordTrace tailWord_5023539 prefixEnd_5023539 859830031202242038086557 := by
  unfold tailWord_5023539
  simp only [CollatzResearch.WordTrace]
  refine ⟨183223519747583630001249671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122149013165055753334166447 183223519747583630001249671)
  ·
    refine ⟨274835279621375445001874507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183223519747583630001249671 274835279621375445001874507)
    ·
      refine ⟨412252919432063167502811761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274835279621375445001874507 412252919432063167502811761)
      ·
        refine ⟨309189689574047375627108821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412252919432063167502811761 309189689574047375627108821)
        ·
          refine ⟨7246633349391735366260363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 309189689574047375627108821 7246633349391735366260363)
          ·
            refine ⟨10869950024087603049390545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7246633349391735366260363 10869950024087603049390545)
            ·
              refine ⟨8152462518065702287042909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10869950024087603049390545 8152462518065702287042909)
              ·
                refine ⟨3057173444274638357641091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8152462518065702287042909 3057173444274638357641091)
                ·
                  refine ⟨4585760166411957536461637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3057173444274638357641091 4585760166411957536461637)
                  ·
                    refine ⟨859830031202242038086557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4585760166411957536461637 859830031202242038086557)
                    ·
                      rfl

theorem cell23_5023539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 7, 1, 2, 3, 1, 4].length) (baseStart_5023539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023539 prefixEnd_5023539 := by exact prefixLift 5023539
  have htrace : WordTrace (prefixWord ++ tailWord_5023539) baseStart_5023539 baseEnd_5023539 := by
    simpa [prefixWord, tailWord_5023539, baseEnd_5023539] using wordTrace_append hprefix tailTrace_5023539
  have hstable : (prefixWord ++ tailWord_5023539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023539).length < 2 ^ (prefixWord ++ tailWord_5023539).sum := by decide
  have hdescent : baseEnd_5023539 < baseStart_5023539 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023562 : List Nat := [3, 1, 2, 1, 1, 1, 6, 1, 3, 1, 3]
def baseStart_5023562 : Nat := 118140960795 + 5023562 * 2 ^ 59
def prefixEnd_5023562 : Nat := 4983230072969 + 3 ^ 40 * 5023562 * 2
def baseEnd_5023562 : Nat := 2579501903661779524272065

theorem tailTrace_5023562 : CollatzResearch.WordTrace tailWord_5023562 prefixEnd_5023562 2579501903661779524272065 := by
  unfold tailWord_5023562
  simp only [CollatzResearch.WordTrace]
  refine ⟨45806089656625076232334235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122149572417666869952891293 45806089656625076232334235)
  ·
    refine ⟨68709134484937614348501353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45806089656625076232334235 68709134484937614348501353)
    ·
      refine ⟨51531850863703210761376015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68709134484937614348501353 51531850863703210761376015)
      ·
        refine ⟨77297776295554816142064023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51531850863703210761376015 77297776295554816142064023)
        ·
          refine ⟨115946664443332224213096035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77297776295554816142064023 115946664443332224213096035)
          ·
            refine ⟨173919996664998336319644053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115946664443332224213096035 173919996664998336319644053)
            ·
              refine ⟨8152499843671797014983315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 173919996664998336319644053 8152499843671797014983315)
              ·
                refine ⟨12228749765507695522474973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8152499843671797014983315 12228749765507695522474973)
                ·
                  refine ⟨4585781162065385820928115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12228749765507695522474973 4585781162065385820928115)
                  ·
                    refine ⟨6878671743098078731392173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4585781162065385820928115 6878671743098078731392173)
                    ·
                      refine ⟨2579501903661779524272065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6878671743098078731392173 2579501903661779524272065)
                      ·
                        rfl

theorem cell23_5023562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 6, 1, 3, 1, 3].length) (baseStart_5023562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023562 prefixEnd_5023562 := by exact prefixLift 5023562
  have htrace : WordTrace (prefixWord ++ tailWord_5023562) baseStart_5023562 baseEnd_5023562 := by
    simpa [prefixWord, tailWord_5023562, baseEnd_5023562] using wordTrace_append hprefix tailTrace_5023562
  have hstable : (prefixWord ++ tailWord_5023562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023562).length < 2 ^ (prefixWord ++ tailWord_5023562).sum := by decide
  have hdescent : baseEnd_5023562 < baseStart_5023562 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023572 : List Nat := [2, 4, 1, 1, 3, 1, 1, 2, 1, 5, 2]
def baseStart_5023572 : Nat := 118140960795 + 5023572 * 2 ^ 59
def prefixEnd_5023572 : Nat := 4983230072969 + 3 ^ 40 * 5023572 * 2
def baseEnd_5023572 : Nat := 2579507038468324485147019

theorem tailTrace_5023572 : CollatzResearch.WordTrace tailWord_5023572 prefixEnd_5023572 2579507038468324485147019 := by
  unfold tailWord_5023572
  simp only [CollatzResearch.WordTrace]
  refine ⟨91612361678232038318600485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122149815570976051091467313 91612361678232038318600485)
  ·
    refine ⟨17177317814668507184737591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 91612361678232038318600485 17177317814668507184737591)
    ·
      refine ⟨25765976722002760777106387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17177317814668507184737591 25765976722002760777106387)
      ·
        refine ⟨38648965083004141165659581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25765976722002760777106387 38648965083004141165659581)
        ·
          refine ⟨14493361906126552937122343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38648965083004141165659581 14493361906126552937122343)
          ·
            refine ⟨21740042859189829405683515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14493361906126552937122343 21740042859189829405683515)
            ·
              refine ⟨32610064288784744108525273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21740042859189829405683515 32610064288784744108525273)
              ·
                refine ⟨24457548216588558081393955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32610064288784744108525273 24457548216588558081393955)
                ·
                  refine ⟨36686322324882837122090933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24457548216588558081393955 36686322324882837122090933)
                  ·
                    refine ⟨3439342717957765980196025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 36686322324882837122090933 3439342717957765980196025)
                    ·
                      refine ⟨2579507038468324485147019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3439342717957765980196025 2579507038468324485147019)
                      ·
                        rfl

theorem cell23_5023572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 1, 2, 1, 5, 2].length) (baseStart_5023572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023572 prefixEnd_5023572 := by exact prefixLift 5023572
  have htrace : WordTrace (prefixWord ++ tailWord_5023572) baseStart_5023572 baseEnd_5023572 := by
    simpa [prefixWord, tailWord_5023572, baseEnd_5023572] using wordTrace_append hprefix tailTrace_5023572
  have hstable : (prefixWord ++ tailWord_5023572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023572).length < 2 ^ (prefixWord ++ tailWord_5023572).sum := by decide
  have hdescent : baseEnd_5023572 < baseStart_5023572 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023585 : List Nat := [1, 2, 3, 1, 1, 1, 3, 1, 2, 6, 2]
def baseStart_5023585 : Nat := 118140960795 + 5023585 * 2 ^ 59
def prefixEnd_5023585 : Nat := 4983230072969 + 3 ^ 40 * 5023585 * 2
def baseEnd_5023585 : Nat := 2579513713716832934284459

theorem tailTrace_5023585 : CollatzResearch.WordTrace tailWord_5023585 prefixEnd_5023585 2579513713716832934284459 := by
  unfold tailWord_5023585
  simp only [CollatzResearch.WordTrace]
  refine ⟨183225197505416979857424209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122150131670277986571616139 183225197505416979857424209)
  ·
    refine ⟨137418898129062734893068157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183225197505416979857424209 137418898129062734893068157)
    ·
      refine ⟨51532086798398525584900559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137418898129062734893068157 51532086798398525584900559)
      ·
        refine ⟨77298130197597788377350839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51532086798398525584900559 77298130197597788377350839)
        ·
          refine ⟨115947195296396682566026259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77298130197597788377350839 115947195296396682566026259)
          ·
            refine ⟨173920792944595023849039389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115947195296396682566026259 173920792944595023849039389)
            ·
              refine ⟨65220297354223133943389771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 173920792944595023849039389 65220297354223133943389771)
              ·
                refine ⟨97830446031334700915084657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65220297354223133943389771 97830446031334700915084657)
                ·
                  refine ⟨73372834523501025686313493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97830446031334700915084657 73372834523501025686313493)
                  ·
                    refine ⟨3439351618289110579045945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73372834523501025686313493 3439351618289110579045945)
                    ·
                      refine ⟨2579513713716832934284459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3439351618289110579045945 2579513713716832934284459)
                      ·
                        rfl

theorem cell23_5023585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 1, 2, 6, 2].length) (baseStart_5023585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023585 prefixEnd_5023585 := by exact prefixLift 5023585
  have htrace : WordTrace (prefixWord ++ tailWord_5023585) baseStart_5023585 baseEnd_5023585 := by
    simpa [prefixWord, tailWord_5023585, baseEnd_5023585] using wordTrace_append hprefix tailTrace_5023585
  have hstable : (prefixWord ++ tailWord_5023585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023585).length < 2 ^ (prefixWord ++ tailWord_5023585).sum := by decide
  have hdescent : baseEnd_5023585 < baseStart_5023585 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023596 : List Nat := [2, 2, 1, 1, 4, 4, 1, 3, 1, 1, 3]
def baseStart_5023596 : Nat := 118140960795 + 5023596 * 2 ^ 59
def prefixEnd_5023596 : Nat := 4983230072969 + 3 ^ 40 * 5023596 * 2
def baseEnd_5023596 : Nat := 2579519362004032391246909

theorem tailTrace_5023596 : CollatzResearch.WordTrace tailWord_5023596 prefixEnd_5023596 2579519362004032391246909 := by
  unfold tailWord_5023596
  simp only [CollatzResearch.WordTrace]
  refine ⟨91612799354188564368037321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122150399138918085824049761 91612799354188564368037321)
  ·
    refine ⟨68709599515641423276027991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91612799354188564368037321 68709599515641423276027991)
    ·
      refine ⟨103064399273462134914041987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68709599515641423276027991 103064399273462134914041987)
      ·
        refine ⟨154596598910193202371062981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103064399273462134914041987 154596598910193202371062981)
        ·
          refine ⟨28986862295661225444574309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154596598910193202371062981 28986862295661225444574309)
          ·
            refine ⟨5435036680436479770857683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28986862295661225444574309 5435036680436479770857683)
            ·
              refine ⟨8152555020654719656286525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5435036680436479770857683 8152555020654719656286525)
              ·
                refine ⟨3057208132745519871107447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8152555020654719656286525 3057208132745519871107447)
                ·
                  refine ⟨4585812199118279806661171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3057208132745519871107447 4585812199118279806661171)
                  ·
                    refine ⟨6878718298677419709991757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4585812199118279806661171 6878718298677419709991757)
                    ·
                      refine ⟨2579519362004032391246909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6878718298677419709991757 2579519362004032391246909)
                      ·
                        rfl

theorem cell23_5023596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 4, 1, 3, 1, 1, 3].length) (baseStart_5023596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023596 prefixEnd_5023596 := by exact prefixLift 5023596
  have htrace : WordTrace (prefixWord ++ tailWord_5023596) baseStart_5023596 baseEnd_5023596 := by
    simpa [prefixWord, tailWord_5023596, baseEnd_5023596] using wordTrace_append hprefix tailTrace_5023596
  have hstable : (prefixWord ++ tailWord_5023596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023596).length < 2 ^ (prefixWord ++ tailWord_5023596).sum := by decide
  have hdescent : baseEnd_5023596 < baseStart_5023596 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023606 : List Nat := [5, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2]
def baseStart_5023606 : Nat := 118140960795 + 5023606 * 2 ^ 59
def prefixEnd_5023606 : Nat := 4983230072969 + 3 ^ 40 * 5023606 * 2
def baseEnd_5023606 : Nat := 2579524496810577352121863

theorem tailTrace_5023606 : CollatzResearch.WordTrace tailWord_5023606 prefixEnd_5023606 2579524496810577352121863 := by
  unfold tailWord_5023606
  simp only [CollatzResearch.WordTrace]
  refine ⟨11451622714896306277746167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 122150642292227266962625781 11451622714896306277746167)
  ·
    refine ⟨17177434072344459416619251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11451622714896306277746167 17177434072344459416619251)
    ·
      refine ⟨25766151108516689124928877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17177434072344459416619251 25766151108516689124928877)
      ·
        refine ⟨9662306665693758421848329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25766151108516689124928877 9662306665693758421848329)
        ·
          refine ⟨7246729999270318816386247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9662306665693758421848329 7246729999270318816386247)
          ·
            refine ⟨10870094998905478224579371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7246729999270318816386247 10870094998905478224579371)
            ·
              refine ⟨16305142498358217336869057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10870094998905478224579371 16305142498358217336869057)
              ·
                refine ⟨12228856873768663002651793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16305142498358217336869057 12228856873768663002651793)
                ·
                  refine ⟨9171642655326497251988845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12228856873768663002651793 9171642655326497251988845)
                  ·
                    refine ⟨3439365995747436469495817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9171642655326497251988845 3439365995747436469495817)
                    ·
                      refine ⟨2579524496810577352121863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3439365995747436469495817 2579524496810577352121863)
                      ·
                        rfl

theorem cell23_5023606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_5023606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023606 prefixEnd_5023606 := by exact prefixLift 5023606
  have htrace : WordTrace (prefixWord ++ tailWord_5023606) baseStart_5023606 baseEnd_5023606 := by
    simpa [prefixWord, tailWord_5023606, baseEnd_5023606] using wordTrace_append hprefix tailTrace_5023606
  have hstable : (prefixWord ++ tailWord_5023606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023606).length < 2 ^ (prefixWord ++ tailWord_5023606).sum := by decide
  have hdescent : baseEnd_5023606 < baseStart_5023606 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023619 : List Nat := [1, 1, 1, 3, 4, 2, 3, 1, 3, 2, 2]
def baseStart_5023619 : Nat := 118140960795 + 5023619 * 2 ^ 59
def prefixEnd_5023619 : Nat := 4983230072969 + 3 ^ 40 * 5023619 * 2
def baseEnd_5023619 : Nat := 2579531172059085801259303

theorem tailTrace_5023619 : CollatzResearch.WordTrace tailWord_5023619 prefixEnd_5023619 2579531172059085801259303 := by
  unfold tailWord_5023619
  simp only [CollatzResearch.WordTrace]
  refine ⟨183226437587293803664161911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122150958391529202442774607 183226437587293803664161911)
  ·
    refine ⟨274839656380940705496242867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183226437587293803664161911 274839656380940705496242867)
    ·
      refine ⟨412259484571411058244364301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274839656380940705496242867 412259484571411058244364301)
      ·
        refine ⟨154597306714279146841636613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 412259484571411058244364301 154597306714279146841636613)
        ·
          refine ⟨28986995008927340032806865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 154597306714279146841636613 28986995008927340032806865)
          ·
            refine ⟨21740246256695505024605149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28986995008927340032806865 21740246256695505024605149)
            ·
              refine ⟨8152592346260814384226931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21740246256695505024605149 8152592346260814384226931)
              ·
                refine ⟨12228888519391221576340397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8152592346260814384226931 12228888519391221576340397)
                ·
                  refine ⟨4585833194771708091127649, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12228888519391221576340397 4585833194771708091127649)
                  ·
                    refine ⟨3439374896078781068345737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4585833194771708091127649 3439374896078781068345737)
                    ·
                      refine ⟨2579531172059085801259303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3439374896078781068345737 2579531172059085801259303)
                      ·
                        rfl

theorem cell23_5023619_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 3, 1, 3, 2, 2].length) (baseStart_5023619 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023619 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023619 prefixEnd_5023619 := by exact prefixLift 5023619
  have htrace : WordTrace (prefixWord ++ tailWord_5023619) baseStart_5023619 baseEnd_5023619 := by
    simpa [prefixWord, tailWord_5023619, baseEnd_5023619] using wordTrace_append hprefix tailTrace_5023619
  have hstable : (prefixWord ++ tailWord_5023619).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023619).length < 2 ^ (prefixWord ++ tailWord_5023619).sum := by decide
  have hdescent : baseEnd_5023619 < baseStart_5023619 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023619) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023628 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 1, 4, 6]
def baseStart_5023628 : Nat := 118140960795 + 5023628 * 2 ^ 59
def prefixEnd_5023628 : Nat := 4983230072969 + 3 ^ 40 * 5023628 * 2
def baseEnd_5023628 : Nat := 2579535793384976266046761

theorem tailTrace_5023628 : CollatzResearch.WordTrace tailWord_5023628 prefixEnd_5023628 2579535793384976266046761 := by
  unfold tailWord_5023628
  simp only [CollatzResearch.WordTrace]
  refine ⟨91613382922130599100619769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122151177229507465467493025 91613382922130599100619769)
  ·
    refine ⟨68710037191597949325464827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91613382922130599100619769 68710037191597949325464827)
    ·
      refine ⟨103065055787396923988197241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68710037191597949325464827 103065055787396923988197241)
      ·
        refine ⟨77298791840547692991147931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103065055787396923988197241 77298791840547692991147931)
        ·
          refine ⟨115948187760821539486721897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77298791840547692991147931 115948187760821539486721897)
          ·
            refine ⟨86961140820616154615041423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115948187760821539486721897 86961140820616154615041423)
            ·
              refine ⟨130441711230924231922562135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86961140820616154615041423 130441711230924231922562135)
              ·
                refine ⟨195662566846386347883843203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130441711230924231922562135 195662566846386347883843203)
                ·
                  refine ⟨293493850269579521825764805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 195662566846386347883843203 293493850269579521825764805)
                  ·
                    refine ⟨55030096925546160342330901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 293493850269579521825764805 55030096925546160342330901)
                    ·
                      refine ⟨2579535793384976266046761, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55030096925546160342330901 2579535793384976266046761)
                      ·
                        rfl

theorem cell23_5023628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 1, 4, 6].length) (baseStart_5023628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023628 prefixEnd_5023628 := by exact prefixLift 5023628
  have htrace : WordTrace (prefixWord ++ tailWord_5023628) baseStart_5023628 baseEnd_5023628 := by
    simpa [prefixWord, tailWord_5023628, baseEnd_5023628] using wordTrace_append hprefix tailTrace_5023628
  have hstable : (prefixWord ++ tailWord_5023628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023628).length < 2 ^ (prefixWord ++ tailWord_5023628).sum := by decide
  have hdescent : baseEnd_5023628 < baseStart_5023628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023639 : List Nat := [1, 1, 3, 3, 1, 5, 1, 2, 1, 2, 3]
def baseStart_5023639 : Nat := 118140960795 + 5023639 * 2 ^ 59
def prefixEnd_5023639 : Nat := 4983230072969 + 3 ^ 40 * 5023639 * 2
def baseEnd_5023639 : Nat := 2579541441672175723009211

theorem tailTrace_5023639 : CollatzResearch.WordTrace tailWord_5023639 prefixEnd_5023639 2579541441672175723009211 := by
  unfold tailWord_5023639
  simp only [CollatzResearch.WordTrace]
  refine ⟨183227167047221347079889971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122151444698147564719926647 183227167047221347079889971)
  ·
    refine ⟨274840750570832020619834957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183227167047221347079889971 274840750570832020619834957)
    ·
      refine ⟨103065281464062007732438109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 274840750570832020619834957 103065281464062007732438109)
      ·
        refine ⟨38649480549023252899664291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103065281464062007732438109 38649480549023252899664291)
        ·
          refine ⟨57974220823534879349496437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38649480549023252899664291 57974220823534879349496437)
          ·
            refine ⟨5435083202206394939015291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57974220823534879349496437 5435083202206394939015291)
            ·
              refine ⟨8152624803309592408522937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5435083202206394939015291 8152624803309592408522937)
              ·
                refine ⟨6114468602482194306392203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8152624803309592408522937 6114468602482194306392203)
                ·
                  refine ⟨9171702903723291459588305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6114468602482194306392203 9171702903723291459588305)
                  ·
                    refine ⟨6878777177792468594691229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9171702903723291459588305 6878777177792468594691229)
                    ·
                      refine ⟨2579541441672175723009211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6878777177792468594691229 2579541441672175723009211)
                      ·
                        rfl

theorem cell23_5023639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 5, 1, 2, 1, 2, 3].length) (baseStart_5023639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023639 prefixEnd_5023639 := by exact prefixLift 5023639
  have htrace : WordTrace (prefixWord ++ tailWord_5023639) baseStart_5023639 baseEnd_5023639 := by
    simpa [prefixWord, tailWord_5023639, baseEnd_5023639] using wordTrace_append hprefix tailTrace_5023639
  have hstable : (prefixWord ++ tailWord_5023639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023639).length < 2 ^ (prefixWord ++ tailWord_5023639).sum := by decide
  have hdescent : baseEnd_5023639 < baseStart_5023639 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023652 : List Nat := [2, 3, 1, 2, 1, 4, 1, 2, 1, 3, 3]
def baseStart_5023652 : Nat := 118140960795 + 5023652 * 2 ^ 59
def prefixEnd_5023652 : Nat := 4983230072969 + 3 ^ 40 * 5023652 * 2
def baseEnd_5023652 : Nat := 2579548116920684172146651

theorem tailTrace_5023652 : CollatzResearch.WordTrace tailWord_5023652 prefixEnd_5023652 2579548116920684172146651 := by
  unfold tailWord_5023652
  simp only [CollatzResearch.WordTrace]
  refine ⟨91613820598087125150056605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122151760797449500200075473 91613820598087125150056605)
  ·
    refine ⟨34355182724282671931271227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91613820598087125150056605 34355182724282671931271227)
    ·
      refine ⟨51532774086424007896906841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34355182724282671931271227 51532774086424007896906841)
      ·
        refine ⟨38649580564818005922680131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51532774086424007896906841 38649580564818005922680131)
        ·
          refine ⟨57974370847227008884020197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38649580564818005922680131 57974370847227008884020197)
          ·
            refine ⟨10870194533855064165753787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57974370847227008884020197 10870194533855064165753787)
            ·
              refine ⟨16305291800782596248630681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10870194533855064165753787 16305291800782596248630681)
              ·
                refine ⟨12228968850586947186473011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16305291800782596248630681 12228968850586947186473011)
                ·
                  refine ⟨18343453275880420779709517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12228968850586947186473011 18343453275880420779709517)
                  ·
                    refine ⟨6878794978455157792391069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18343453275880420779709517 6878794978455157792391069)
                    ·
                      refine ⟨2579548116920684172146651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6878794978455157792391069 2579548116920684172146651)
                      ·
                        rfl

theorem cell23_5023652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 4, 1, 2, 1, 3, 3].length) (baseStart_5023652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023652 prefixEnd_5023652 := by exact prefixLift 5023652
  have htrace : WordTrace (prefixWord ++ tailWord_5023652) baseStart_5023652 baseEnd_5023652 := by
    simpa [prefixWord, tailWord_5023652, baseEnd_5023652] using wordTrace_append hprefix tailTrace_5023652
  have hstable : (prefixWord ++ tailWord_5023652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023652).length < 2 ^ (prefixWord ++ tailWord_5023652).sum := by decide
  have hdescent : baseEnd_5023652 < baseStart_5023652 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023656 : List Nat := [2, 1, 6, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_5023656 : Nat := 118140960795 + 5023656 * 2 ^ 59
def prefixEnd_5023656 : Nat := 4983230072969 + 3 ^ 40 * 5023656 * 2
def baseEnd_5023656 : Nat := 2579550170843302156496633

theorem tailTrace_5023656 : CollatzResearch.WordTrace tailWord_5023656 prefixEnd_5023656 2579550170843302156496633 := by
  unfold tailWord_5023656
  simp only [CollatzResearch.WordTrace]
  refine ⟨91613893544079879491629411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122151858058773172655505881 91613893544079879491629411)
  ·
    refine ⟨137420840316119819237444117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91613893544079879491629411 137420840316119819237444117)
    ·
      refine ⟨6441601889818116526755193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 137420840316119819237444117 6441601889818116526755193)
      ·
        refine ⟨4831201417363587395066395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6441601889818116526755193 4831201417363587395066395)
        ·
          refine ⟨7246802126045381092599593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4831201417363587395066395 7246802126045381092599593)
          ·
            refine ⟨5435101594534035819449695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7246802126045381092599593 5435101594534035819449695)
            ·
              refine ⟨8152652391801053729174543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5435101594534035819449695 8152652391801053729174543)
              ·
                refine ⟨12228978587701580593761815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8152652391801053729174543 12228978587701580593761815)
                ·
                  refine ⟨18343467881552370890642723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12228978587701580593761815 18343467881552370890642723)
                  ·
                    refine ⟨27515201822328556335964085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18343467881552370890642723 27515201822328556335964085)
                    ·
                      refine ⟨2579550170843302156496633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27515201822328556335964085 2579550170843302156496633)
                      ·
                        rfl

theorem cell23_5023656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_5023656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023656 prefixEnd_5023656 := by exact prefixLift 5023656
  have htrace : WordTrace (prefixWord ++ tailWord_5023656) baseStart_5023656 baseEnd_5023656 := by
    simpa [prefixWord, tailWord_5023656, baseEnd_5023656] using wordTrace_append hprefix tailTrace_5023656
  have hstable : (prefixWord ++ tailWord_5023656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023656).length < 2 ^ (prefixWord ++ tailWord_5023656).sum := by decide
  have hdescent : baseEnd_5023656 < baseStart_5023656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023669 : List Nat := [1, 3, 3, 2, 1, 2, 1, 4, 2, 1, 3]
def baseStart_5023669 : Nat := 118140960795 + 5023669 * 2 ^ 59
def prefixEnd_5023669 : Nat := 4983230072969 + 3 ^ 40 * 5023669 * 2
def baseEnd_5023669 : Nat := 2579556846091810605634073

theorem tailTrace_5023669 : CollatzResearch.WordTrace tailWord_5023669 prefixEnd_5023669 2579556846091810605634073 := by
  unfold tailWord_5023669
  simp only [CollatzResearch.WordTrace]
  refine ⟨183228261237112662203482061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122152174158075108135654707 183228261237112662203482061)
  ·
    refine ⟨68710597963917248326305773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183228261237112662203482061 68710597963917248326305773)
    ·
      refine ⟨25766474236468968122364665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68710597963917248326305773 25766474236468968122364665)
      ·
        refine ⟨19324855677351726091773499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25766474236468968122364665 19324855677351726091773499)
        ·
          refine ⟨28987283516027589137660249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19324855677351726091773499 28987283516027589137660249)
          ·
            refine ⟨21740462637020691853245187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28987283516027589137660249 21740462637020691853245187)
            ·
              refine ⟨32610693955531037779867781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21740462637020691853245187 32610693955531037779867781)
              ·
                refine ⟨6114505116662069583725209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32610693955531037779867781 6114505116662069583725209)
                ·
                  refine ⟨4585878837496552187793907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6114505116662069583725209 4585878837496552187793907)
                  ·
                    refine ⟨6878818256244828281690861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4585878837496552187793907 6878818256244828281690861)
                    ·
                      refine ⟨2579556846091810605634073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6878818256244828281690861 2579556846091810605634073)
                      ·
                        rfl

theorem cell23_5023669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_5023669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023669 prefixEnd_5023669 := by exact prefixLift 5023669
  have htrace : WordTrace (prefixWord ++ tailWord_5023669) baseStart_5023669 baseEnd_5023669 := by
    simpa [prefixWord, tailWord_5023669, baseEnd_5023669] using wordTrace_append hprefix tailTrace_5023669
  have hstable : (prefixWord ++ tailWord_5023669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023669).length < 2 ^ (prefixWord ++ tailWord_5023669).sum := by decide
  have hdescent : baseEnd_5023669 < baseStart_5023669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023695 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 2, 4, 3]
def baseStart_5023695 : Nat := 118140960795 + 5023695 * 2 ^ 59
def prefixEnd_5023695 : Nat := 4983230072969 + 3 ^ 40 * 5023695 * 2
def baseEnd_5023695 : Nat := 2579570196588827503908953

theorem tailTrace_5023695 : CollatzResearch.WordTrace tailWord_5023695 prefixEnd_5023695 2579570196588827503908953 := by
  unfold tailWord_5023695
  simp only [CollatzResearch.WordTrace]
  refine ⟨183229209535018468643928539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122152806356678979095952359 183229209535018468643928539)
  ·
    refine ⟨274843814302527702965892809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183229209535018468643928539 274843814302527702965892809)
    ·
      refine ⟨206132860726895777224419607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274843814302527702965892809 206132860726895777224419607)
      ·
        refine ⟨309199291090343665836629411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206132860726895777224419607 309199291090343665836629411)
        ·
          refine ⟨463798936635515498754944117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309199291090343665836629411 463798936635515498754944117)
          ·
            refine ⟨43481150309579578008276011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 463798936635515498754944117 43481150309579578008276011)
            ·
              refine ⟨65221725464369367012414017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43481150309579578008276011 65221725464369367012414017)
              ·
                refine ⟨48916294098277025259310513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65221725464369367012414017 48916294098277025259310513)
                ·
                  refine ⟨36687220573707768944482885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48916294098277025259310513 36687220573707768944482885)
                  ·
                    refine ⟨6878853857570206677090541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 36687220573707768944482885 6878853857570206677090541)
                    ·
                      refine ⟨2579570196588827503908953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6878853857570206677090541 2579570196588827503908953)
                      ·
                        rfl

theorem cell23_5023695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 2, 4, 3].length) (baseStart_5023695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023695 prefixEnd_5023695 := by exact prefixLift 5023695
  have htrace : WordTrace (prefixWord ++ tailWord_5023695) baseStart_5023695 baseEnd_5023695 := by
    simpa [prefixWord, tailWord_5023695, baseEnd_5023695] using wordTrace_append hprefix tailTrace_5023695
  have hstable : (prefixWord ++ tailWord_5023695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023695).length < 2 ^ (prefixWord ++ tailWord_5023695).sum := by decide
  have hdescent : baseEnd_5023695 < baseStart_5023695 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023726 : List Nat := [4, 1, 2, 1, 3, 2, 1, 1, 4, 2, 2]
def baseStart_5023726 : Nat := 118140960795 + 5023726 * 2 ^ 59
def prefixEnd_5023726 : Nat := 4983230072969 + 3 ^ 40 * 5023726 * 2
def baseEnd_5023726 : Nat := 2579586114489116882621311

theorem tailTrace_5023726 : CollatzResearch.WordTrace tailWord_5023726 prefixEnd_5023726 2579586114489116882621311 := by
  unfold tailWord_5023726
  simp only [CollatzResearch.WordTrace]
  refine ⟨22903792524738270117288379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122153560131937440625538021 22903792524738270117288379)
  ·
    refine ⟨34355688787107405175932569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22903792524738270117288379 34355688787107405175932569)
    ·
      refine ⟨25766766590330553881949427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34355688787107405175932569 25766766590330553881949427)
      ·
        refine ⟨38650149885495830822924141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25766766590330553881949427 38650149885495830822924141)
        ·
          refine ⟨14493806207060936558596553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38650149885495830822924141 14493806207060936558596553)
          ·
            refine ⟨10870354655295702418947415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14493806207060936558596553 10870354655295702418947415)
            ·
              refine ⟨16305531982943553628421123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10870354655295702418947415 16305531982943553628421123)
              ·
                refine ⟨24458297974415330442631685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16305531982943553628421123 24458297974415330442631685)
                ·
                  refine ⟨4585930870202874457993441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24458297974415330442631685 4585930870202874457993441)
                  ·
                    refine ⟨3439448152652155843495081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4585930870202874457993441 3439448152652155843495081)
                    ·
                      refine ⟨2579586114489116882621311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3439448152652155843495081 2579586114489116882621311)
                      ·
                        rfl

theorem cell23_5023726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 3, 2, 1, 1, 4, 2, 2].length) (baseStart_5023726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023726 prefixEnd_5023726 := by exact prefixLift 5023726
  have htrace : WordTrace (prefixWord ++ tailWord_5023726) baseStart_5023726 baseEnd_5023726 := by
    simpa [prefixWord, tailWord_5023726, baseEnd_5023726] using wordTrace_append hprefix tailTrace_5023726
  have hstable : (prefixWord ++ tailWord_5023726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023726).length < 2 ^ (prefixWord ++ tailWord_5023726).sum := by decide
  have hdescent : baseEnd_5023726 < baseStart_5023726 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023745 : List Nat := [1, 2, 4, 1, 2, 1, 1, 1, 3, 7]
def baseStart_5023745 : Nat := 118140960795 + 5023745 * 2 ^ 59
def prefixEnd_5023745 : Nat := 4983230072969 + 3 ^ 40 * 5023745 * 2
def baseEnd_5023745 : Nat := 859865290207184102761241

theorem tailTrace_5023745 : CollatzResearch.WordTrace tailWord_5023745 prefixEnd_5023745 859865290207184102761241 := by
  unfold tailWord_5023745
  simp only [CollatzResearch.WordTrace]
  refine ⟨183231033184837327183248689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122154022123224884788832459 183231033184837327183248689)
  ·
    refine ⟨137423274888627995387436517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183231033184837327183248689 137423274888627995387436517)
    ·
      refine ⟨25766864041617749135144347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 137423274888627995387436517 25766864041617749135144347)
      ·
        refine ⟨38650296062426623702716521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25766864041617749135144347 38650296062426623702716521)
        ·
          refine ⟨28987722046819967777037391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38650296062426623702716521 28987722046819967777037391)
          ·
            refine ⟨43481583070229951665556087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28987722046819967777037391 43481583070229951665556087)
            ·
              refine ⟨65222374605344927498334131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43481583070229951665556087 65222374605344927498334131)
              ·
                refine ⟨97833561908017391247501197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65222374605344927498334131 97833561908017391247501197)
                ·
                  refine ⟨36687585715506521717812949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 97833561908017391247501197 36687585715506521717812949)
                  ·
                    refine ⟨859865290207184102761241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 36687585715506521717812949 859865290207184102761241)
                    ·
                      rfl

theorem cell23_5023745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 1, 3, 7].length) (baseStart_5023745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023745 prefixEnd_5023745 := by exact prefixLift 5023745
  have htrace : WordTrace (prefixWord ++ tailWord_5023745) baseStart_5023745 baseEnd_5023745 := by
    simpa [prefixWord, tailWord_5023745, baseEnd_5023745] using wordTrace_append hprefix tailTrace_5023745
  have hstable : (prefixWord ++ tailWord_5023745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023745).length < 2 ^ (prefixWord ++ tailWord_5023745).sum := by decide
  have hdescent : baseEnd_5023745 < baseStart_5023745 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023783 : List Nat := [1, 1, 7, 1, 2, 1, 3, 2, 5]
def baseStart_5023783 : Nat := 118140960795 + 5023783 * 2 ^ 59
def prefixEnd_5023783 : Nat := 4983230072969 + 3 ^ 40 * 5023783 * 2
def baseEnd_5023783 : Nat := 286623931431824795512061

theorem tailTrace_5023783 : CollatzResearch.WordTrace tailWord_5023783 prefixEnd_5023783 286623931431824795512061 := by
  unfold tailWord_5023783
  simp only [CollatzResearch.WordTrace]
  refine ⟨183232419158699659673132003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122154946105799773115421335 183232419158699659673132003)
  ·
    refine ⟨274848628738049489509698005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183232419158699659673132003 274848628738049489509698005)
    ·
      refine ⟨6441764736048034910383547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 274848628738049489509698005 6441764736048034910383547)
      ·
        refine ⟨9662647104072052365575321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6441764736048034910383547 9662647104072052365575321)
        ·
          refine ⟨7246985328054039274181491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9662647104072052365575321 7246985328054039274181491)
          ·
            refine ⟨10870477992081058911272237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7246985328054039274181491 10870477992081058911272237)
            ·
              refine ⟨4076429247030397091727089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10870477992081058911272237 4076429247030397091727089)
              ·
                refine ⟨3057321935272797818795317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4076429247030397091727089 3057321935272797818795317)
                ·
                  refine ⟨286623931431824795512061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3057321935272797818795317 286623931431824795512061)
                  ·
                    rfl

theorem cell23_5023783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 1, 3, 2, 5].length) (baseStart_5023783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023783 prefixEnd_5023783 := by exact prefixLift 5023783
  have htrace : WordTrace (prefixWord ++ tailWord_5023783) baseStart_5023783 baseEnd_5023783 := by
    simpa [prefixWord, tailWord_5023783, baseEnd_5023783] using wordTrace_append hprefix tailTrace_5023783
  have hstable : (prefixWord ++ tailWord_5023783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023783).length < 2 ^ (prefixWord ++ tailWord_5023783).sum := by decide
  have hdescent : baseEnd_5023783 < baseStart_5023783 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023795 : List Nat := [1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 6]
def baseStart_5023795 : Nat := 118140960795 + 5023795 * 2 ^ 59
def prefixEnd_5023795 : Nat := 4983230072969 + 3 ^ 40 * 5023795 * 2
def baseEnd_5023795 : Nat := 2579621544654277112658493

theorem tailTrace_5023795 : CollatzResearch.WordTrace tailWord_5023795 prefixEnd_5023795 2579621544654277112658493 := by
  unfold tailWord_5023795
  simp only [CollatzResearch.WordTrace]
  refine ⟨183232856834656185722568839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122155237889770790481712559 183232856834656185722568839)
  ·
    refine ⟨274849285251984278583853259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183232856834656185722568839 274849285251984278583853259)
    ·
      refine ⟨412273927877976417875779889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274849285251984278583853259 412273927877976417875779889)
      ·
        refine ⟨309205445908482313406834917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412273927877976417875779889 309205445908482313406834917)
        ·
          refine ⟨57976021107840433763781547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 309205445908482313406834917 57976021107840433763781547)
          ·
            refine ⟨86964031661760650645672321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57976021107840433763781547 86964031661760650645672321)
            ·
              refine ⟨65223023746320487984254241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86964031661760650645672321 65223023746320487984254241)
              ·
                refine ⟨48917267809740365988190681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65223023746320487984254241 48917267809740365988190681)
                ·
                  refine ⟨36687950857305274491143011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48917267809740365988190681 36687950857305274491143011)
                  ·
                    refine ⟨55031926285957911736714517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 36687950857305274491143011 55031926285957911736714517)
                    ·
                      refine ⟨2579621544654277112658493, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 55031926285957911736714517 2579621544654277112658493)
                      ·
                        rfl

theorem cell23_5023795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 2, 2, 2, 1, 6].length) (baseStart_5023795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023795 prefixEnd_5023795 := by exact prefixLift 5023795
  have htrace : WordTrace (prefixWord ++ tailWord_5023795) baseStart_5023795 baseEnd_5023795 := by
    simpa [prefixWord, tailWord_5023795, baseEnd_5023795] using wordTrace_append hprefix tailTrace_5023795
  have hstable : (prefixWord ++ tailWord_5023795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023795).length < 2 ^ (prefixWord ++ tailWord_5023795).sum := by decide
  have hdescent : baseEnd_5023795 < baseStart_5023795 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023802 : List Nat := [3, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3]
def baseStart_5023802 : Nat := 118140960795 + 5023802 * 2 ^ 59
def prefixEnd_5023802 : Nat := 4983230072969 + 3 ^ 40 * 5023802 * 2
def baseEnd_5023802 : Nat := 2579625139018858585270961

theorem tailTrace_5023802 : CollatzResearch.WordTrace tailWord_5023802 prefixEnd_5023802 2579625139018858585270961 := by
  unfold tailWord_5023802
  simp only [CollatzResearch.WordTrace]
  refine ⟨45808278036407706479518415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122155408097087217278715773 45808278036407706479518415)
  ·
    refine ⟨68712417054611559719277623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45808278036407706479518415 68712417054611559719277623)
    ·
      refine ⟨103068625581917339578916435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68712417054611559719277623 103068625581917339578916435)
      ·
        refine ⟨154602938372876009368374653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103068625581917339578916435 154602938372876009368374653)
        ·
          refine ⟨57976101889828503513140495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154602938372876009368374653 57976101889828503513140495)
          ·
            refine ⟨86964152834742755269710743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57976101889828503513140495 86964152834742755269710743)
            ·
              refine ⟨130446229252114132904566115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86964152834742755269710743 130446229252114132904566115)
              ·
                refine ⟨195669343878171199356849173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 130446229252114132904566115 195669343878171199356849173)
                ·
                  refine ⟨9172000494289274969852305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 195669343878171199356849173 9172000494289274969852305)
                  ·
                    refine ⟨6879000370716956227389229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9172000494289274969852305 6879000370716956227389229)
                    ·
                      refine ⟨2579625139018858585270961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6879000370716956227389229 2579625139018858585270961)
                      ·
                        rfl

theorem cell23_5023802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 1, 6, 2, 3].length) (baseStart_5023802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023802 prefixEnd_5023802 := by exact prefixLift 5023802
  have htrace : WordTrace (prefixWord ++ tailWord_5023802) baseStart_5023802 baseEnd_5023802 := by
    simpa [prefixWord, tailWord_5023802, baseEnd_5023802] using wordTrace_append hprefix tailTrace_5023802
  have hstable : (prefixWord ++ tailWord_5023802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023802).length < 2 ^ (prefixWord ++ tailWord_5023802).sum := by decide
  have hdescent : baseEnd_5023802 < baseStart_5023802 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023825 : List Nat := [1, 2, 2, 1, 3, 1, 1, 2, 1, 1, 8]
def baseStart_5023825 : Nat := 118140960795 + 5023825 * 2 ^ 59
def prefixEnd_5023825 : Nat := 4983230072969 + 3 ^ 40 * 5023825 * 2
def baseEnd_5023825 : Nat := 2579636949073911995283355

theorem tailTrace_5023825 : CollatzResearch.WordTrace tailWord_5023825 prefixEnd_5023825 2579636949073911995283355 := by
  unfold tailWord_5023825
  simp only [CollatzResearch.WordTrace]
  refine ⟨183233951024547500846160929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122155967349698333897440619 183233951024547500846160929)
  ·
    refine ⟨137425463268410625634620697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183233951024547500846160929 137425463268410625634620697)
    ·
      refine ⟨103069097451307969225965523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137425463268410625634620697 103069097451307969225965523)
      ·
        refine ⟨154603646176961953838948285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103069097451307969225965523 154603646176961953838948285)
        ·
          refine ⟨57976367316360732689605607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154603646176961953838948285 57976367316360732689605607)
          ·
            refine ⟨86964550974541099034408411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57976367316360732689605607 86964550974541099034408411)
            ·
              refine ⟨130446826461811648551612617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86964550974541099034408411 130446826461811648551612617)
              ·
                refine ⟨97835119846358736413709463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 130446826461811648551612617 97835119846358736413709463)
                ·
                  refine ⟨146752679769538104620564195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97835119846358736413709463 146752679769538104620564195)
                  ·
                    refine ⟨220129019654307156930846293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 146752679769538104620564195 220129019654307156930846293)
                    ·
                      refine ⟨2579636949073911995283355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 220129019654307156930846293 2579636949073911995283355)
                      ·
                        rfl

theorem cell23_5023825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 2, 1, 1, 8].length) (baseStart_5023825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023825 prefixEnd_5023825 := by exact prefixLift 5023825
  have htrace : WordTrace (prefixWord ++ tailWord_5023825) baseStart_5023825 baseEnd_5023825 := by
    simpa [prefixWord, tailWord_5023825, baseEnd_5023825] using wordTrace_append hprefix tailTrace_5023825
  have hstable : (prefixWord ++ tailWord_5023825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023825).length < 2 ^ (prefixWord ++ tailWord_5023825).sum := by decide
  have hdescent : baseEnd_5023825 < baseStart_5023825 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023849 : List Nat := [1, 2, 1, 1, 1, 5, 2, 3, 3, 1, 3]
def baseStart_5023849 : Nat := 118140960795 + 5023849 * 2 ^ 59
def prefixEnd_5023849 : Nat := 4983230072969 + 3 ^ 40 * 5023849 * 2
def baseEnd_5023849 : Nat := 2579649272609619901383245

theorem tailTrace_5023849 : CollatzResearch.WordTrace tailWord_5023849 prefixEnd_5023849 2579649272609619901383245 := by
  unfold tailWord_5023849
  simp only [CollatzResearch.WordTrace]
  refine ⟨183234826376460552945034601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122156550917640368630023067 183234826376460552945034601)
  ·
    refine ⟨137426119782345414708775951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183234826376460552945034601 137426119782345414708775951)
    ·
      refine ⟨206139179673518122063163927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137426119782345414708775951 206139179673518122063163927)
      ·
        refine ⟨309208769510277183094745891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206139179673518122063163927 309208769510277183094745891)
        ·
          refine ⟨463813154265415774642118837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309208769510277183094745891 463813154265415774642118837)
          ·
            refine ⟨43482483212382728872698641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 463813154265415774642118837 43482483212382728872698641)
            ·
              refine ⟨32611862409287046654523981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43482483212382728872698641 32611862409287046654523981)
              ·
                refine ⟨12229448403482642495446493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32611862409287046654523981 12229448403482642495446493)
                ·
                  refine ⟨4586043151305990935792435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12229448403482642495446493 4586043151305990935792435)
                  ·
                    refine ⟨6879064726958986403688653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4586043151305990935792435 6879064726958986403688653)
                    ·
                      refine ⟨2579649272609619901383245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6879064726958986403688653 2579649272609619901383245)
                      ·
                        rfl

theorem cell23_5023849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 2, 3, 3, 1, 3].length) (baseStart_5023849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023849 prefixEnd_5023849 := by exact prefixLift 5023849
  have htrace : WordTrace (prefixWord ++ tailWord_5023849) baseStart_5023849 baseEnd_5023849 := by
    simpa [prefixWord, tailWord_5023849, baseEnd_5023849] using wordTrace_append hprefix tailTrace_5023849
  have hstable : (prefixWord ++ tailWord_5023849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023849).length < 2 ^ (prefixWord ++ tailWord_5023849).sum := by decide
  have hdescent : baseEnd_5023849 < baseStart_5023849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023852 : List Nat := [2, 2, 1, 1, 3, 3, 1, 2, 3, 5]
def baseStart_5023852 : Nat := 118140960795 + 5023852 * 2 ^ 59
def prefixEnd_5023852 : Nat := 4983230072969 + 3 ^ 40 * 5023852 * 2
def baseEnd_5023852 : Nat := 859883604350527796548577

theorem tailTrace_5023852 : CollatzResearch.WordTrace tailWord_5023852 prefixEnd_5023852 859883604350527796548577 := by
  unfold tailWord_5023852
  simp only [CollatzResearch.WordTrace]
  refine ⟨91617467897724842228696905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122156623863633122971595873 91617467897724842228696905)
  ·
    refine ⟨68713100923293631671522679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91617467897724842228696905 68713100923293631671522679)
    ·
      refine ⟨103069651384940447507284019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68713100923293631671522679 103069651384940447507284019)
      ·
        refine ⟨154604477077410671260926029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103069651384940447507284019 154604477077410671260926029)
        ·
          refine ⟨57976678904029001722847261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 154604477077410671260926029 57976678904029001722847261)
          ·
            refine ⟨21741254589010875646067723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57976678904029001722847261 21741254589010875646067723)
            ·
              refine ⟨32611881883516313469101585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21741254589010875646067723 32611881883516313469101585)
              ·
                refine ⟨24458911412637235101826189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 32611881883516313469101585 24458911412637235101826189)
                ·
                  refine ⟨9172091779738963163184821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24458911412637235101826189 9172091779738963163184821)
                  ·
                    refine ⟨859883604350527796548577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9172091779738963163184821 859883604350527796548577)
                    ·
                      rfl

theorem cell23_5023852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 3, 5].length) (baseStart_5023852 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023852 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023852 prefixEnd_5023852 := by exact prefixLift 5023852
  have htrace : WordTrace (prefixWord ++ tailWord_5023852) baseStart_5023852 baseEnd_5023852 := by
    simpa [prefixWord, tailWord_5023852, baseEnd_5023852] using wordTrace_append hprefix tailTrace_5023852
  have hstable : (prefixWord ++ tailWord_5023852).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023852).length < 2 ^ (prefixWord ++ tailWord_5023852).sum := by decide
  have hdescent : baseEnd_5023852 < baseStart_5023852 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023886 : List Nat := [4, 1, 1, 3, 3, 1, 1, 3, 1, 5]
def baseStart_5023886 : Nat := 118140960795 + 5023886 * 2 ^ 59
def prefixEnd_5023886 : Nat := 4983230072969 + 3 ^ 40 * 5023886 * 2
def baseEnd_5023886 : Nat := 859889423797945418873525

theorem tailTrace_5023886 : CollatzResearch.WordTrace tailWord_5023886 prefixEnd_5023886 859889423797945418873525 := by
  unfold tailWord_5023886
  simp only [CollatzResearch.WordTrace]
  refine ⟨22904521984665813533016439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122157450584884338842754341 22904521984665813533016439)
  ·
    refine ⟨34356782976998720299524659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22904521984665813533016439 34356782976998720299524659)
    ·
      refine ⟨51535174465498080449286989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34356782976998720299524659 51535174465498080449286989)
      ·
        refine ⟨19325690424561780168482621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51535174465498080449286989 19325690424561780168482621)
        ·
          refine ⟨7247133909210667563180983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19325690424561780168482621 7247133909210667563180983)
          ·
            refine ⟨10870700863816001344771475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7247133909210667563180983 10870700863816001344771475)
            ·
              refine ⟨16306051295724002017157213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10870700863816001344771475 16306051295724002017157213)
              ·
                refine ⟨6114769235896500756433955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16306051295724002017157213 6114769235896500756433955)
                ·
                  refine ⟨9172153853844751134650933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6114769235896500756433955 9172153853844751134650933)
                  ·
                    refine ⟨859889423797945418873525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9172153853844751134650933 859889423797945418873525)
                    ·
                      rfl

theorem cell23_5023886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 1, 1, 3, 1, 5].length) (baseStart_5023886 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023886 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023886 prefixEnd_5023886 := by exact prefixLift 5023886
  have htrace : WordTrace (prefixWord ++ tailWord_5023886) baseStart_5023886 baseEnd_5023886 := by
    simpa [prefixWord, tailWord_5023886, baseEnd_5023886] using wordTrace_append hprefix tailTrace_5023886
  have hstable : (prefixWord ++ tailWord_5023886).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023886).length < 2 ^ (prefixWord ++ tailWord_5023886).sum := by decide
  have hdescent : baseEnd_5023886 < baseStart_5023886 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023957 : List Nat := [1, 3, 2, 4, 3, 1, 1, 1, 3, 2, 2]
def baseStart_5023957 : Nat := 118140960795 + 5023957 * 2 ^ 59
def prefixEnd_5023957 : Nat := 4983230072969 + 3 ^ 40 * 5023957 * 2
def baseEnd_5023957 : Nat := 2579704728520305478832749

theorem tailTrace_5023957 : CollatzResearch.WordTrace tailWord_5023957 prefixEnd_5023957 2579704728520305478832749 := by
  unfold tailWord_5023957
  simp only [CollatzResearch.WordTrace]
  refine ⟨183238765460069287389966125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122159176973379524926644083 183238765460069287389966125)
  ·
    refine ⟨68714537047525982771237297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183238765460069287389966125 68714537047525982771237297)
    ·
      refine ⟨51535902785644487078427973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68714537047525982771237297 51535902785644487078427973)
      ·
        refine ⟨9662981772308341327205245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51535902785644487078427973 9662981772308341327205245)
        ·
          refine ⟨3623618164615627997701967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9662981772308341327205245 3623618164615627997701967)
          ·
            refine ⟨5435427246923441996552951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3623618164615627997701967 5435427246923441996552951)
            ·
              refine ⟨8153140870385162994829427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5435427246923441996552951 8153140870385162994829427)
              ·
                refine ⟨12229711305577744492244141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8153140870385162994829427 12229711305577744492244141)
                ·
                  refine ⟨4586141739591654184591553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12229711305577744492244141 4586141739591654184591553)
                  ·
                    refine ⟨3439606304693740638443665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4586141739591654184591553 3439606304693740638443665)
                    ·
                      refine ⟨2579704728520305478832749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3439606304693740638443665 2579704728520305478832749)
                      ·
                        rfl

theorem cell23_5023957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 1, 1, 3, 2, 2].length) (baseStart_5023957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023957 prefixEnd_5023957 := by exact prefixLift 5023957
  have htrace : WordTrace (prefixWord ++ tailWord_5023957) baseStart_5023957 baseEnd_5023957 := by
    simpa [prefixWord, tailWord_5023957, baseEnd_5023957] using wordTrace_append hprefix tailTrace_5023957
  have hstable : (prefixWord ++ tailWord_5023957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023957).length < 2 ^ (prefixWord ++ tailWord_5023957).sum := by decide
  have hdescent : baseEnd_5023957 < baseStart_5023957 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023972 : List Nat := [2, 3, 1, 1, 1, 2, 1, 3, 1, 8]
def baseStart_5023972 : Nat := 118140960795 + 5023972 * 2 ^ 59
def prefixEnd_5023972 : Nat := 4983230072969 + 3 ^ 40 * 5023972 * 2
def baseEnd_5023972 : Nat := 859904143576707640048393

theorem tailTrace_5023972 : CollatzResearch.WordTrace tailWord_5023972 prefixEnd_5023972 859904143576707640048393 := by
  unfold tailWord_5023972
  simp only [CollatzResearch.WordTrace]
  refine ⟨91619656277507472475881085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122159541703343296634508113 91619656277507472475881085)
  ·
    refine ⟨34357371104065302178455407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91619656277507472475881085 34357371104065302178455407)
    ·
      refine ⟨51536056656097953267683111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34357371104065302178455407 51536056656097953267683111)
      ·
        refine ⟨77304084984146929901524667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51536056656097953267683111 77304084984146929901524667)
        ·
          refine ⟨115956127476220394852287001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77304084984146929901524667 115956127476220394852287001)
          ·
            refine ⟨86967095607165296139215251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115956127476220394852287001 86967095607165296139215251)
            ·
              refine ⟨130450643410747944208822877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86967095607165296139215251 130450643410747944208822877)
              ·
                refine ⟨48918991279030479078308579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 130450643410747944208822877 48918991279030479078308579)
                ·
                  refine ⟨73378486918545718617462869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48918991279030479078308579 73378486918545718617462869)
                  ·
                    refine ⟨859904143576707640048393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 73378486918545718617462869 859904143576707640048393)
                    ·
                      rfl

theorem cell23_5023972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 1, 3, 1, 8].length) (baseStart_5023972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023972 prefixEnd_5023972 := by exact prefixLift 5023972
  have htrace : WordTrace (prefixWord ++ tailWord_5023972) baseStart_5023972 baseEnd_5023972 := by
    simpa [prefixWord, tailWord_5023972, baseEnd_5023972] using wordTrace_append hprefix tailTrace_5023972
  have hstable : (prefixWord ++ tailWord_5023972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023972).length < 2 ^ (prefixWord ++ tailWord_5023972).sum := by decide
  have hdescent : baseEnd_5023972 < baseStart_5023972 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023973 : List Nat := [1, 3, 1, 4, 2, 2, 1, 3, 2, 1, 3]
def baseStart_5023973 : Nat := 118140960795 + 5023973 * 2 ^ 59
def prefixEnd_5023973 : Nat := 4983230072969 + 3 ^ 40 * 5023973 * 2
def baseEnd_5023973 : Nat := 2579712944210777416232675

theorem tailTrace_5023973 : CollatzResearch.WordTrace tailWord_5023973 prefixEnd_5023973 2579712944210777416232675 := by
  unfold tailWord_5023973
  simp only [CollatzResearch.WordTrace]
  refine ⟨183239349028011322122548573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122159566018674214748365715 183239349028011322122548573)
  ·
    refine ⟨68714755885504245795955715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183239349028011322122548573 68714755885504245795955715)
    ·
      refine ⟨103072133828256368693933573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68714755885504245795955715 103072133828256368693933573)
      ·
        refine ⟨19326025092798069130112545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 103072133828256368693933573 19326025092798069130112545)
        ·
          refine ⟨14494518819598551847584409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19326025092798069130112545 14494518819598551847584409)
          ·
            refine ⟨10870889114698913885688307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14494518819598551847584409 10870889114698913885688307)
            ·
              refine ⟨16306333672048370828532461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10870889114698913885688307 16306333672048370828532461)
              ·
                refine ⟨6114875127018139060699673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16306333672048370828532461 6114875127018139060699673)
                ·
                  refine ⟨4586156345263604295524755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6114875127018139060699673 4586156345263604295524755)
                  ·
                    refine ⟨6879234517895406443287133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4586156345263604295524755 6879234517895406443287133)
                    ·
                      refine ⟨2579712944210777416232675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6879234517895406443287133 2579712944210777416232675)
                      ·
                        rfl

theorem cell23_5023973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 2, 1, 3, 2, 1, 3].length) (baseStart_5023973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023973 prefixEnd_5023973 := by exact prefixLift 5023973
  have htrace : WordTrace (prefixWord ++ tailWord_5023973) baseStart_5023973 baseEnd_5023973 := by
    simpa [prefixWord, tailWord_5023973, baseEnd_5023973] using wordTrace_append hprefix tailTrace_5023973
  have hstable : (prefixWord ++ tailWord_5023973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023973).length < 2 ^ (prefixWord ++ tailWord_5023973).sum := by decide
  have hdescent : baseEnd_5023973 < baseStart_5023973 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023983 : List Nat := [1, 1, 2, 1, 6, 1, 3, 2, 1, 3, 2]
def baseStart_5023983 : Nat := 118140960795 + 5023983 * 2 ^ 59
def prefixEnd_5023983 : Nat := 4983230072969 + 3 ^ 40 * 5023983 * 2
def baseEnd_5023983 : Nat := 2579718079017322377107629

theorem tailTrace_5023983 : CollatzResearch.WordTrace tailWord_5023983 prefixEnd_5023983 2579718079017322377107629 := by
  unfold tailWord_5023983
  simp only [CollatzResearch.WordTrace]
  refine ⟨183239713757975093830412603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122159809171983395886941735 183239713757975093830412603)
  ·
    refine ⟨274859570636962640745618905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183239713757975093830412603 274859570636962640745618905)
    ·
      refine ⟨206144677977721980559214179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274859570636962640745618905 206144677977721980559214179)
      ·
        refine ⟨309217016966582970838821269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206144677977721980559214179 309217016966582970838821269)
        ·
          refine ⟨14494547670308576758069747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 309217016966582970838821269 14494547670308576758069747)
          ·
            refine ⟨21741821505462865137104621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14494547670308576758069747 21741821505462865137104621)
            ·
              refine ⟨8153183064548574426414233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21741821505462865137104621 8153183064548574426414233)
              ·
                refine ⟨6114887298411430819810675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8153183064548574426414233 6114887298411430819810675)
                ·
                  refine ⟨9172330947617146229716013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6114887298411430819810675 9172330947617146229716013)
                  ·
                    refine ⟨3439624105356429836143505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9172330947617146229716013 3439624105356429836143505)
                    ·
                      refine ⟨2579718079017322377107629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3439624105356429836143505 2579718079017322377107629)
                      ·
                        rfl

theorem cell23_5023983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 6, 1, 3, 2, 1, 3, 2].length) (baseStart_5023983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023983 prefixEnd_5023983 := by exact prefixLift 5023983
  have htrace : WordTrace (prefixWord ++ tailWord_5023983) baseStart_5023983 baseEnd_5023983 := by
    simpa [prefixWord, tailWord_5023983, baseEnd_5023983] using wordTrace_append hprefix tailTrace_5023983
  have hstable : (prefixWord ++ tailWord_5023983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023983).length < 2 ^ (prefixWord ++ tailWord_5023983).sum := by decide
  have hdescent : baseEnd_5023983 < baseStart_5023983 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5023996 : List Nat := [2, 2, 2, 1, 4, 1, 1, 1, 3, 4, 2]
def baseStart_5023996 : Nat := 118140960795 + 5023996 * 2 ^ 59
def prefixEnd_5023996 : Nat := 4983230072969 + 3 ^ 40 * 5023996 * 2
def baseEnd_5023996 : Nat := 2579724754265830826245069

theorem tailTrace_5023996 : CollatzResearch.WordTrace tailWord_5023996 prefixEnd_5023996 2579724754265830826245069 := by
  unfold tailWord_5023996
  simp only [CollatzResearch.WordTrace]
  refine ⟨91620093953463998525317921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122160125271285331367090561 91620093953463998525317921)
  ·
    refine ⟨68715070465097998893988441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 91620093953463998525317921 68715070465097998893988441)
    ·
      refine ⟨51536302848823499170491331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68715070465097998893988441 51536302848823499170491331)
      ·
        refine ⟨77304454273235248755736997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51536302848823499170491331 77304454273235248755736997)
        ·
          refine ⟨14494585176231609141700687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77304454273235248755736997 14494585176231609141700687)
          ·
            refine ⟨21741877764347413712551031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14494585176231609141700687 21741877764347413712551031)
            ·
              refine ⟨32612816646521120568826547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21741877764347413712551031 32612816646521120568826547)
              ·
                refine ⟨48919224969781680853239821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32612816646521120568826547 48919224969781680853239821)
                ·
                  refine ⟨18344709363668130319964933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48919224969781680853239821 18344709363668130319964933)
                  ·
                    refine ⟨3439633005687774434993425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18344709363668130319964933 3439633005687774434993425)
                    ·
                      refine ⟨2579724754265830826245069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3439633005687774434993425 2579724754265830826245069)
                      ·
                        rfl

theorem cell23_5023996_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 1, 1, 3, 4, 2].length) (baseStart_5023996 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5023996 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5023996 prefixEnd_5023996 := by exact prefixLift 5023996
  have htrace : WordTrace (prefixWord ++ tailWord_5023996) baseStart_5023996 baseEnd_5023996 := by
    simpa [prefixWord, tailWord_5023996, baseEnd_5023996] using wordTrace_append hprefix tailTrace_5023996
  have hstable : (prefixWord ++ tailWord_5023996).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5023996).length < 2 ^ (prefixWord ++ tailWord_5023996).sum := by decide
  have hdescent : baseEnd_5023996 < baseStart_5023996 := by decide
  rcases family_descends (prefixWord ++ tailWord_5023996) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024026 : List Nat := [3, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4]
def baseStart_5024026 : Nat := 118140960795 + 5024026 * 2 ^ 59
def prefixEnd_5024026 : Nat := 4983230072969 + 3 ^ 40 * 5024026 * 2
def baseEnd_5024026 : Nat := 2579740158685465708869931

theorem tailTrace_5024026 : CollatzResearch.WordTrace tailWord_5024026 prefixEnd_5024026 2579740158685465708869931 := by
  unfold tailWord_5024026
  simp only [CollatzResearch.WordTrace]
  refine ⟨45810320524204828043556983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122160854731212874782818621 45810320524204828043556983)
  ·
    refine ⟨68715480786307242065335475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45810320524204828043556983 68715480786307242065335475)
    ·
      refine ⟨103073221179460863098003213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68715480786307242065335475 103073221179460863098003213)
      ·
        refine ⟨38652457942297823661751205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 103073221179460863098003213 38652457942297823661751205)
        ·
          refine ⟨7247335864180841936578351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38652457942297823661751205 7247335864180841936578351)
          ·
            refine ⟨10871003796271262904867527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7247335864180841936578351 10871003796271262904867527)
            ·
              refine ⟨16306505694406894357301291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10871003796271262904867527 16306505694406894357301291)
              ·
                refine ⟨24459758541610341535951937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16306505694406894357301291 24459758541610341535951937)
                ·
                  refine ⟨18344818906207756151963953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24459758541610341535951937 18344818906207756151963953)
                  ·
                    refine ⟨13758614179655817113972965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18344818906207756151963953 13758614179655817113972965)
                    ·
                      refine ⟨2579740158685465708869931, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13758614179655817113972965 2579740158685465708869931)
                      ·
                        rfl

theorem cell23_5024026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_5024026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024026 prefixEnd_5024026 := by exact prefixLift 5024026
  have htrace : WordTrace (prefixWord ++ tailWord_5024026) baseStart_5024026 baseEnd_5024026 := by
    simpa [prefixWord, tailWord_5024026, baseEnd_5024026] using wordTrace_append hprefix tailTrace_5024026
  have hstable : (prefixWord ++ tailWord_5024026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024026).length < 2 ^ (prefixWord ++ tailWord_5024026).sum := by decide
  have hdescent : baseEnd_5024026 < baseStart_5024026 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024030 : List Nat := [4, 3, 2, 1, 1, 1, 1, 3, 1, 4, 2]
def baseStart_5024030 : Nat := 118140960795 + 5024030 * 2 ^ 59
def prefixEnd_5024030 : Nat := 4983230072969 + 3 ^ 40 * 5024030 * 2
def baseEnd_5024030 : Nat := 2579742212608083693219913

theorem tailTrace_5024030 : CollatzResearch.WordTrace tailWord_5024030 prefixEnd_5024030 2579742212608083693219913 := by
  unfold tailWord_5024030
  simp only [CollatzResearch.WordTrace]
  refine ⟨22905178498600602607171693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122160951992536547238249029 22905178498600602607171693)
  ·
    refine ⟨8589441936975225977689385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22905178498600602607171693 8589441936975225977689385)
    ·
      refine ⟨6442081452731419483267039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8589441936975225977689385 6442081452731419483267039)
      ·
        refine ⟨9663122179097129224900559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6442081452731419483267039 9663122179097129224900559)
        ·
          refine ⟨14494683268645693837350839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9663122179097129224900559 14494683268645693837350839)
          ·
            refine ⟨21742024902968540756026259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14494683268645693837350839 21742024902968540756026259)
            ·
              refine ⟨32613037354452811134039389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21742024902968540756026259 32613037354452811134039389)
              ·
                refine ⟨12229889007919804175264771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32613037354452811134039389 12229889007919804175264771)
                ·
                  refine ⟨18344833511879706262897157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12229889007919804175264771 18344833511879706262897157)
                  ·
                    refine ⟨3439656283477444924293217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18344833511879706262897157 3439656283477444924293217)
                    ·
                      refine ⟨2579742212608083693219913, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3439656283477444924293217 2579742212608083693219913)
                      ·
                        rfl

theorem cell23_5024030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 3, 1, 4, 2].length) (baseStart_5024030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024030 prefixEnd_5024030 := by exact prefixLift 5024030
  have htrace : WordTrace (prefixWord ++ tailWord_5024030) baseStart_5024030 baseEnd_5024030 := by
    simpa [prefixWord, tailWord_5024030, baseEnd_5024030] using wordTrace_append hprefix tailTrace_5024030
  have hstable : (prefixWord ++ tailWord_5024030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024030).length < 2 ^ (prefixWord ++ tailWord_5024030).sum := by decide
  have hdescent : baseEnd_5024030 < baseStart_5024030 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024099 : List Nat := [1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 4]
def baseStart_5024099 : Nat := 118140960795 + 5024099 * 2 ^ 59
def prefixEnd_5024099 : Nat := 4983230072969 + 3 ^ 40 * 5024099 * 2
def baseEnd_5024099 : Nat := 2579777642773243923257095

theorem tailTrace_5024099 : CollatzResearch.WordTrace tailWord_5024099 prefixEnd_5024099 2579777642773243923257095 := by
  unfold tailWord_5024099
  simp only [CollatzResearch.WordTrace]
  refine ⟨183243944625554845641635351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122162629750369897094423567 183243944625554845641635351)
  ·
    refine ⟨274865916938332268462453027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183243944625554845641635351 274865916938332268462453027)
    ·
      refine ⟨412298875407498402693679541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274865916938332268462453027 412298875407498402693679541)
      ·
        refine ⟨38653019569452975252532457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 412298875407498402693679541 38653019569452975252532457)
        ·
          refine ⟨28989764677089731439399343, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38653019569452975252532457 28989764677089731439399343)
          ·
            refine ⟨43484647015634597159099015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28989764677089731439399343 43484647015634597159099015)
            ·
              refine ⟨65226970523451895738648523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43484647015634597159099015 65226970523451895738648523)
              ·
                refine ⟨97840455785177843607972785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65226970523451895738648523 97840455785177843607972785)
                ·
                  refine ⟨73380341838883382705979589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97840455785177843607972785 73380341838883382705979589)
                  ·
                    refine ⟨13758814094790634257371173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 73380341838883382705979589 13758814094790634257371173)
                    ·
                      refine ⟨2579777642773243923257095, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13758814094790634257371173 2579777642773243923257095)
                      ·
                        rfl

theorem cell23_5024099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 4].length) (baseStart_5024099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024099 prefixEnd_5024099 := by exact prefixLift 5024099
  have htrace : WordTrace (prefixWord ++ tailWord_5024099) baseStart_5024099 baseEnd_5024099 := by
    simpa [prefixWord, tailWord_5024099, baseEnd_5024099] using wordTrace_append hprefix tailTrace_5024099
  have hstable : (prefixWord ++ tailWord_5024099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024099).length < 2 ^ (prefixWord ++ tailWord_5024099).sum := by decide
  have hdescent : baseEnd_5024099 < baseStart_5024099 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024109 : List Nat := [1, 5, 1, 1, 1, 2, 1, 1, 10]
def baseStart_5024109 : Nat := 118140960795 + 5024109 * 2 ^ 59
def prefixEnd_5024109 : Nat := 4983230072969 + 3 ^ 40 * 5024109 * 2
def baseEnd_5024109 : Nat := 286642530842198764903561

theorem tailTrace_5024109 : CollatzResearch.WordTrace tailWord_5024109 prefixEnd_5024109 286642530842198764903561 := by
  unfold tailWord_5024109
  simp only [CollatzResearch.WordTrace]
  refine ⟨183244309355518617349499381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122162872903679078232999587 183244309355518617349499381)
  ·
    refine ⟨17179154002079870376515567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 183244309355518617349499381 17179154002079870376515567)
    ·
      refine ⟨25768731003119805564773351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17179154002079870376515567 25768731003119805564773351)
      ·
        refine ⟨38653096504679708347160027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25768731003119805564773351 38653096504679708347160027)
        ·
          refine ⟨57979644757019562520740041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38653096504679708347160027 57979644757019562520740041)
          ·
            refine ⟨43484733567764671890555031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57979644757019562520740041 43484733567764671890555031)
            ·
              refine ⟨65227100351647007835832547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43484733567764671890555031 65227100351647007835832547)
              ·
                refine ⟨97840650527470511753748821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65227100351647007835832547 97840650527470511753748821)
                ·
                  refine ⟨286642530842198764903561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 97840650527470511753748821 286642530842198764903561)
                  ·
                    rfl

theorem cell23_5024109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_5024109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024109 prefixEnd_5024109 := by exact prefixLift 5024109
  have htrace : WordTrace (prefixWord ++ tailWord_5024109) baseStart_5024109 baseEnd_5024109 := by
    simpa [prefixWord, tailWord_5024109, baseEnd_5024109] using wordTrace_append hprefix tailTrace_5024109
  have hstable : (prefixWord ++ tailWord_5024109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024109).length < 2 ^ (prefixWord ++ tailWord_5024109).sum := by decide
  have hdescent : baseEnd_5024109 < baseStart_5024109 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024163 : List Nat := [1, 1, 1, 4, 1, 4, 1, 3, 2, 3, 2]
def baseStart_5024163 : Nat := 118140960795 + 5024163 * 2 ^ 59
def prefixEnd_5024163 : Nat := 4983230072969 + 3 ^ 40 * 5024163 * 2
def baseEnd_5024163 : Nat := 2579810505535131672856801

theorem tailTrace_5024163 : CollatzResearch.WordTrace tailWord_5024163 prefixEnd_5024163 2579810505535131672856801 := by
  unfold tailWord_5024163
  simp only [CollatzResearch.WordTrace]
  refine ⟨183246278897322984571965143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122164185931548656381310095 183246278897322984571965143)
  ·
    refine ⟨274869418345984476857947715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183246278897322984571965143 274869418345984476857947715)
    ·
      refine ⟨412304127518976715286921573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274869418345984476857947715 412304127518976715286921573)
      ·
        refine ⟨77307023909808134116297795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 412304127518976715286921573 77307023909808134116297795)
        ·
          refine ⟨115960535864712201174446693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77307023909808134116297795 115960535864712201174446693)
          ·
            refine ⟨21742600474633537720208755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115960535864712201174446693 21742600474633537720208755)
            ·
              refine ⟨32613900711950306580313133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21742600474633537720208755 32613900711950306580313133)
              ·
                refine ⟨12230212766981364967617425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32613900711950306580313133 12230212766981364967617425)
                ·
                  refine ⟨9172659575236023725713069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12230212766981364967617425 9172659575236023725713069)
                  ·
                    refine ⟨3439747340713508897142401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9172659575236023725713069 3439747340713508897142401)
                    ·
                      refine ⟨2579810505535131672856801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3439747340713508897142401 2579810505535131672856801)
                      ·
                        rfl

theorem cell23_5024163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 1, 3, 2, 3, 2].length) (baseStart_5024163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024163 prefixEnd_5024163 := by exact prefixLift 5024163
  have htrace : WordTrace (prefixWord ++ tailWord_5024163) baseStart_5024163 baseEnd_5024163 := by
    simpa [prefixWord, tailWord_5024163, baseEnd_5024163] using wordTrace_append hprefix tailTrace_5024163
  have hstable : (prefixWord ++ tailWord_5024163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024163).length < 2 ^ (prefixWord ++ tailWord_5024163).sum := by decide
  have hdescent : baseEnd_5024163 < baseStart_5024163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024176 : List Nat := [2, 1, 1, 1, 2, 1, 1, 2, 4, 6, 2]
def baseStart_5024176 : Nat := 118140960795 + 5024176 * 2 ^ 59
def prefixEnd_5024176 : Nat := 4983230072969 + 3 ^ 40 * 5024176 * 2
def baseEnd_5024176 : Nat := 2579817180783640121994241

theorem tailTrace_5024176 : CollatzResearch.WordTrace tailWord_5024176 prefixEnd_5024176 2579817180783640121994241 := by
  unfold tailWord_5024176
  simp only [CollatzResearch.WordTrace]
  refine ⟨91623376523137943896094191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122164502030850591861458921 91623376523137943896094191)
  ·
    refine ⟨137435064784706915844141287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91623376523137943896094191 137435064784706915844141287)
    ·
      refine ⟨206152597177060373766211931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 137435064784706915844141287 206152597177060373766211931)
      ·
        refine ⟨309228895765590560649317897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206152597177060373766211931 309228895765590560649317897)
        ·
          refine ⟨231921671824192920486988423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309228895765590560649317897 231921671824192920486988423)
          ·
            refine ⟨347882507736289380730482635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231921671824192920486988423 347882507736289380730482635)
            ·
              refine ⟨521823761604434071095723953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 347882507736289380730482635 521823761604434071095723953)
              ·
                refine ⟨391367821203325553321792965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 521823761604434071095723953 391367821203325553321792965)
                ·
                  refine ⟨73381466475623541247836181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 391367821203325553321792965 73381466475623541247836181)
                  ·
                    refine ⟨3439756241044853495992321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 73381466475623541247836181 3439756241044853495992321)
                    ·
                      refine ⟨2579817180783640121994241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3439756241044853495992321 2579817180783640121994241)
                      ·
                        rfl

theorem cell23_5024176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 2, 4, 6, 2].length) (baseStart_5024176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024176 prefixEnd_5024176 := by exact prefixLift 5024176
  have htrace : WordTrace (prefixWord ++ tailWord_5024176) baseStart_5024176 baseEnd_5024176 := by
    simpa [prefixWord, tailWord_5024176, baseEnd_5024176] using wordTrace_append hprefix tailTrace_5024176
  have hstable : (prefixWord ++ tailWord_5024176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024176).length < 2 ^ (prefixWord ++ tailWord_5024176).sum := by decide
  have hdescent : baseEnd_5024176 < baseStart_5024176 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024186 : List Nat := [3, 1, 1, 1, 2, 1, 1, 5, 4, 4]
def baseStart_5024186 : Nat := 118140960795 + 5024186 * 2 ^ 59
def prefixEnd_5024186 : Nat := 4983230072969 + 3 ^ 40 * 5024186 * 2
def baseEnd_5024186 : Nat := 859940771863395027623065

theorem tailTrace_5024186 : CollatzResearch.WordTrace tailWord_5024186 prefixEnd_5024186 859940771863395027623065 := by
  unfold tailWord_5024186
  simp only [CollatzResearch.WordTrace]
  refine ⟨45811779444059914875013103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122164745184159773000034941 45811779444059914875013103)
  ·
    refine ⟨68717669166089872312519655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45811779444059914875013103 68717669166089872312519655)
    ·
      refine ⟨103076503749134808468779483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68717669166089872312519655 103076503749134808468779483)
      ·
        refine ⟨154614755623702212703169225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103076503749134808468779483 154614755623702212703169225)
        ·
          refine ⟨115961066717776659527376919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154614755623702212703169225 115961066717776659527376919)
          ·
            refine ⟨173941600076664989291065379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115961066717776659527376919 173941600076664989291065379)
            ·
              refine ⟨260912400114997483936598069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173941600076664989291065379 260912400114997483936598069)
              ·
                refine ⟨24460537510781014119056069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 260912400114997483936598069 24460537510781014119056069)
                ·
                  refine ⟨4586350783271440147323013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24460537510781014119056069 4586350783271440147323013)
                  ·
                    refine ⟨859940771863395027623065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4586350783271440147323013 859940771863395027623065)
                    ·
                      rfl

theorem cell23_5024186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 5, 4, 4].length) (baseStart_5024186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024186 prefixEnd_5024186 := by exact prefixLift 5024186
  have htrace : WordTrace (prefixWord ++ tailWord_5024186) baseStart_5024186 baseEnd_5024186 := by
    simpa [prefixWord, tailWord_5024186, baseEnd_5024186] using wordTrace_append hprefix tailTrace_5024186
  have hstable : (prefixWord ++ tailWord_5024186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024186).length < 2 ^ (prefixWord ++ tailWord_5024186).sum := by decide
  have hdescent : baseEnd_5024186 < baseStart_5024186 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024209 : List Nat := [1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 7]
def baseStart_5024209 : Nat := 118140960795 + 5024209 * 2 ^ 59
def prefixEnd_5024209 : Nat := 4983230072969 + 3 ^ 40 * 5024209 * 2
def baseEnd_5024209 : Nat := 2579834125645238492881589

theorem tailTrace_5024209 : CollatzResearch.WordTrace tailWord_5024209 prefixEnd_5024209 2579834125645238492881589 := by
  unfold tailWord_5024209
  simp only [CollatzResearch.WordTrace]
  refine ⟨183247956655156334428139681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122165304436770889618759787 183247956655156334428139681)
  ·
    refine ⟨137435967491367250821104761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183247956655156334428139681 137435967491367250821104761)
    ·
      refine ⟨103076975618525438115828571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137435967491367250821104761 103076975618525438115828571)
      ·
        refine ⟨154615463427788157173742857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103076975618525438115828571 154615463427788157173742857)
        ·
          refine ⟨115961597570841117880307143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154615463427788157173742857 115961597570841117880307143)
          ·
            refine ⟨173942396356261676820460715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115961597570841117880307143 173942396356261676820460715)
            ·
              refine ⟨260913594534392515230691073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173942396356261676820460715 260913594534392515230691073)
              ·
                refine ⟨195685195900794386423018305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 260913594534392515230691073 195685195900794386423018305)
                ·
                  refine ⟨146763896925595789817263729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 195685195900794386423018305 146763896925595789817263729)
                  ·
                    refine ⟨110072922694196842362947797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 146763896925595789817263729 110072922694196842362947797)
                    ·
                      refine ⟨2579834125645238492881589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 110072922694196842362947797 2579834125645238492881589)
                      ·
                        rfl

theorem cell23_5024209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 2, 2, 7].length) (baseStart_5024209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024209 prefixEnd_5024209 := by exact prefixLift 5024209
  have htrace : WordTrace (prefixWord ++ tailWord_5024209) baseStart_5024209 baseEnd_5024209 := by
    simpa [prefixWord, tailWord_5024209, baseEnd_5024209] using wordTrace_append hprefix tailTrace_5024209
  have hstable : (prefixWord ++ tailWord_5024209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024209).length < 2 ^ (prefixWord ++ tailWord_5024209).sum := by decide
  have hdescent : baseEnd_5024209 < baseStart_5024209 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024213 : List Nat := [1, 3, 2, 3, 1, 2, 2, 1, 3, 2, 3]
def baseStart_5024213 : Nat := 118140960795 + 5024213 * 2 ^ 59
def prefixEnd_5024213 : Nat := 4983230072969 + 3 ^ 40 * 5024213 * 2
def baseEnd_5024213 : Nat := 2579836179567856477231571

theorem tailTrace_5024213 : CollatzResearch.WordTrace tailWord_5024213 prefixEnd_5024213 2579836179567856477231571 := by
  unfold tailWord_5024213
  simp only [CollatzResearch.WordTrace]
  refine ⟨183248102547141843111285293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122165401698094562074190195 183248102547141843111285293)
  ·
    refine ⟨68718038455178191166731985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183248102547141843111285293 68718038455178191166731985)
    ·
      refine ⟨51538528841383643375048989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68718038455178191166731985 51538528841383643375048989)
      ·
        refine ⟨19326948315518866265643371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51538528841383643375048989 19326948315518866265643371)
        ·
          refine ⟨28990422473278299398465057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19326948315518866265643371 28990422473278299398465057)
          ·
            refine ⟨21742816854958724548848793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28990422473278299398465057 21742816854958724548848793)
            ·
              refine ⟨16307112641219043411636595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21742816854958724548848793 16307112641219043411636595)
              ·
                refine ⟨24460668961828565117454893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16307112641219043411636595 24460668961828565117454893)
                ·
                  refine ⟨9172750860685711919045585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24460668961828565117454893 9172750860685711919045585)
                  ·
                    refine ⟨6879563145514283939284189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 9172750860685711919045585 6879563145514283939284189)
                    ·
                      refine ⟨2579836179567856477231571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6879563145514283939284189 2579836179567856477231571)
                      ·
                        rfl

theorem cell23_5024213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_5024213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024213 prefixEnd_5024213 := by exact prefixLift 5024213
  have htrace : WordTrace (prefixWord ++ tailWord_5024213) baseStart_5024213 baseEnd_5024213 := by
    simpa [prefixWord, tailWord_5024213, baseEnd_5024213] using wordTrace_append hprefix tailTrace_5024213
  have hstable : (prefixWord ++ tailWord_5024213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024213).length < 2 ^ (prefixWord ++ tailWord_5024213).sum := by decide
  have hdescent : baseEnd_5024213 < baseStart_5024213 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024227 : List Nat := [1, 1, 1, 6, 3, 2, 2, 1, 1, 1, 4]
def baseStart_5024227 : Nat := 118140960795 + 5024227 * 2 ^ 59
def prefixEnd_5024227 : Nat := 4983230072969 + 3 ^ 40 * 5024227 * 2
def baseEnd_5024227 : Nat := 2579843368297019422456507

theorem tailTrace_5024227 : CollatzResearch.WordTrace tailWord_5024227 prefixEnd_5024227 2579843368297019422456507 := by
  unfold tailWord_5024227
  simp only [CollatzResearch.WordTrace]
  refine ⟨183248613169091123502294935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122165742112727415668196623 183248613169091123502294935)
  ·
    refine ⟨274872919753636685253442403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183248613169091123502294935 274872919753636685253442403)
    ·
      refine ⟨412309379630455027880163605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274872919753636685253442403 412309379630455027880163605)
      ·
        refine ⟨19327002170177579431882669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 412309379630455027880163605 19327002170177579431882669)
        ·
          refine ⟨7247625813816592286956001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19327002170177579431882669 7247625813816592286956001)
          ·
            refine ⟨5435719360362444215217001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7247625813816592286956001 5435719360362444215217001)
            ·
              refine ⟨4076789520271833161412751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5435719360362444215217001 4076789520271833161412751)
              ·
                refine ⟨6115184280407749742119127, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4076789520271833161412751 6115184280407749742119127)
                ·
                  refine ⟨9172776420611624613178691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6115184280407749742119127 9172776420611624613178691)
                  ·
                    refine ⟨13759164630917436919768037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9172776420611624613178691 13759164630917436919768037)
                    ·
                      refine ⟨2579843368297019422456507, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13759164630917436919768037 2579843368297019422456507)
                      ·
                        rfl

theorem cell23_5024227_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 2, 2, 1, 1, 1, 4].length) (baseStart_5024227 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024227 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024227 prefixEnd_5024227 := by exact prefixLift 5024227
  have htrace : WordTrace (prefixWord ++ tailWord_5024227) baseStart_5024227 baseEnd_5024227 := by
    simpa [prefixWord, tailWord_5024227, baseEnd_5024227] using wordTrace_append hprefix tailTrace_5024227
  have hstable : (prefixWord ++ tailWord_5024227).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024227).length < 2 ^ (prefixWord ++ tailWord_5024227).sum := by decide
  have hdescent : baseEnd_5024227 < baseStart_5024227 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024227) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024237 : List Nat := [1, 5, 1, 3, 1, 3, 1, 2, 2, 4]
def baseStart_5024237 : Nat := 118140960795 + 5024237 * 2 ^ 59
def prefixEnd_5024237 : Nat := 4983230072969 + 3 ^ 40 * 5024237 * 2
def baseEnd_5024237 : Nat := 859949501034521461110487

theorem tailTrace_5024237 : CollatzResearch.WordTrace tailWord_5024237 prefixEnd_5024237 859949501034521461110487 := by
  unfold tailWord_5024237
  simp only [CollatzResearch.WordTrace]
  refine ⟨183248977899054895210158965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122165985266036596806772643 183248977899054895210158965)
  ·
    refine ⟨17179591678036396425952403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 183248977899054895210158965 17179591678036396425952403)
    ·
      refine ⟨25769387517054594638928605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17179591678036396425952403 25769387517054594638928605)
      ·
        refine ⟨9663520318895472989598227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25769387517054594638928605 9663520318895472989598227)
        ·
          refine ⟨14495280478343209484397341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9663520318895472989598227 14495280478343209484397341)
          ·
            refine ⟨5435730179378703556649003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14495280478343209484397341 5435730179378703556649003)
            ·
              refine ⟨8153595269068055334973505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5435730179378703556649003 8153595269068055334973505)
              ·
                refine ⟨6115196451801041501230129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8153595269068055334973505 6115196451801041501230129)
                ·
                  refine ⟨4586397338850781125922597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6115196451801041501230129 4586397338850781125922597)
                  ·
                    refine ⟨859949501034521461110487, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4586397338850781125922597 859949501034521461110487)
                    ·
                      rfl

theorem cell23_5024237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 3, 1, 2, 2, 4].length) (baseStart_5024237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024237 prefixEnd_5024237 := by exact prefixLift 5024237
  have htrace : WordTrace (prefixWord ++ tailWord_5024237) baseStart_5024237 baseEnd_5024237 := by
    simpa [prefixWord, tailWord_5024237, baseEnd_5024237] using wordTrace_append hprefix tailTrace_5024237
  have hstable : (prefixWord ++ tailWord_5024237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024237).length < 2 ^ (prefixWord ++ tailWord_5024237).sum := by decide
  have hdescent : baseEnd_5024237 < baseStart_5024237 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024243 : List Nat := [1, 1, 1, 2, 2, 2, 5, 1, 4, 1, 3]
def baseStart_5024243 : Nat := 118140960795 + 5024243 * 2 ^ 59
def prefixEnd_5024243 : Nat := 4983230072969 + 3 ^ 40 * 5024243 * 2
def baseEnd_5024243 : Nat := 2579851583987491359856433

theorem tailTrace_5024243 : CollatzResearch.WordTrace tailWord_5024243 prefixEnd_5024243 2579851583987491359856433 := by
  unfold tailWord_5024243
  simp only [CollatzResearch.WordTrace]
  refine ⟨183249196737033158234877383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122166131158022105489918255 183249196737033158234877383)
  ·
    refine ⟨274873795105549737352316075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183249196737033158234877383 274873795105549737352316075)
    ·
      refine ⟨412310692658324606028474113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274873795105549737352316075 412310692658324606028474113)
      ·
        refine ⟨309233019493743454521355585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412310692658324606028474113 309233019493743454521355585)
        ·
          refine ⟨231924764620307590891016689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309233019493743454521355585 231924764620307590891016689)
          ·
            refine ⟨173943573465230693168262517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 231924764620307590891016689 173943573465230693168262517)
            ·
              refine ⟨16307210012365377484524611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 173943573465230693168262517 16307210012365377484524611)
              ·
                refine ⟨24460815018548066226786917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16307210012365377484524611 24460815018548066226786917)
                ·
                  refine ⟨4586402815977762417522547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 24460815018548066226786917 4586402815977762417522547)
                  ·
                    refine ⟨6879604223966643626283821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4586402815977762417522547 6879604223966643626283821)
                    ·
                      refine ⟨2579851583987491359856433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6879604223966643626283821 2579851583987491359856433)
                      ·
                        rfl

theorem cell23_5024243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 5, 1, 4, 1, 3].length) (baseStart_5024243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024243 prefixEnd_5024243 := by exact prefixLift 5024243
  have htrace : WordTrace (prefixWord ++ tailWord_5024243) baseStart_5024243 baseEnd_5024243 := by
    simpa [prefixWord, tailWord_5024243, baseEnd_5024243] using wordTrace_append hprefix tailTrace_5024243
  have hstable : (prefixWord ++ tailWord_5024243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024243).length < 2 ^ (prefixWord ++ tailWord_5024243).sum := by decide
  have hdescent : baseEnd_5024243 < baseStart_5024243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024260 : List Nat := [2, 3, 2, 3, 1, 1, 3, 1, 1, 3, 3]
def baseStart_5024260 : Nat := 118140960795 + 5024260 * 2 ^ 59
def prefixEnd_5024260 : Nat := 4983230072969 + 3 ^ 40 * 5024260 * 2
def baseEnd_5024260 : Nat := 2579860313158617793343855

theorem tailTrace_5024260 : CollatzResearch.WordTrace tailWord_5024260 prefixEnd_5024260 2579860313158617793343855 := by
  unfold tailWord_5024260
  simp only [CollatzResearch.WordTrace]
  refine ⟨91624908388985785069123117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122166544518647713425497489 91624908388985785069123117)
  ·
    refine ⟨34359340645869669400921169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 91624908388985785069123117 34359340645869669400921169)
    ·
      refine ⟨25769505484402252050690877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34359340645869669400921169 25769505484402252050690877)
      ·
        refine ⟨9663564556650844519009079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25769505484402252050690877 9663564556650844519009079)
        ·
          refine ⟨14495346834976266778513619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9663564556650844519009079 14495346834976266778513619)
          ·
            refine ⟨21743020252464400167770429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14495346834976266778513619 21743020252464400167770429)
            ·
              refine ⟨8153632594674150062913911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21743020252464400167770429 8153632594674150062913911)
              ·
                refine ⟨12230448892011225094370867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8153632594674150062913911 12230448892011225094370867)
                ·
                  refine ⟨18345673338016837641556301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12230448892011225094370867 18345673338016837641556301)
                  ·
                    refine ⟨6879627501756314115583613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18345673338016837641556301 6879627501756314115583613)
                    ·
                      refine ⟨2579860313158617793343855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6879627501756314115583613 2579860313158617793343855)
                      ·
                        rfl

theorem cell23_5024260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 3, 1, 1, 3, 3].length) (baseStart_5024260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024260 prefixEnd_5024260 := by exact prefixLift 5024260
  have htrace : WordTrace (prefixWord ++ tailWord_5024260) baseStart_5024260 baseEnd_5024260 := by
    simpa [prefixWord, tailWord_5024260, baseEnd_5024260] using wordTrace_append hprefix tailTrace_5024260
  have hstable : (prefixWord ++ tailWord_5024260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024260).length < 2 ^ (prefixWord ++ tailWord_5024260).sum := by decide
  have hdescent : baseEnd_5024260 < baseStart_5024260 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024353 : List Nat := [1, 2, 3, 1, 1, 4, 2, 2, 2, 5]
def baseStart_5024353 : Nat := 118140960795 + 5024353 * 2 ^ 59
def prefixEnd_5024353 : Nat := 4983230072969 + 3 ^ 40 * 5024353 * 2
def baseEnd_5024353 : Nat := 859969355619828643160309

theorem tailTrace_5024353 : CollatzResearch.WordTrace tailWord_5024353 prefixEnd_5024353 859969355619828643160309 := by
  unfold tailWord_5024353
  simp only [CollatzResearch.WordTrace]
  refine ⟨183253208766634647021381713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122168805844423098014254475 183253208766634647021381713)
  ·
    refine ⟨137439906574975985266036285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183253208766634647021381713 137439906574975985266036285)
    ·
      refine ⟨51539964965615994474763607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137439906574975985266036285 51539964965615994474763607)
      ·
        refine ⟨77309947448423991712145411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51539964965615994474763607 77309947448423991712145411)
        ·
          refine ⟨115964921172635987568218117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77309947448423991712145411 115964921172635987568218117)
          ·
            refine ⟨21743422719869247669040897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115964921172635987568218117 21743422719869247669040897)
            ·
              refine ⟨16307567039901935751780673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21743422719869247669040897 16307567039901935751780673)
              ·
                refine ⟨12230675279926451813835505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16307567039901935751780673 12230675279926451813835505)
                ·
                  refine ⟨9173006459944838860376629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12230675279926451813835505 9173006459944838860376629)
                  ·
                    refine ⟨859969355619828643160309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9173006459944838860376629 859969355619828643160309)
                    ·
                      rfl

theorem cell23_5024353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 2, 2, 2, 5].length) (baseStart_5024353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024353 prefixEnd_5024353 := by exact prefixLift 5024353
  have htrace : WordTrace (prefixWord ++ tailWord_5024353) baseStart_5024353 baseEnd_5024353 := by
    simpa [prefixWord, tailWord_5024353, baseEnd_5024353] using wordTrace_append hprefix tailTrace_5024353
  have hstable : (prefixWord ++ tailWord_5024353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024353).length < 2 ^ (prefixWord ++ tailWord_5024353).sum := by decide
  have hdescent : baseEnd_5024353 < baseStart_5024353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024376 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 1, 5, 5]
def baseStart_5024376 : Nat := 118140960795 + 5024376 * 2 ^ 59
def prefixEnd_5024376 : Nat := 4983230072969 + 3 ^ 40 * 5024376 * 2
def baseEnd_5024376 : Nat := 2579919876914539339493321

theorem tailTrace_5024376 : CollatzResearch.WordTrace tailWord_5024376 prefixEnd_5024376 2579919876914539339493321 := by
  unfold tailWord_5024376
  simp only [CollatzResearch.WordTrace]
  refine ⟨91627023822775660974734491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 122169365097034214632979321 91627023822775660974734491)
  ·
    refine ⟨137440535734163491462101737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 91627023822775660974734491 137440535734163491462101737)
    ·
      refine ⟨103080401800622618596576303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137440535734163491462101737 103080401800622618596576303)
      ·
        refine ⟨154620602700933927894864455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 103080401800622618596576303 154620602700933927894864455)
        ·
          refine ⟨231930904051400891842296683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154620602700933927894864455 231930904051400891842296683)
          ·
            refine ⟨347896356077101337763445025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231930904051400891842296683 347896356077101337763445025)
            ·
              refine ⟨260922267057826003322583769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 347896356077101337763445025 260922267057826003322583769)
              ·
                refine ⟨195691700293369502491937827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 260922267057826003322583769 195691700293369502491937827)
                ·
                  refine ⟨293537550440054253737906741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 195691700293369502491937827 293537550440054253737906741)
                  ·
                    refine ⟨27519145353755086287928757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 293537550440054253737906741 27519145353755086287928757)
                    ·
                      refine ⟨2579919876914539339493321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 27519145353755086287928757 2579919876914539339493321)
                      ·
                        rfl

theorem cell23_5024376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_5024376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024376 prefixEnd_5024376 := by exact prefixLift 5024376
  have htrace : WordTrace (prefixWord ++ tailWord_5024376) baseStart_5024376 baseEnd_5024376 := by
    simpa [prefixWord, tailWord_5024376, baseEnd_5024376] using wordTrace_append hprefix tailTrace_5024376
  have hstable : (prefixWord ++ tailWord_5024376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024376).length < 2 ^ (prefixWord ++ tailWord_5024376).sum := by decide
  have hdescent : baseEnd_5024376 < baseStart_5024376 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024417 : List Nat := [1, 2, 3, 3, 3, 1, 2, 1, 3, 4]
def baseStart_5024417 : Nat := 118140960795 + 5024417 * 2 ^ 59
def prefixEnd_5024417 : Nat := 4983230072969 + 3 ^ 40 * 5024417 * 2
def baseEnd_5024417 : Nat := 859980309873791226360211

theorem tailTrace_5024417 : CollatzResearch.WordTrace tailWord_5024417 prefixEnd_5024417 859980309873791226360211 := by
  unfold tailWord_5024417
  simp only [CollatzResearch.WordTrace]
  refine ⟨183255543038402785951711505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122170362025601857301141003 183255543038402785951711505)
  ·
    refine ⟨137441657278802089463783629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183255543038402785951711505 137441657278802089463783629)
    ·
      refine ⟨51540621479550783548918861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 137441657278802089463783629 51540621479550783548918861)
      ·
        refine ⟨19327733054831543830844573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51540621479550783548918861 19327733054831543830844573)
        ·
          refine ⟨7247899895561828936566715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19327733054831543830844573 7247899895561828936566715)
          ·
            refine ⟨10871849843342743404850073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7247899895561828936566715 10871849843342743404850073)
            ·
              refine ⟨8153887382507057553637555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10871849843342743404850073 8153887382507057553637555)
              ·
                refine ⟨12230831073760586330456333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8153887382507057553637555 12230831073760586330456333)
                ·
                  refine ⟨4586561652660219873921125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12230831073760586330456333 4586561652660219873921125)
                  ·
                    refine ⟨859980309873791226360211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4586561652660219873921125 859980309873791226360211)
                    ·
                      rfl

theorem cell23_5024417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 1, 2, 1, 3, 4].length) (baseStart_5024417 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024417 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024417 prefixEnd_5024417 := by exact prefixLift 5024417
  have htrace : WordTrace (prefixWord ++ tailWord_5024417) baseStart_5024417 baseEnd_5024417 := by
    simpa [prefixWord, tailWord_5024417, baseEnd_5024417] using wordTrace_append hprefix tailTrace_5024417
  have hstable : (prefixWord ++ tailWord_5024417).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024417).length < 2 ^ (prefixWord ++ tailWord_5024417).sum := by decide
  have hdescent : baseEnd_5024417 < baseStart_5024417 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024463 : List Nat := [1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 4]
def baseStart_5024463 : Nat := 118140960795 + 5024463 * 2 ^ 59
def prefixEnd_5024463 : Nat := 4983230072969 + 3 ^ 40 * 5024463 * 2
def baseEnd_5024463 : Nat := 2579964549731480499105421

theorem tailTrace_5024463 : CollatzResearch.WordTrace tailWord_5024463 prefixEnd_5024463 2579964549731480499105421 := by
  unfold tailWord_5024463
  simp only [CollatzResearch.WordTrace]
  refine ⟨183257220796236135807886043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122171480530824090538590695 183257220796236135807886043)
  ·
    refine ⟨274885831194354203711829065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183257220796236135807886043 274885831194354203711829065)
    ·
      refine ⟨206164373395765652783871799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 274885831194354203711829065 206164373395765652783871799)
      ·
        refine ⟨309246560093648479175807699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 206164373395765652783871799 309246560093648479175807699)
        ·
          refine ⟨463869840140472718763711549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 309246560093648479175807699 463869840140472718763711549)
          ·
            refine ⟨173951190052677269536391831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 463869840140472718763711549 173951190052677269536391831)
            ·
              refine ⟨260926785079015904304587747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173951190052677269536391831 260926785079015904304587747)
              ·
                refine ⟨391390177618523856456881621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260926785079015904304587747 391390177618523856456881621)
                ·
                  refine ⟨9173207287934152885708163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 391390177618523856456881621 9173207287934152885708163)
                  ·
                    refine ⟨13759810931901229328562245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9173207287934152885708163 13759810931901229328562245)
                    ·
                      refine ⟨2579964549731480499105421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 13759810931901229328562245 2579964549731480499105421)
                      ·
                        rfl

theorem cell23_5024463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 1, 1, 7, 1, 4].length) (baseStart_5024463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024463 prefixEnd_5024463 := by exact prefixLift 5024463
  have htrace : WordTrace (prefixWord ++ tailWord_5024463) baseStart_5024463 baseEnd_5024463 := by
    simpa [prefixWord, tailWord_5024463, baseEnd_5024463] using wordTrace_append hprefix tailTrace_5024463
  have hstable : (prefixWord ++ tailWord_5024463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024463).length < 2 ^ (prefixWord ++ tailWord_5024463).sum := by decide
  have hdescent : baseEnd_5024463 < baseStart_5024463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024497 : List Nat := [1, 2, 2, 2, 2, 2, 2, 1, 5, 2, 2]
def baseStart_5024497 : Nat := 118140960795 + 5024497 * 2 ^ 59
def prefixEnd_5024497 : Nat := 4983230072969 + 3 ^ 40 * 5024497 * 2
def baseEnd_5024497 : Nat := 2579982008073733366080265

theorem tailTrace_5024497 : CollatzResearch.WordTrace tailWord_5024497 prefixEnd_5024497 2579982008073733366080265 := by
  unfold tailWord_5024497
  simp only [CollatzResearch.WordTrace]
  refine ⟨183258460878112959614623745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122172307252075306409749163 183258460878112959614623745)
  ·
    refine ⟨137443845658584719710967809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 183258460878112959614623745 137443845658584719710967809)
    ·
      refine ⟨103082884243938539783225857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 137443845658584719710967809 103082884243938539783225857)
      ·
        refine ⟨77312163182953904837419393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103082884243938539783225857 77312163182953904837419393)
        ·
          refine ⟨57984122387215428628064545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77312163182953904837419393 57984122387215428628064545)
          ·
            refine ⟨43488091790411571471048409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57984122387215428628064545 43488091790411571471048409)
            ·
              refine ⟨32616068842808678603286307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43488091790411571471048409 32616068842808678603286307)
              ·
                refine ⟨48924103264213017904929461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32616068842808678603286307 48924103264213017904929461)
                ·
                  refine ⟨4586634681019970428587137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48924103264213017904929461 4586634681019970428587137)
                  ·
                    refine ⟨3439976010764977821440353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4586634681019970428587137 3439976010764977821440353)
                    ·
                      refine ⟨2579982008073733366080265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3439976010764977821440353 2579982008073733366080265)
                      ·
                        rfl

theorem cell23_5024497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 2, 1, 5, 2, 2].length) (baseStart_5024497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024497 prefixEnd_5024497 := by exact prefixLift 5024497
  have htrace : WordTrace (prefixWord ++ tailWord_5024497) baseStart_5024497 baseEnd_5024497 := by
    simpa [prefixWord, tailWord_5024497, baseEnd_5024497] using wordTrace_append hprefix tailTrace_5024497
  have hstable : (prefixWord ++ tailWord_5024497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024497).length < 2 ^ (prefixWord ++ tailWord_5024497).sum := by decide
  have hdescent : baseEnd_5024497 < baseStart_5024497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024533 : List Nat := [1, 3, 2, 1, 2, 2, 1, 1, 1, 9]
def baseStart_5024533 : Nat := 118140960795 + 5024533 * 2 ^ 59
def prefixEnd_5024533 : Nat := 4983230072969 + 3 ^ 40 * 5024533 * 2
def baseEnd_5024533 : Nat := 860000164459098408410033

theorem tailTrace_5024533 : CollatzResearch.WordTrace tailWord_5024533 prefixEnd_5024533 860000164459098408410033 := by
  unfold tailWord_5024533
  simp only [CollatzResearch.WordTrace]
  refine ⟨183259773905982537762934253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122173182603988358508622835 183259773905982537762934253)
  ·
    refine ⟨68722415214743451661100345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183259773905982537762934253 68722415214743451661100345)
    ·
      refine ⟨51541811411057588745825259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68722415214743451661100345 51541811411057588745825259)
      ·
        refine ⟨77312717116586383118737889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51541811411057588745825259 77312717116586383118737889)
        ·
          refine ⟨57984537837439787339053417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77312717116586383118737889 57984537837439787339053417)
          ·
            refine ⟨43488403378079840504290063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57984537837439787339053417 43488403378079840504290063)
            ·
              refine ⟨65232605067119760756435095, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43488403378079840504290063 65232605067119760756435095)
              ·
                refine ⟨97848907600679641134652643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65232605067119760756435095 97848907600679641134652643)
                ·
                  refine ⟨146773361401019461701978965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97848907600679641134652643 146773361401019461701978965)
                  ·
                    refine ⟨860000164459098408410033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 146773361401019461701978965 860000164459098408410033)
                    ·
                      rfl

theorem cell23_5024533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_5024533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024533 prefixEnd_5024533 := by exact prefixLift 5024533
  have htrace : WordTrace (prefixWord ++ tailWord_5024533) baseStart_5024533 baseEnd_5024533 := by
    simpa [prefixWord, tailWord_5024533, baseEnd_5024533] using wordTrace_append hprefix tailTrace_5024533
  have hstable : (prefixWord ++ tailWord_5024533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024533).length < 2 ^ (prefixWord ++ tailWord_5024533).sum := by decide
  have hdescent : baseEnd_5024533 < baseStart_5024533 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024554 : List Nat := [3, 1, 4, 3, 1, 1, 3, 7]
def baseStart_5024554 : Nat := 118140960795 + 5024554 * 2 ^ 59
def prefixEnd_5024554 : Nat := 4983230072969 + 3 ^ 40 * 5024554 * 2
def baseEnd_5024554 : Nat := 95555973202631097891389

theorem tailTrace_5024554 : CollatzResearch.WordTrace tailWord_5024554 prefixEnd_5024554 95555973202631097891389 := by
  unfold tailWord_5024554
  simp only [CollatzResearch.WordTrace]
  refine ⟨45815134959726614587362179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122173693225937638899632477 45815134959726614587362179)
  ·
    refine ⟨68722702439589921881043269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45815134959726614587362179 68722702439589921881043269)
    ·
      refine ⟨12885506707423110352695613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68722702439589921881043269 12885506707423110352695613)
      ·
        refine ⟨4832065015283666382260855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12885506707423110352695613 4832065015283666382260855)
        ·
          refine ⟨7248097522925499573391283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4832065015283666382260855 7248097522925499573391283)
          ·
            refine ⟨10872146284388249360086925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7248097522925499573391283 10872146284388249360086925)
            ·
              refine ⟨4077054856645593510032597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10872146284388249360086925 4077054856645593510032597)
              ·
                refine ⟨95555973202631097891389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4077054856645593510032597 95555973202631097891389)
                ·
                  rfl

theorem cell23_5024554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 3, 1, 1, 3, 7].length) (baseStart_5024554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024554 prefixEnd_5024554 := by exact prefixLift 5024554
  have htrace : WordTrace (prefixWord ++ tailWord_5024554) baseStart_5024554 baseEnd_5024554 := by
    simpa [prefixWord, tailWord_5024554, baseEnd_5024554] using wordTrace_append hprefix tailTrace_5024554
  have hstable : (prefixWord ++ tailWord_5024554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024554).length < 2 ^ (prefixWord ++ tailWord_5024554).sum := by decide
  have hdescent : baseEnd_5024554 < baseStart_5024554 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024590 : List Nat := [4, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3]
def baseStart_5024590 : Nat := 118140960795 + 5024590 * 2 ^ 59
def prefixEnd_5024590 : Nat := 4983230072969 + 3 ^ 40 * 5024590 * 2
def baseEnd_5024590 : Nat := 2580029761774601502217337

theorem tailTrace_5024590 : CollatzResearch.WordTrace tailWord_5024590 prefixEnd_5024590 2580029761774601502217337 := by
  unfold tailWord_5024590
  simp only [CollatzResearch.WordTrace]
  refine ⟨22907731608347004562219903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 122174568577850690998506149 22907731608347004562219903)
  ·
    refine ⟨34361597412520506843329855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22907731608347004562219903 34361597412520506843329855)
    ·
      refine ⟨51542396118780760264994783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34361597412520506843329855 51542396118780760264994783)
      ·
        refine ⟨77313594178171140397492175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51542396118780760264994783 77313594178171140397492175)
        ·
          refine ⟨115970391267256710596238263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77313594178171140397492175 115970391267256710596238263)
          ·
            refine ⟨173955586900885065894357395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115970391267256710596238263 173955586900885065894357395)
            ·
              refine ⟨260933380351327598841536093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173955586900885065894357395 260933380351327598841536093)
              ·
                refine ⟨97850017631747849565576035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 260933380351327598841536093 97850017631747849565576035)
                ·
                  refine ⟨146775026447621774348364053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97850017631747849565576035 146775026447621774348364053)
                  ·
                    refine ⟨6880079364732270672579565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 146775026447621774348364053 6880079364732270672579565)
                    ·
                      refine ⟨2580029761774601502217337, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6880079364732270672579565 2580029761774601502217337)
                      ·
                        rfl

theorem cell23_5024590_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 3, 1, 6, 3].length) (baseStart_5024590 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024590 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024590 prefixEnd_5024590 := by exact prefixLift 5024590
  have htrace : WordTrace (prefixWord ++ tailWord_5024590) baseStart_5024590 baseEnd_5024590 := by
    simpa [prefixWord, tailWord_5024590, baseEnd_5024590] using wordTrace_append hprefix tailTrace_5024590
  have hstable : (prefixWord ++ tailWord_5024590).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024590).length < 2 ^ (prefixWord ++ tailWord_5024590).sum := by decide
  have hdescent : baseEnd_5024590 < baseStart_5024590 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024590) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024627 : List Nat := [1, 1, 1, 2, 2, 1, 7, 3, 5]
def baseStart_5024627 : Nat := 118140960795 + 5024627 * 2 ^ 59
def prefixEnd_5024627 : Nat := 4983230072969 + 3 ^ 40 * 5024627 * 2
def baseEnd_5024627 : Nat := 286672084506535317494963

theorem tailTrace_5024627 : CollatzResearch.WordTrace tailWord_5024627 prefixEnd_5024627 286672084506535317494963 := by
  unfold tailWord_5024627
  simp only [CollatzResearch.WordTrace]
  refine ⟨183263202367641991816856135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122175468245094661211237423 183263202367641991816856135)
  ·
    refine ⟨274894803551462987725284203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 183263202367641991816856135 274894803551462987725284203)
    ·
      refine ⟨412342205327194481587926305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 274894803551462987725284203 412342205327194481587926305)
      ·
        refine ⟨309256653995395861190944729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 412342205327194481587926305 309256653995395861190944729)
        ·
          refine ⟨231942490496546895893208547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 309256653995395861190944729 231942490496546895893208547)
          ·
            refine ⟨347913735744820343839812821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231942490496546895893208547 347913735744820343839812821)
            ·
              refine ⟨8154228181519226808745613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 347913735744820343839812821 8154228181519226808745613)
              ·
                refine ⟨3057835568069710053279605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8154228181519226808745613 3057835568069710053279605)
                ·
                  refine ⟨286672084506535317494963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3057835568069710053279605 286672084506535317494963)
                  ·
                    rfl

theorem cell23_5024627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 7, 3, 5].length) (baseStart_5024627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024627 prefixEnd_5024627 := by exact prefixLift 5024627
  have htrace : WordTrace (prefixWord ++ tailWord_5024627) baseStart_5024627 baseEnd_5024627 := by
    simpa [prefixWord, tailWord_5024627, baseEnd_5024627] using wordTrace_append hprefix tailTrace_5024627
  have hstable : (prefixWord ++ tailWord_5024627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024627).length < 2 ^ (prefixWord ++ tailWord_5024627).sum := by decide
  have hdescent : baseEnd_5024627 < baseStart_5024627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024674 : List Nat := [3, 3, 1, 2, 2, 2, 2, 1, 2, 5]
def baseStart_5024674 : Nat := 118140960795 + 5024674 * 2 ^ 59
def prefixEnd_5024674 : Nat := 4983230072969 + 3 ^ 40 * 5024674 * 2
def baseEnd_5024674 : Nat := 860024298049859724522317

theorem tailTrace_5024674 : CollatzResearch.WordTrace tailWord_5024674 prefixEnd_5024674 860024298049859724522317 := by
  unfold tailWord_5024674
  simp only [CollatzResearch.WordTrace]
  refine ⟨45816229149617929710954269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 122176611065647812562544717 45816229149617929710954269)
  ·
    refine ⟨17181085931106723641607851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45816229149617929710954269 17181085931106723641607851)
    ·
      refine ⟨25771628896660085462411777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17181085931106723641607851 25771628896660085462411777)
      ·
        refine ⟨19328721672495064096808833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25771628896660085462411777 19328721672495064096808833)
        ·
          refine ⟨14496541254371298072606625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19328721672495064096808833 14496541254371298072606625)
          ·
            refine ⟨10872405940778473554454969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14496541254371298072606625 10872405940778473554454969)
            ·
              refine ⟨8154304455583855165841227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10872405940778473554454969 8154304455583855165841227)
              ·
                refine ⟨12231456683375782748761841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8154304455583855165841227 12231456683375782748761841)
                ·
                  refine ⟨9173592512531837061571381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12231456683375782748761841 9173592512531837061571381)
                  ·
                    refine ⟨860024298049859724522317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9173592512531837061571381 860024298049859724522317)
                    ·
                      rfl

theorem cell23_5024674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 2, 1, 2, 5].length) (baseStart_5024674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024674 prefixEnd_5024674 := by exact prefixLift 5024674
  have htrace : WordTrace (prefixWord ++ tailWord_5024674) baseStart_5024674 baseEnd_5024674 := by
    simpa [prefixWord, tailWord_5024674, baseEnd_5024674] using wordTrace_append hprefix tailTrace_5024674
  have hstable : (prefixWord ++ tailWord_5024674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024674).length < 2 ^ (prefixWord ++ tailWord_5024674).sum := by decide
  have hdescent : baseEnd_5024674 < baseStart_5024674 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5024677 : List Nat := [1, 3, 1, 2, 1, 1, 1, 1, 6, 4, 2]
def baseStart_5024677 : Nat := 118140960795 + 5024677 * 2 ^ 59
def prefixEnd_5024677 : Nat := 4983230072969 + 3 ^ 40 * 5024677 * 2
def baseEnd_5024677 : Nat := 2580074434591542661829437

theorem tailTrace_5024677 : CollatzResearch.WordTrace tailWord_5024677 prefixEnd_5024677 2580074434591542661829437 := by
  unfold tailWord_5024677
  simp only [CollatzResearch.WordTrace]
  refine ⟨183265026017460850356176285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 122176684011640566904117523 183265026017460850356176285)
  ·
    refine ⟨68724384756547818883566107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 183265026017460850356176285 68724384756547818883566107)
    ·
      refine ⟨103086577134821728325349161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68724384756547818883566107 103086577134821728325349161)
      ·
        refine ⟨77314932851116296244011871, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 103086577134821728325349161 77314932851116296244011871)
        ·
          refine ⟨115972399276674444366017807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77314932851116296244011871 115972399276674444366017807)
          ·
            refine ⟨173958598915011666549026711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115972399276674444366017807 173958598915011666549026711)
            ·
              refine ⟨260937898372517499823540067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 173958598915011666549026711 260937898372517499823540067)
              ·
                refine ⟨391406847558776249735310101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 260937898372517499823540067 391406847558776249735310101)
                ·
                  refine ⟨18347195979317636706342661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 391406847558776249735310101 18347195979317636706342661)
                  ·
                    refine ⟨3440099246122056882439249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18347195979317636706342661 3440099246122056882439249)
                    ·
                      refine ⟨2580074434591542661829437, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3440099246122056882439249 2580074434591542661829437)
                      ·
                        rfl

theorem cell23_5024677_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 6, 4, 2].length) (baseStart_5024677 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5024677 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5024677 prefixEnd_5024677 := by exact prefixLift 5024677
  have htrace : WordTrace (prefixWord ++ tailWord_5024677) baseStart_5024677 baseEnd_5024677 := by
    simpa [prefixWord, tailWord_5024677, baseEnd_5024677] using wordTrace_append hprefix tailTrace_5024677
  have hstable : (prefixWord ++ tailWord_5024677).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5024677).length < 2 ^ (prefixWord ++ tailWord_5024677).sum := by decide
  have hdescent : baseEnd_5024677 < baseStart_5024677 := by decide
  rcases family_descends (prefixWord ++ tailWord_5024677) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
