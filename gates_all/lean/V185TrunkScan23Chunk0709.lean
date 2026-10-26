import V185TrunkScan23Chunk0708

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4190697 : List Nat := [1, 2, 1, 1, 1, 2, 1, 4, 4, 2, 4]
def baseStart_4190697 : Nat := 118140960795 + 4190697 * 2 ^ 59
def prefixEnd_4190697 : Nat := 4983230072969 + 3 ^ 40 * 4190697 * 2
def baseEnd_4190697 : Nat := 2151841838354895612414841

theorem tailTrace_4190697 : CollatzResearch.WordTrace tailWord_4190697 prefixEnd_4190697 2151841838354895612414841 := by
  unfold tailWord_4190697
  simp only [CollatzResearch.WordTrace]
  refine ⟨152847276498827957911802345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101898184332551971941201563 152847276498827957911802345)
  ·
    refine ⟨114635457374120968433851759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152847276498827957911802345 114635457374120968433851759)
    ·
      refine ⟨171953186061181452650777639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114635457374120968433851759 171953186061181452650777639)
      ·
        refine ⟨257929779091772178976166459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171953186061181452650777639 257929779091772178976166459)
        ·
          refine ⟨386894668637658268464249689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257929779091772178976166459 386894668637658268464249689)
          ·
            refine ⟨290171001478243701348187267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 386894668637658268464249689 290171001478243701348187267)
            ·
              refine ⟨435256502217365552022280901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290171001478243701348187267 435256502217365552022280901)
              ·
                refine ⟨81610594165756041004177669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 435256502217365552022280901 81610594165756041004177669)
                ·
                  refine ⟨15301986406079257688283313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81610594165756041004177669 15301986406079257688283313)
                  ·
                    refine ⟨11476489804559443266212485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15301986406079257688283313 11476489804559443266212485)
                    ·
                      refine ⟨2151841838354895612414841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11476489804559443266212485 2151841838354895612414841)
                      ·
                        rfl

theorem cell23_4190697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 4, 4, 2, 4].length) (baseStart_4190697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190697 prefixEnd_4190697 := by exact prefixLift 4190697
  have htrace : WordTrace (prefixWord ++ tailWord_4190697) baseStart_4190697 baseEnd_4190697 := by
    simpa [prefixWord, tailWord_4190697, baseEnd_4190697] using wordTrace_append hprefix tailTrace_4190697
  have hstable : (prefixWord ++ tailWord_4190697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190697).length < 2 ^ (prefixWord ++ tailWord_4190697).sum := by decide
  have hdescent : baseEnd_4190697 < baseStart_4190697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190717 : List Nat := [1, 4, 1, 1, 1, 3, 1, 1, 1, 2, 7]
def baseStart_4190717 : Nat := 118140960795 + 4190717 * 2 ^ 59
def prefixEnd_4190717 : Nat := 4983230072969 + 3 ^ 40 * 4190717 * 2
def baseEnd_4190717 : Nat := 2151852107967985534164749

theorem tailTrace_4190717 : CollatzResearch.WordTrace tailWord_4190717 prefixEnd_4190717 2151852107967985534164749 := by
  unfold tailWord_4190717
  simp only [CollatzResearch.WordTrace]
  refine ⟨152848005958755501327530405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101898670639170334218353603 152848005958755501327530405)
  ·
    refine ⟨28659001117266656498911951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152848005958755501327530405 28659001117266656498911951)
    ·
      refine ⟨42988501675899984748367927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28659001117266656498911951 42988501675899984748367927)
      ·
        refine ⟨64482752513849977122551891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42988501675899984748367927 64482752513849977122551891)
        ·
          refine ⟨96724128770774965683827837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64482752513849977122551891 96724128770774965683827837)
          ·
            refine ⟨36271548289040612131435439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96724128770774965683827837 36271548289040612131435439)
            ·
              refine ⟨54407322433560918197153159, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36271548289040612131435439 54407322433560918197153159)
              ·
                refine ⟨81610983650341377295729739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54407322433560918197153159 81610983650341377295729739)
                ·
                  refine ⟨122416475475512065943594609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81610983650341377295729739 122416475475512065943594609)
                  ·
                    refine ⟨91812356606634049457695957, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 122416475475512065943594609 91812356606634049457695957)
                    ·
                      refine ⟨2151852107967985534164749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91812356606634049457695957 2151852107967985534164749)
                      ·
                        rfl

theorem cell23_4190717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 2, 7].length) (baseStart_4190717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190717 prefixEnd_4190717 := by exact prefixLift 4190717
  have htrace : WordTrace (prefixWord ++ tailWord_4190717) baseStart_4190717 baseEnd_4190717 := by
    simpa [prefixWord, tailWord_4190717, baseEnd_4190717] using wordTrace_append hprefix tailTrace_4190717
  have hstable : (prefixWord ++ tailWord_4190717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190717).length < 2 ^ (prefixWord ++ tailWord_4190717).sum := by decide
  have hdescent : baseEnd_4190717 < baseStart_4190717 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190737 : List Nat := [1, 2, 2, 1, 1, 2, 2, 4, 1, 7]
def baseStart_4190737 : Nat := 118140960795 + 4190737 * 2 ^ 59
def prefixEnd_4190737 : Nat := 4983230072969 + 3 ^ 40 * 4190737 * 2
def baseEnd_4190737 : Nat := 717287459193691818638219

theorem tailTrace_4190737 : CollatzResearch.WordTrace tailWord_4190737 prefixEnd_4190737 717287459193691818638219 := by
  unfold tailWord_4190737
  simp only [CollatzResearch.WordTrace]
  refine ⟨152848735418683044743258465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101899156945788696495505643 152848735418683044743258465)
  ·
    refine ⟨114636551564012283557443849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152848735418683044743258465 114636551564012283557443849)
    ·
      refine ⟨85977413673009212668082887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114636551564012283557443849 85977413673009212668082887)
      ·
        refine ⟨128966120509513819002124331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85977413673009212668082887 128966120509513819002124331)
        ·
          refine ⟨193449180764270728503186497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128966120509513819002124331 193449180764270728503186497)
          ·
            refine ⟨145086885573203046377389873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193449180764270728503186497 145086885573203046377389873)
            ·
              refine ⟨108815164179902284783042405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145086885573203046377389873 108815164179902284783042405)
              ·
                refine ⟨20402843283731678396820451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108815164179902284783042405 20402843283731678396820451)
                ·
                  refine ⟨30604264925597517595230677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20402843283731678396820451 30604264925597517595230677)
                  ·
                    refine ⟨717287459193691818638219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30604264925597517595230677 717287459193691818638219)
                    ·
                      rfl

theorem cell23_4190737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 7].length) (baseStart_4190737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190737 prefixEnd_4190737 := by exact prefixLift 4190737
  have htrace : WordTrace (prefixWord ++ tailWord_4190737) baseStart_4190737 baseEnd_4190737 := by
    simpa [prefixWord, tailWord_4190737, baseEnd_4190737] using wordTrace_append hprefix tailTrace_4190737
  have hstable : (prefixWord ++ tailWord_4190737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190737).length < 2 ^ (prefixWord ++ tailWord_4190737).sum := by decide
  have hdescent : baseEnd_4190737 < baseStart_4190737 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190791 : List Nat := [1, 1, 4, 1, 4, 1, 1, 1, 1, 6, 2]
def baseStart_4190791 : Nat := 118140960795 + 4190791 * 2 ^ 59
def prefixEnd_4190791 : Nat := 4983230072969 + 3 ^ 40 * 4190791 * 2
def baseEnd_4190791 : Nat := 2151890105536418244639409

theorem tailTrace_4190791 : CollatzResearch.WordTrace tailWord_4190791 prefixEnd_4190791 2151890105536418244639409 := by
  unfold tailWord_4190791
  simp only [CollatzResearch.WordTrace]
  refine ⟨152850704960487411965724227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101900469973658274643816151 152850704960487411965724227)
  ·
    refine ⟨229276057440731117948586341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152850704960487411965724227 229276057440731117948586341)
    ·
      refine ⟨42989260770137084615359939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229276057440731117948586341 42989260770137084615359939)
      ·
        refine ⟨64483891155205626923039909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42989260770137084615359939 64483891155205626923039909)
        ·
          refine ⟨12090729591601055048069983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64483891155205626923039909 12090729591601055048069983)
          ·
            refine ⟨18136094387401582572104975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12090729591601055048069983 18136094387401582572104975)
            ·
              refine ⟨27204141581102373858157463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18136094387401582572104975 27204141581102373858157463)
              ·
                refine ⟨40806212371653560787236195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27204141581102373858157463 40806212371653560787236195)
                ·
                  refine ⟨61209318557480341180854293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40806212371653560787236195 61209318557480341180854293)
                  ·
                    refine ⟨2869186807381890992852545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61209318557480341180854293 2869186807381890992852545)
                    ·
                      refine ⟨2151890105536418244639409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2869186807381890992852545 2151890105536418244639409)
                      ·
                        rfl

theorem cell23_4190791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 1, 1, 6, 2].length) (baseStart_4190791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190791 prefixEnd_4190791 := by exact prefixLift 4190791
  have htrace : WordTrace (prefixWord ++ tailWord_4190791) baseStart_4190791 baseEnd_4190791 := by
    simpa [prefixWord, tailWord_4190791, baseEnd_4190791] using wordTrace_append hprefix tailTrace_4190791
  have hstable : (prefixWord ++ tailWord_4190791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190791).length < 2 ^ (prefixWord ++ tailWord_4190791).sum := by decide
  have hdescent : baseEnd_4190791 < baseStart_4190791 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190801 : List Nat := [1, 2, 2, 1, 3, 4, 1, 2, 3, 4]
def baseStart_4190801 : Nat := 118140960795 + 4190801 * 2 ^ 59
def prefixEnd_4190801 : Nat := 4983230072969 + 3 ^ 40 * 4190801 * 2
def baseEnd_4190801 : Nat := 717298413447654401838121

theorem tailTrace_4190801 : CollatzResearch.WordTrace tailWord_4190801 prefixEnd_4190801 717298413447654401838121 := by
  unfold tailWord_4190801
  simp only [CollatzResearch.WordTrace]
  refine ⟨152851069690451183673588257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101900713126967455782392171 152851069690451183673588257)
  ·
    refine ⟨114638302267838387755191193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152851069690451183673588257 114638302267838387755191193)
    ·
      refine ⟨85978726700878790816393395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114638302267838387755191193 85978726700878790816393395)
      ·
        refine ⟨128968090051318186224590093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85978726700878790816393395 128968090051318186224590093)
        ·
          refine ⟨48363033769244319834221285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128968090051318186224590093 48363033769244319834221285)
          ·
            refine ⟨9068068831733309968916491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48363033769244319834221285 9068068831733309968916491)
            ·
              refine ⟨13602103247599964953374737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9068068831733309968916491 13602103247599964953374737)
              ·
                refine ⟨10201577435699973715031053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13602103247599964953374737 10201577435699973715031053)
                ·
                  refine ⟨3825591538387490143136645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10201577435699973715031053 3825591538387490143136645)
                  ·
                    refine ⟨717298413447654401838121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3825591538387490143136645 717298413447654401838121)
                    ·
                      rfl

theorem cell23_4190801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 2, 3, 4].length) (baseStart_4190801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190801 prefixEnd_4190801 := by exact prefixLift 4190801
  have htrace : WordTrace (prefixWord ++ tailWord_4190801) baseStart_4190801 baseEnd_4190801 := by
    simpa [prefixWord, tailWord_4190801, baseEnd_4190801] using wordTrace_append hprefix tailTrace_4190801
  have hstable : (prefixWord ++ tailWord_4190801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190801).length < 2 ^ (prefixWord ++ tailWord_4190801).sum := by decide
  have hdescent : baseEnd_4190801 < baseStart_4190801 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190844 : List Nat := [2, 2, 2, 1, 1, 2, 2, 1, 5, 5]
def baseStart_4190844 : Nat := 118140960795 + 4190844 * 2 ^ 59
def prefixEnd_4190844 : Nat := 4983230072969 + 3 ^ 40 * 4190844 * 2
def baseEnd_4190844 : Nat := 717305773337035512425555

theorem tailTrace_4190844 : CollatzResearch.WordTrace tailWord_4190844 prefixEnd_4190844 717305773337035512425555 := by
  unfold tailWord_4190844
  simp only [CollatzResearch.WordTrace]
  refine ⟨76426319014647701008701793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101901758686196934678269057 76426319014647701008701793)
  ·
    refine ⟨57319739260985775756526345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76426319014647701008701793 57319739260985775756526345)
    ·
      refine ⟨42989804445739331817394759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57319739260985775756526345 42989804445739331817394759)
      ·
        refine ⟨64484706668608997726092139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42989804445739331817394759 64484706668608997726092139)
        ·
          refine ⟨96727060002913496589138209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64484706668608997726092139 96727060002913496589138209)
          ·
            refine ⟨72545295002185122441853657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96727060002913496589138209 72545295002185122441853657)
            ·
              refine ⟨54408971251638841831390243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72545295002185122441853657 54408971251638841831390243)
              ·
                refine ⟨81613456877458262747085365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54408971251638841831390243 81613456877458262747085365)
                ·
                  refine ⟨7651261582261712132539253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81613456877458262747085365 7651261582261712132539253)
                  ·
                    refine ⟨717305773337035512425555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7651261582261712132539253 717305773337035512425555)
                    ·
                      rfl

theorem cell23_4190844_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_4190844 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190844 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190844 prefixEnd_4190844 := by exact prefixLift 4190844
  have htrace : WordTrace (prefixWord ++ tailWord_4190844) baseStart_4190844 baseEnd_4190844 := by
    simpa [prefixWord, tailWord_4190844, baseEnd_4190844] using wordTrace_append hprefix tailTrace_4190844
  have hstable : (prefixWord ++ tailWord_4190844).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190844).length < 2 ^ (prefixWord ++ tailWord_4190844).sum := by decide
  have hdescent : baseEnd_4190844 < baseStart_4190844 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190844) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190851 : List Nat := [1, 1, 1, 3, 3, 1, 3, 2, 1, 5, 2]
def baseStart_4190851 : Nat := 118140960795 + 4190851 * 2 ^ 59
def prefixEnd_4190851 : Nat := 4983230072969 + 3 ^ 40 * 4190851 * 2
def baseEnd_4190851 : Nat := 2151920914375688009889133

theorem tailTrace_4190851 : CollatzResearch.WordTrace tailWord_4190851 prefixEnd_4190851 2151920914375688009889133 := by
  unfold tailWord_4190851
  simp only [CollatzResearch.WordTrace]
  refine ⟨152852893340270042212908407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101901928893513361475272271 152852893340270042212908407)
  ·
    refine ⟨229279340010405063319362611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152852893340270042212908407 229279340010405063319362611)
    ·
      refine ⟨343919010015607594979043917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229279340010405063319362611 343919010015607594979043917)
      ·
        refine ⟨128969628755852848117141469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 343919010015607594979043917 128969628755852848117141469)
        ·
          refine ⟨48363610783444818043928051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 128969628755852848117141469 48363610783444818043928051)
          ·
            refine ⟨72545416175167227065892077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48363610783444818043928051 72545416175167227065892077)
            ·
              refine ⟨27204531065687710149709529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72545416175167227065892077 27204531065687710149709529)
              ·
                refine ⟨20403398299265782612282147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27204531065687710149709529 20403398299265782612282147)
                ·
                  refine ⟨30605097448898673918423221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20403398299265782612282147 30605097448898673918423221)
                  ·
                    refine ⟨2869227885834250679852177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30605097448898673918423221 2869227885834250679852177)
                    ·
                      refine ⟨2151920914375688009889133, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2869227885834250679852177 2151920914375688009889133)
                      ·
                        rfl

theorem cell23_4190851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 3, 2, 1, 5, 2].length) (baseStart_4190851 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190851 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190851 prefixEnd_4190851 := by exact prefixLift 4190851
  have htrace : WordTrace (prefixWord ++ tailWord_4190851) baseStart_4190851 baseEnd_4190851 := by
    simpa [prefixWord, tailWord_4190851, baseEnd_4190851] using wordTrace_append hprefix tailTrace_4190851
  have hstable : (prefixWord ++ tailWord_4190851).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190851).length < 2 ^ (prefixWord ++ tailWord_4190851).sum := by decide
  have hdescent : baseEnd_4190851 < baseStart_4190851 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190878 : List Nat := [4, 3, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_4190878 : Nat := 118140960795 + 4190878 * 2 ^ 59
def prefixEnd_4190878 : Nat := 4983230072969 + 3 ^ 40 * 4190878 * 2
def baseEnd_4190878 : Nat := 717311592784453134750503

theorem tailTrace_4190878 : CollatzResearch.WordTrace tailWord_4190878 prefixEnd_4190878 717311592784453134750503 := by
  unfold tailWord_4190878
  simp only [CollatzResearch.WordTrace]
  refine ⟨19106734763896528228017661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101902585407448150549427525 19106734763896528228017661)
  ·
    refine ⟨7165025536461198085506623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19106734763896528228017661 7165025536461198085506623)
    ·
      refine ⟨10747538304691797128259935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7165025536461198085506623 10747538304691797128259935)
      ·
        refine ⟨16121307457037695692389903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10747538304691797128259935 16121307457037695692389903)
        ·
          refine ⟨24181961185556543538584855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16121307457037695692389903 24181961185556543538584855)
          ·
            refine ⟨36272941778334815307877283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24181961185556543538584855 36272941778334815307877283)
            ·
              refine ⟨54409412667502222961815925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36272941778334815307877283 54409412667502222961815925)
              ·
                refine ⟨5100882437578333402670243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54409412667502222961815925 5100882437578333402670243)
                ·
                  refine ⟨7651323656367500104005365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5100882437578333402670243 7651323656367500104005365)
                  ·
                    refine ⟨717311592784453134750503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7651323656367500104005365 717311592784453134750503)
                    ·
                      rfl

theorem cell23_4190878_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_4190878 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190878 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190878 prefixEnd_4190878 := by exact prefixLift 4190878
  have htrace : WordTrace (prefixWord ++ tailWord_4190878) baseStart_4190878 baseEnd_4190878 := by
    simpa [prefixWord, tailWord_4190878, baseEnd_4190878] using wordTrace_append hprefix tailTrace_4190878
  have hstable : (prefixWord ++ tailWord_4190878).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190878).length < 2 ^ (prefixWord ++ tailWord_4190878).sum := by decide
  have hdescent : baseEnd_4190878 < baseStart_4190878 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190878) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190908 : List Nat := [2, 2, 2, 3, 1, 1, 3, 3, 2, 4]
def baseStart_4190908 : Nat := 118140960795 + 4190908 * 2 ^ 59
def prefixEnd_4190908 : Nat := 4983230072969 + 3 ^ 40 * 4190908 * 2
def baseEnd_4190908 : Nat := 717316727590998095625457

theorem tailTrace_4190908 : CollatzResearch.WordTrace tailWord_4190908 prefixEnd_4190908 717316727590998095625457 := by
  unfold tailWord_4190908
  simp only [CollatzResearch.WordTrace]
  refine ⟨76427486150531770473866689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101903314867375693965155585 76427486150531770473866689)
  ·
    refine ⟨57320614612898827855400017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76427486150531770473866689 57320614612898827855400017)
    ·
      refine ⟨42990460959674120891550013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57320614612898827855400017 42990460959674120891550013)
      ·
        refine ⟨16121422859877795334331255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 42990460959674120891550013 16121422859877795334331255)
        ·
          refine ⟨24182134289816693001496883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16121422859877795334331255 24182134289816693001496883)
          ·
            refine ⟨36273201434725039502245325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24182134289816693001496883 36273201434725039502245325)
            ·
              refine ⟨13602450538021889813341997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36273201434725039502245325 13602450538021889813341997)
              ·
                refine ⟨5100918951758208680003249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13602450538021889813341997 5100918951758208680003249)
                ·
                  refine ⟨3825689213818656510002437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5100918951758208680003249 3825689213818656510002437)
                  ·
                    refine ⟨717316727590998095625457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3825689213818656510002437 717316727590998095625457)
                    ·
                      rfl

theorem cell23_4190908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_4190908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190908 prefixEnd_4190908 := by exact prefixLift 4190908
  have htrace : WordTrace (prefixWord ++ tailWord_4190908) baseStart_4190908 baseEnd_4190908 := by
    simpa [prefixWord, tailWord_4190908, baseEnd_4190908] using wordTrace_append hprefix tailTrace_4190908
  have hstable : (prefixWord ++ tailWord_4190908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190908).length < 2 ^ (prefixWord ++ tailWord_4190908).sum := by decide
  have hdescent : baseEnd_4190908 < baseStart_4190908 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190925 : List Nat := [1, 6, 2, 1, 2, 1, 1, 2, 1, 6]
def baseStart_4190925 : Nat := 118140960795 + 4190925 * 2 ^ 59
def prefixEnd_4190925 : Nat := 4983230072969 + 3 ^ 40 * 4190925 * 2
def baseEnd_4190925 : Nat := 717319637314706906787931

theorem tailTrace_4190925 : CollatzResearch.WordTrace tailWord_4190925 prefixEnd_4190925 717319637314706906787931 := by
  unfold tailWord_4190925
  simp only [CollatzResearch.WordTrace]
  refine ⟨152855592342001952851102229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101903728228001301900734819 152855592342001952851102229)
  ·
    refine ⟨7165105891031341539895417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152855592342001952851102229 7165105891031341539895417)
    ·
      refine ⟨5373829418273506154921563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7165105891031341539895417 5373829418273506154921563)
      ·
        refine ⟨8060744127410259232382345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5373829418273506154921563 8060744127410259232382345)
        ·
          refine ⟨6045558095557694424286759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8060744127410259232382345 6045558095557694424286759)
          ·
            refine ⟨9068337143336541636430139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6045558095557694424286759 9068337143336541636430139)
            ·
              refine ⟨13602505715004812454645209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9068337143336541636430139 13602505715004812454645209)
              ·
                refine ⟨10201879286253609340983907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13602505715004812454645209 10201879286253609340983907)
                ·
                  refine ⟨15302818929380414011475861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10201879286253609340983907 15302818929380414011475861)
                  ·
                    refine ⟨717319637314706906787931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15302818929380414011475861 717319637314706906787931)
                    ·
                      rfl

theorem cell23_4190925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 1, 2, 1, 6].length) (baseStart_4190925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190925 prefixEnd_4190925 := by exact prefixLift 4190925
  have htrace : WordTrace (prefixWord ++ tailWord_4190925) baseStart_4190925 baseEnd_4190925 := by
    simpa [prefixWord, tailWord_4190925, baseEnd_4190925] using wordTrace_append hprefix tailTrace_4190925
  have hstable : (prefixWord ++ tailWord_4190925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190925).length < 2 ^ (prefixWord ++ tailWord_4190925).sum := by decide
  have hdescent : baseEnd_4190925 < baseStart_4190925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190932 : List Nat := [2, 4, 1, 3, 2, 1, 3, 1, 1, 1, 4]
def baseStart_4190932 : Nat := 118140960795 + 4190932 * 2 ^ 59
def prefixEnd_4190932 : Nat := 4983230072969 + 3 ^ 40 * 4190932 * 2
def baseEnd_4190932 : Nat := 2151962506308702192976261

theorem tailTrace_4190932 : CollatzResearch.WordTrace tailWord_4190932 prefixEnd_4190932 2151962506308702192976261 := by
  unfold tailWord_4190932
  simp only [CollatzResearch.WordTrace]
  refine ⟨76427923826488296523303525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101903898435317728697738033 76427923826488296523303525)
  ·
    refine ⟨14330235717466555598119411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76427923826488296523303525 14330235717466555598119411)
    ·
      refine ⟨21495353576199833397179117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14330235717466555598119411 21495353576199833397179117)
      ·
        refine ⟨8060757591074937523942169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21495353576199833397179117 8060757591074937523942169)
        ·
          refine ⟨6045568193306203142956627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8060757591074937523942169 6045568193306203142956627)
          ·
            refine ⟨9068352289959304714434941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6045568193306203142956627 9068352289959304714434941)
            ·
              refine ⟨3400632108734739267913103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9068352289959304714434941 3400632108734739267913103)
              ·
                refine ⟨5100948163102108901869655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3400632108734739267913103 5100948163102108901869655)
                ·
                  refine ⟨7651422244653163352804483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5100948163102108901869655 7651422244653163352804483)
                  ·
                    refine ⟨11477133366979745029206725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7651422244653163352804483 11477133366979745029206725)
                    ·
                      refine ⟨2151962506308702192976261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11477133366979745029206725 2151962506308702192976261)
                      ·
                        rfl

theorem cell23_4190932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 1, 3, 1, 1, 1, 4].length) (baseStart_4190932 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190932 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190932 prefixEnd_4190932 := by exact prefixLift 4190932
  have htrace : WordTrace (prefixWord ++ tailWord_4190932) baseStart_4190932 baseEnd_4190932 := by
    simpa [prefixWord, tailWord_4190932, baseEnd_4190932] using wordTrace_append hprefix tailTrace_4190932
  have hstable : (prefixWord ++ tailWord_4190932).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190932).length < 2 ^ (prefixWord ++ tailWord_4190932).sum := by decide
  have hdescent : baseEnd_4190932 < baseStart_4190932 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190935 : List Nat := [1, 1, 3, 2, 1, 5, 3, 1, 1, 2, 3]
def baseStart_4190935 : Nat := 118140960795 + 4190935 * 2 ^ 59
def prefixEnd_4190935 : Nat := 4983230072969 + 3 ^ 40 * 4190935 * 2
def baseEnd_4190935 : Nat := 2151964046750665681238747

theorem tailTrace_4190935 : CollatzResearch.WordTrace tailWord_4190935 prefixEnd_4190935 2151964046750665681238747 := by
  unfold tailWord_4190935
  simp only [CollatzResearch.WordTrace]
  refine ⟨152855957071965724558966259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101903971381310483039310839 152855957071965724558966259)
  ·
    refine ⟨229283935607948586838449389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152855957071965724558966259 229283935607948586838449389)
    ·
      refine ⟨85981475852980720064418521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229283935607948586838449389 85981475852980720064418521)
      ·
        refine ⟨64486106889735540048313891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 85981475852980720064418521 64486106889735540048313891)
        ·
          refine ⟨96729160334603310072470837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64486106889735540048313891 96729160334603310072470837)
          ·
            refine ⟨9068358781369060319294141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96729160334603310072470837 9068358781369060319294141)
            ·
              refine ⟨3400634543013397619735303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9068358781369060319294141 3400634543013397619735303)
              ·
                refine ⟨5100951814520096429602955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3400634543013397619735303 5100951814520096429602955)
                ·
                  refine ⟨7651427721780144644404433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5100951814520096429602955 7651427721780144644404433)
                  ·
                    refine ⟨5738570791335108483303325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7651427721780144644404433 5738570791335108483303325)
                    ·
                      refine ⟨2151964046750665681238747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5738570791335108483303325 2151964046750665681238747)
                      ·
                        rfl

theorem cell23_4190935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 5, 3, 1, 1, 2, 3].length) (baseStart_4190935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190935 prefixEnd_4190935 := by exact prefixLift 4190935
  have htrace : WordTrace (prefixWord ++ tailWord_4190935) baseStart_4190935 baseEnd_4190935 := by
    simpa [prefixWord, tailWord_4190935, baseEnd_4190935] using wordTrace_append hprefix tailTrace_4190935
  have hstable : (prefixWord ++ tailWord_4190935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190935).length < 2 ^ (prefixWord ++ tailWord_4190935).sum := by decide
  have hdescent : baseEnd_4190935 < baseStart_4190935 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190949 : List Nat := [1, 3, 1, 4, 1, 2, 4, 2, 1, 2, 2]
def baseStart_4190949 : Nat := 118140960795 + 4190949 * 2 ^ 59
def prefixEnd_4190949 : Nat := 4983230072969 + 3 ^ 40 * 4190949 * 2
def baseEnd_4190949 : Nat := 2151971235479828626463683

theorem tailTrace_4190949 : CollatzResearch.WordTrace tailWord_4190949 prefixEnd_4190949 2151971235479828626463683 := by
  unfold tailWord_4190949
  simp only [CollatzResearch.WordTrace]
  refine ⟨152856467693915004949975901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101904311795943336633317267 152856467693915004949975901)
  ·
    refine ⟨57321175385218126856240963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152856467693915004949975901 57321175385218126856240963)
    ·
      refine ⟨85981763077827190284361445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57321175385218126856240963 85981763077827190284361445)
      ·
        refine ⟨16121580577092598178317771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85981763077827190284361445 16121580577092598178317771)
        ·
          refine ⟨24182370865638897267476657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16121580577092598178317771 24182370865638897267476657)
          ·
            refine ⟨18136778149229172950607493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24182370865638897267476657 18136778149229172950607493)
            ·
              refine ⟨3400645902980469928238905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18136778149229172950607493 3400645902980469928238905)
              ·
                refine ⟨2550484427235352446179179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3400645902980469928238905 2550484427235352446179179)
                ·
                  refine ⟨3825726640853028669268769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2550484427235352446179179 3825726640853028669268769)
                  ·
                    refine ⟨2869294980639771501951577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3825726640853028669268769 2869294980639771501951577)
                    ·
                      refine ⟨2151971235479828626463683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2869294980639771501951577 2151971235479828626463683)
                      ·
                        rfl

theorem cell23_4190949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_4190949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190949 prefixEnd_4190949 := by exact prefixLift 4190949
  have htrace : WordTrace (prefixWord ++ tailWord_4190949) baseStart_4190949 baseEnd_4190949 := by
    simpa [prefixWord, tailWord_4190949, baseEnd_4190949] using wordTrace_append hprefix tailTrace_4190949
  have hstable : (prefixWord ++ tailWord_4190949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190949).length < 2 ^ (prefixWord ++ tailWord_4190949).sum := by decide
  have hdescent : baseEnd_4190949 < baseStart_4190949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4190999 : List Nat := [1, 1, 3, 4, 4, 1, 1, 2, 2, 1, 3]
def baseStart_4190999 : Nat := 118140960795 + 4190999 * 2 ^ 59
def prefixEnd_4190999 : Nat := 4983230072969 + 3 ^ 40 * 4190999 * 2
def baseEnd_4190999 : Nat := 2151996909512553430838453

theorem tailTrace_4190999 : CollatzResearch.WordTrace tailWord_4190999 prefixEnd_4190999 2151996909512553430838453 := by
  unfold tailWord_4190999
  simp only [CollatzResearch.WordTrace]
  refine ⟨152858291343733863489296051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101905527562489242326197367 152858291343733863489296051)
  ·
    refine ⟨229287437015600795233944077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152858291343733863489296051 229287437015600795233944077)
    ·
      refine ⟨85982788880850298212729029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229287437015600795233944077 85982788880850298212729029)
      ·
        refine ⟨16121772915159430914886693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 85982788880850298212729029 16121772915159430914886693)
        ·
          refine ⟨3022832421592393296541255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16121772915159430914886693 3022832421592393296541255)
          ·
            refine ⟨4534248632388589944811883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3022832421592393296541255 4534248632388589944811883)
            ·
              refine ⟨6801372948582884917217825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4534248632388589944811883 6801372948582884917217825)
              ·
                refine ⟨5101029711437163687913369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6801372948582884917217825 5101029711437163687913369)
                ·
                  refine ⟨3825772283577872765935027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5101029711437163687913369 3825772283577872765935027)
                  ·
                    refine ⟨5738658425366809148902541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3825772283577872765935027 5738658425366809148902541)
                    ·
                      refine ⟨2151996909512553430838453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5738658425366809148902541 2151996909512553430838453)
                      ·
                        rfl

theorem cell23_4190999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 4, 1, 1, 2, 2, 1, 3].length) (baseStart_4190999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4190999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4190999 prefixEnd_4190999 := by exact prefixLift 4190999
  have htrace : WordTrace (prefixWord ++ tailWord_4190999) baseStart_4190999 baseEnd_4190999 := by
    simpa [prefixWord, tailWord_4190999, baseEnd_4190999] using wordTrace_append hprefix tailTrace_4190999
  have hstable : (prefixWord ++ tailWord_4190999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4190999).length < 2 ^ (prefixWord ++ tailWord_4190999).sum := by decide
  have hdescent : baseEnd_4190999 < baseStart_4190999 := by decide
  rcases family_descends (prefixWord ++ tailWord_4190999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191022 : List Nat := [4, 1, 3, 2, 1, 1, 3, 1, 1, 4, 2]
def baseStart_4191022 : Nat := 118140960795 + 4191022 * 2 ^ 59
def prefixEnd_4191022 : Nat := 4983230072969 + 3 ^ 40 * 4191022 * 2
def baseEnd_4191022 : Nat := 2152008719567606840850847

theorem tailTrace_4191022 : CollatzResearch.WordTrace tailWord_4191022 prefixEnd_4191022 2152008719567606840850847 := by
  unfold tailWord_4191022
  simp only [CollatzResearch.WordTrace]
  refine ⟨19107391277831317302172915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101906086815100358944922213 19107391277831317302172915)
  ·
    refine ⟨28661086916746975953259373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19107391277831317302172915 28661086916746975953259373)
    ·
      refine ⟨10747907593780115982472265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28661086916746975953259373 10747907593780115982472265)
      ·
        refine ⟨8060930695335086986854199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10747907593780115982472265 8060930695335086986854199)
        ·
          refine ⟨12091396043002630480281299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8060930695335086986854199 12091396043002630480281299)
          ·
            refine ⟨18137094064503945720421949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12091396043002630480281299 18137094064503945720421949)
            ·
              refine ⟨6801410274188979645158231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18137094064503945720421949 6801410274188979645158231)
              ·
                refine ⟨10202115411283469467737347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6801410274188979645158231 10202115411283469467737347)
                ·
                  refine ⟨15303173116925204201606021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10202115411283469467737347 15303173116925204201606021)
                  ·
                    refine ⟨2869344959423475787801129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15303173116925204201606021 2869344959423475787801129)
                    ·
                      refine ⟨2152008719567606840850847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2869344959423475787801129 2152008719567606840850847)
                      ·
                        rfl

theorem cell23_4191022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 3, 1, 1, 4, 2].length) (baseStart_4191022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191022 prefixEnd_4191022 := by exact prefixLift 4191022
  have htrace : WordTrace (prefixWord ++ tailWord_4191022) baseStart_4191022 baseEnd_4191022 := by
    simpa [prefixWord, tailWord_4191022, baseEnd_4191022] using wordTrace_append hprefix tailTrace_4191022
  have hstable : (prefixWord ++ tailWord_4191022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191022).length < 2 ^ (prefixWord ++ tailWord_4191022).sum := by decide
  have hdescent : baseEnd_4191022 < baseStart_4191022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191058 : List Nat := [3, 2, 2, 1, 1, 2, 3, 2, 2, 5]
def baseStart_4191058 : Nat := 118140960795 + 4191058 * 2 ^ 59
def prefixEnd_4191058 : Nat := 4983230072969 + 3 ^ 40 * 4191058 * 2
def baseEnd_4191058 : Nat := 717342401623722900000227

theorem tailTrace_4191058 : CollatzResearch.WordTrace tailWord_4191058 prefixEnd_4191058 717342401623722900000227 := by
  unfold tailWord_4191058
  simp only [CollatzResearch.WordTrace]
  refine ⟨38215110812630029141423457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101906962167013411043795885 38215110812630029141423457)
  ·
    refine ⟨28661333109472521856067593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38215110812630029141423457 28661333109472521856067593)
    ·
      refine ⟨21495999832104391392050695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28661333109472521856067593 21495999832104391392050695)
      ·
        refine ⟨32243999748156587088076043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21495999832104391392050695 32243999748156587088076043)
        ·
          refine ⟨48365999622234880632114065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32243999748156587088076043 48365999622234880632114065)
          ·
            refine ⟨36274499716676160474085549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48365999622234880632114065 36274499716676160474085549)
            ·
              refine ⟨13602937393753560177782081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36274499716676160474085549 13602937393753560177782081)
              ·
                refine ⟨10202203045315170133336561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13602937393753560177782081 10202203045315170133336561)
                ·
                  refine ⟨7651652283986377600002421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10202203045315170133336561 7651652283986377600002421)
                  ·
                    refine ⟨717342401623722900000227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7651652283986377600002421 717342401623722900000227)
                    ·
                      rfl

theorem cell23_4191058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_4191058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191058 prefixEnd_4191058 := by exact prefixLift 4191058
  have htrace : WordTrace (prefixWord ++ tailWord_4191058) baseStart_4191058 baseEnd_4191058 := by
    simpa [prefixWord, tailWord_4191058, baseEnd_4191058] using wordTrace_append hprefix tailTrace_4191058
  have hstable : (prefixWord ++ tailWord_4191058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191058).length < 2 ^ (prefixWord ++ tailWord_4191058).sum := by decide
  have hdescent : baseEnd_4191058 < baseStart_4191058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191068 : List Nat := [2, 2, 4, 2, 1, 1, 1, 1, 1, 1, 7]
def baseStart_4191068 : Nat := 118140960795 + 4191068 * 2 ^ 59
def prefixEnd_4191068 : Nat := 4983230072969 + 3 ^ 40 * 4191068 * 2
def baseEnd_4191068 : Nat := 2152032339677713660875635

theorem tailTrace_4191068 : CollatzResearch.WordTrace tailWord_4191068 prefixEnd_4191068 2152032339677713660875635 := by
  unfold tailWord_4191068
  simp only [CollatzResearch.WordTrace]
  refine ⟨76430403990241944136778929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101907205320322592182371905 76430403990241944136778929)
  ·
    refine ⟨57322802992681458102584197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76430403990241944136778929 57322802992681458102584197)
    ·
      refine ⟨10748025561127773394234537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57322802992681458102584197 10748025561127773394234537)
      ·
        refine ⟨8061019170845830045675903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10748025561127773394234537 8061019170845830045675903)
        ·
          refine ⟨12091528756268745068513855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8061019170845830045675903 12091528756268745068513855)
          ·
            refine ⟨18137293134403117602770783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12091528756268745068513855 18137293134403117602770783)
            ·
              refine ⟨27205939701604676404156175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18137293134403117602770783 27205939701604676404156175)
              ·
                refine ⟨40808909552407014606234263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27205939701604676404156175 40808909552407014606234263)
                ·
                  refine ⟨61213364328610521909351395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40808909552407014606234263 61213364328610521909351395)
                  ·
                    refine ⟨91820046492915782864027093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61213364328610521909351395 91820046492915782864027093)
                    ·
                      refine ⟨2152032339677713660875635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91820046492915782864027093 2152032339677713660875635)
                      ·
                        rfl

theorem cell23_4191068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 1, 1, 1, 1, 1, 7].length) (baseStart_4191068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191068 prefixEnd_4191068 := by exact prefixLift 4191068
  have htrace : WordTrace (prefixWord ++ tailWord_4191068) baseStart_4191068 baseEnd_4191068 := by
    simpa [prefixWord, tailWord_4191068, baseEnd_4191068] using wordTrace_append hprefix tailTrace_4191068
  have hstable : (prefixWord ++ tailWord_4191068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191068).length < 2 ^ (prefixWord ++ tailWord_4191068).sum := by decide
  have hdescent : baseEnd_4191068 < baseStart_4191068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191088 : List Nat := [2, 1, 1, 1, 4, 1, 2, 4, 3, 4]
def baseStart_4191088 : Nat := 118140960795 + 4191088 * 2 ^ 59
def prefixEnd_4191088 : Nat := 4983230072969 + 3 ^ 40 * 4191088 * 2
def baseEnd_4191088 : Nat := 717347536430267860875181

theorem tailTrace_4191088 : CollatzResearch.WordTrace tailWord_4191088 prefixEnd_4191088 717347536430267860875181 := by
  unfold tailWord_4191088
  simp only [CollatzResearch.WordTrace]
  refine ⟨76430768720205715844642959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101907691626940954459523945 76430768720205715844642959)
  ·
    refine ⟨114646153080308573766964439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76430768720205715844642959 114646153080308573766964439)
    ·
      refine ⟨171969229620462860650446659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114646153080308573766964439 171969229620462860650446659)
      ·
        refine ⟨257953844430694290975669989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171969229620462860650446659 257953844430694290975669989)
        ·
          refine ⟨48366345830755179557938123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 257953844430694290975669989 48366345830755179557938123)
          ·
            refine ⟨72549518746132769336907185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48366345830755179557938123 72549518746132769336907185)
            ·
              refine ⟨54412139059599577002680389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72549518746132769336907185 54412139059599577002680389)
              ·
                refine ⟨10202276073674920688002573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54412139059599577002680389 10202276073674920688002573)
                ·
                  refine ⟨3825853527628095258000965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10202276073674920688002573 3825853527628095258000965)
                  ·
                    refine ⟨717347536430267860875181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3825853527628095258000965 717347536430267860875181)
                    ·
                      rfl

theorem cell23_4191088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 4, 3, 4].length) (baseStart_4191088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191088 prefixEnd_4191088 := by exact prefixLift 4191088
  have htrace : WordTrace (prefixWord ++ tailWord_4191088) baseStart_4191088 baseEnd_4191088 := by
    simpa [prefixWord, tailWord_4191088, baseEnd_4191088] using wordTrace_append hprefix tailTrace_4191088
  have hstable : (prefixWord ++ tailWord_4191088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191088).length < 2 ^ (prefixWord ++ tailWord_4191088).sum := by decide
  have hdescent : baseEnd_4191088 < baseStart_4191088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191091 : List Nat := [1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 4]
def baseStart_4191091 : Nat := 118140960795 + 4191091 * 2 ^ 59
def prefixEnd_4191091 : Nat := 4983230072969 + 3 ^ 40 * 4191091 * 2
def baseEnd_4191091 : Nat := 2152044149732767070888029

theorem tailTrace_4191091 : CollatzResearch.WordTrace tailWord_4191091 prefixEnd_4191091 2152044149732767070888029 := by
  unfold tailWord_4191091
  simp only [CollatzResearch.WordTrace]
  refine ⟨152861646859400563201645127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101907764572933708801096751 152861646859400563201645127)
  ·
    refine ⟨229292470289100844802467691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152861646859400563201645127 229292470289100844802467691)
    ·
      refine ⟨343938705433651267203701537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229292470289100844802467691 343938705433651267203701537)
      ·
        refine ⟨257954029075238450402776153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343938705433651267203701537 257954029075238450402776153)
        ·
          refine ⟨193465521806428837802082115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257954029075238450402776153 193465521806428837802082115)
          ·
            refine ⟨290198282709643256703123173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193465521806428837802082115 290198282709643256703123173)
            ·
              refine ⟨54412178008058110631835595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 290198282709643256703123173 54412178008058110631835595)
              ·
                refine ⟨81618267012087165947753393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54412178008058110631835595 81618267012087165947753393)
                ·
                  refine ⟨61213700259065374460815045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81618267012087165947753393 61213700259065374460815045)
                  ·
                    refine ⟨11477568798574757711402821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61213700259065374460815045 11477568798574757711402821)
                    ·
                      refine ⟨2152044149732767070888029, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11477568798574757711402821 2152044149732767070888029)
                      ·
                        rfl

theorem cell23_4191091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 4, 1, 2, 4, 4].length) (baseStart_4191091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191091 prefixEnd_4191091 := by exact prefixLift 4191091
  have htrace : WordTrace (prefixWord ++ tailWord_4191091) baseStart_4191091 baseEnd_4191091 := by
    simpa [prefixWord, tailWord_4191091, baseEnd_4191091] using wordTrace_append hprefix tailTrace_4191091
  have hstable : (prefixWord ++ tailWord_4191091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191091).length < 2 ^ (prefixWord ++ tailWord_4191091).sum := by decide
  have hdescent : baseEnd_4191091 < baseStart_4191091 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191101 : List Nat := [1, 4, 1, 1, 2, 1, 2, 1, 10]
def baseStart_4191101 : Nat := 118140960795 + 4191101 * 2 ^ 59
def prefixEnd_4191101 : Nat := 4983230072969 + 3 ^ 40 * 4191101 * 2
def baseEnd_4191101 : Nat := 239116587171034670195887

theorem tailTrace_4191101 : CollatzResearch.WordTrace tailWord_4191101 prefixEnd_4191101 239116587171034670195887 := by
  unfold tailWord_4191101
  simp only [CollatzResearch.WordTrace]
  refine ⟨152862011589364334909509157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101908007726242889939672771 152862011589364334909509157)
  ·
    refine ⟨28661627173005812795532967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152862011589364334909509157 28661627173005812795532967)
    ·
      refine ⟨42992440759508719193299451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28661627173005812795532967 42992440759508719193299451)
      ·
        refine ⟨64488661139263078789949177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42992440759508719193299451 64488661139263078789949177)
        ·
          refine ⟨48366495854447309092461883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64488661139263078789949177 48366495854447309092461883)
          ·
            refine ⟨72549743781670963638692825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48366495854447309092461883 72549743781670963638692825)
            ·
              refine ⟨54412307836253222729019619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72549743781670963638692825 54412307836253222729019619)
              ·
                refine ⟨81618461754379834093529429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54412307836253222729019619 81618461754379834093529429)
                ·
                  refine ⟨239116587171034670195887, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 81618461754379834093529429 239116587171034670195887)
                  ·
                    rfl

theorem cell23_4191101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 2, 1, 10].length) (baseStart_4191101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191101 prefixEnd_4191101 := by exact prefixLift 4191101
  have htrace : WordTrace (prefixWord ++ tailWord_4191101) baseStart_4191101 baseEnd_4191101 := by
    simpa [prefixWord, tailWord_4191101, baseEnd_4191101] using wordTrace_append hprefix tailTrace_4191101
  have hstable : (prefixWord ++ tailWord_4191101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191101).length < 2 ^ (prefixWord ++ tailWord_4191101).sum := by decide
  have hdescent : baseEnd_4191101 < baseStart_4191101 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191121 : List Nat := [1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 6]
def baseStart_4191121 : Nat := 118140960795 + 4191121 * 2 ^ 59
def prefixEnd_4191121 : Nat := 4983230072969 + 3 ^ 40 * 4191121 * 2
def baseEnd_4191121 : Nat := 2152059554152401953512891

theorem tailTrace_4191121 : CollatzResearch.WordTrace tailWord_4191121 prefixEnd_4191121 2152059554152401953512891 := by
  unfold tailWord_4191121
  simp only [CollatzResearch.WordTrace]
  refine ⟨152862741049291878325237217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101908494032861252216824811 152862741049291878325237217)
  ·
    refine ⟨114647055786968908743927913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152862741049291878325237217 114647055786968908743927913)
    ·
      refine ⟨85985291840226681557945935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114647055786968908743927913 85985291840226681557945935)
      ·
        refine ⟨128977937760340022336918903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85985291840226681557945935 128977937760340022336918903)
        ·
          refine ⟨193466906640510033505378355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128977937760340022336918903 193466906640510033505378355)
          ·
            refine ⟨290200359960765050258067533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193466906640510033505378355 290200359960765050258067533)
            ·
              refine ⟨108825134985286893846775325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290200359960765050258067533 108825134985286893846775325)
              ·
                refine ⟨40809425619482585192540747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108825134985286893846775325 40809425619482585192540747)
                ·
                  refine ⟨61214138429223877788811121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40809425619482585192540747 61214138429223877788811121)
                  ·
                    refine ⟨45910603821917908341608341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61214138429223877788811121 45910603821917908341608341)
                    ·
                      refine ⟨2152059554152401953512891, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45910603821917908341608341 2152059554152401953512891)
                      ·
                        rfl

theorem cell23_4191121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 6].length) (baseStart_4191121 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191121 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191121 prefixEnd_4191121 := by exact prefixLift 4191121
  have htrace : WordTrace (prefixWord ++ tailWord_4191121) baseStart_4191121 baseEnd_4191121 := by
    simpa [prefixWord, tailWord_4191121, baseEnd_4191121] using wordTrace_append hprefix tailTrace_4191121
  have hstable : (prefixWord ++ tailWord_4191121).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191121).length < 2 ^ (prefixWord ++ tailWord_4191121).sum := by decide
  have hdescent : baseEnd_4191121 < baseStart_4191121 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191145 : List Nat := [1, 2, 1, 1, 1, 1, 7, 2, 3, 1, 3]
def baseStart_4191145 : Nat := 118140960795 + 4191145 * 2 ^ 59
def prefixEnd_4191145 : Nat := 4983230072969 + 3 ^ 40 * 4191145 * 2
def baseEnd_4191145 : Nat := 2152071877688109859612781

theorem tailTrace_4191145 : CollatzResearch.WordTrace tailWord_4191145 prefixEnd_4191145 2152071877688109859612781 := by
  unfold tailWord_4191145
  simp only [CollatzResearch.WordTrace]
  refine ⟨152863616401204930424110889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101909077600803286949407259 152863616401204930424110889)
  ·
    refine ⟨114647712300903697818083167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152863616401204930424110889 114647712300903697818083167)
    ·
      refine ⟨171971568451355546727124751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114647712300903697818083167 171971568451355546727124751)
      ·
        refine ⟨257957352677033320090687127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171971568451355546727124751 257957352677033320090687127)
        ·
          refine ⟨386936029015549980136030691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257957352677033320090687127 386936029015549980136030691)
          ·
            refine ⟨580404043523324970204046037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386936029015549980136030691 580404043523324970204046037)
            ·
              refine ⟨13603219770077928989157329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 580404043523324970204046037 13603219770077928989157329)
              ·
                refine ⟨10202414827558446741867997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13603219770077928989157329 10202414827558446741867997)
                ·
                  refine ⟨3825905560334417528200499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10202414827558446741867997 3825905560334417528200499)
                  ·
                    refine ⟨5738858340501626292300749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3825905560334417528200499 5738858340501626292300749)
                    ·
                      refine ⟨2152071877688109859612781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5738858340501626292300749 2152071877688109859612781)
                      ·
                        rfl

theorem cell23_4191145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 3, 1, 3].length) (baseStart_4191145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191145 prefixEnd_4191145 := by exact prefixLift 4191145
  have htrace : WordTrace (prefixWord ++ tailWord_4191145) baseStart_4191145 baseEnd_4191145 := by
    simpa [prefixWord, tailWord_4191145, baseEnd_4191145] using wordTrace_append hprefix tailTrace_4191145
  have hstable : (prefixWord ++ tailWord_4191145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191145).length < 2 ^ (prefixWord ++ tailWord_4191145).sum := by decide
  have hdescent : baseEnd_4191145 < baseStart_4191145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191155 : List Nat := [1, 1, 1, 2, 3, 1, 2, 5, 2, 3, 2]
def baseStart_4191155 : Nat := 118140960795 + 4191155 * 2 ^ 59
def prefixEnd_4191155 : Nat := 4983230072969 + 3 ^ 40 * 4191155 * 2
def baseEnd_4191155 : Nat := 2152077012494654820487735

theorem tailTrace_4191155 : CollatzResearch.WordTrace tailWord_4191155 prefixEnd_4191155 2152077012494654820487735 := by
  unfold tailWord_4191155
  simp only [CollatzResearch.WordTrace]
  refine ⟨152863981131168702131974919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101909320754112468087983279 152863981131168702131974919)
  ·
    refine ⟨229295971696753053197962379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152863981131168702131974919 229295971696753053197962379)
    ·
      refine ⟨343943957545129579796943569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229295971696753053197962379 343943957545129579796943569)
      ·
        refine ⟨257957968158847184847707677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343943957545129579796943569 257957968158847184847707677)
        ·
          refine ⟨96734238059567694317890379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257957968158847184847707677 96734238059567694317890379)
          ·
            refine ⟨145101357089351541476835569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96734238059567694317890379 145101357089351541476835569)
            ·
              refine ⟨108826017817013656107626677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145101357089351541476835569 108826017817013656107626677)
              ·
                refine ⟨10202439170345030260090001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108826017817013656107626677 10202439170345030260090001)
                ·
                  refine ⟨7651829377758772695067501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10202439170345030260090001 7651829377758772695067501)
                  ·
                    refine ⟨2869436016659539760650313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7651829377758772695067501 2869436016659539760650313)
                    ·
                      refine ⟨2152077012494654820487735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2869436016659539760650313 2152077012494654820487735)
                      ·
                        rfl

theorem cell23_4191155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 2, 5, 2, 3, 2].length) (baseStart_4191155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191155 prefixEnd_4191155 := by exact prefixLift 4191155
  have htrace : WordTrace (prefixWord ++ tailWord_4191155) baseStart_4191155 baseEnd_4191155 := by
    simpa [prefixWord, tailWord_4191155, baseEnd_4191155] using wordTrace_append hprefix tailTrace_4191155
  have hstable : (prefixWord ++ tailWord_4191155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191155).length < 2 ^ (prefixWord ++ tailWord_4191155).sum := by decide
  have hdescent : baseEnd_4191155 < baseStart_4191155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191156 : List Nat := [2, 5, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_4191156 : Nat := 118140960795 + 4191156 * 2 ^ 59
def prefixEnd_4191156 : Nat := 4983230072969 + 3 ^ 40 * 4191156 * 2
def baseEnd_4191156 : Nat := 717359175325103105525077

theorem tailTrace_4191156 : CollatzResearch.WordTrace tailWord_4191156 prefixEnd_4191156 717359175325103105525077 := by
  unfold tailWord_4191156
  simp only [CollatzResearch.WordTrace]
  refine ⟨76432008802082539651380661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101909345069443386201840881 76432008802082539651380661)
  ·
    refine ⟨7165500825195238092316937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76432008802082539651380661 7165500825195238092316937)
    ·
      refine ⟨5374125618896428569237703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7165500825195238092316937 5374125618896428569237703)
      ·
        refine ⟨8061188428344642853856555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5374125618896428569237703 8061188428344642853856555)
        ·
          refine ⟨12091782642516964280784833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8061188428344642853856555 12091782642516964280784833)
          ·
            refine ⟨9068836981887723210588625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12091782642516964280784833 9068836981887723210588625)
            ·
              refine ⟨6801627736415792407941469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9068836981887723210588625 6801627736415792407941469)
              ·
                refine ⟨2550610401155922152978051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6801627736415792407941469 2550610401155922152978051)
                ·
                  refine ⟨3825915601733883229467077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2550610401155922152978051 3825915601733883229467077)
                  ·
                    refine ⟨717359175325103105525077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3825915601733883229467077 717359175325103105525077)
                    ·
                      rfl

theorem cell23_4191156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_4191156 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191156 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191156 prefixEnd_4191156 := by exact prefixLift 4191156
  have htrace : WordTrace (prefixWord ++ tailWord_4191156) baseStart_4191156 baseEnd_4191156 := by
    simpa [prefixWord, tailWord_4191156, baseEnd_4191156] using wordTrace_append hprefix tailTrace_4191156
  have hstable : (prefixWord ++ tailWord_4191156).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191156).length < 2 ^ (prefixWord ++ tailWord_4191156).sum := by decide
  have hdescent : baseEnd_4191156 < baseStart_4191156 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191222 : List Nat := [5, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5]
def baseStart_4191222 : Nat := 118140960795 + 4191222 * 2 ^ 59
def prefixEnd_4191222 : Nat := 4983230072969 + 3 ^ 40 * 4191222 * 2
def baseEnd_4191222 : Nat := 2152111415698506058349927

theorem tailTrace_4191222 : CollatzResearch.WordTrace tailWord_4191222 prefixEnd_4191222 2152111415698506058349927 := by
  unfold tailWord_4191222
  simp only [CollatzResearch.WordTrace]
  refine ⟨9554151551370373285916495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101910949881283981716442613 9554151551370373285916495)
  ·
    refine ⟨14331227327055559928874743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9554151551370373285916495 14331227327055559928874743)
    ·
      refine ⟨21496840990583339893312115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14331227327055559928874743 21496840990583339893312115)
      ·
        refine ⟨32245261485875009839968173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21496840990583339893312115 32245261485875009839968173)
        ·
          refine ⟨12091973057203128689988065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32245261485875009839968173 12091973057203128689988065)
          ·
            refine ⟨9068979792902346517491049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12091973057203128689988065 9068979792902346517491049)
            ·
              refine ⟨6801734844676759888118287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9068979792902346517491049 6801734844676759888118287)
              ·
                refine ⟨10202602267015139832177431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6801734844676759888118287 10202602267015139832177431)
                ·
                  refine ⟨15303903400522709748266147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10202602267015139832177431 15303903400522709748266147)
                  ·
                    refine ⟨22955855100784064622399221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15303903400522709748266147 22955855100784064622399221)
                    ·
                      refine ⟨2152111415698506058349927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22955855100784064622399221 2152111415698506058349927)
                      ·
                        rfl

theorem cell23_4191222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 2, 1, 1, 1, 5].length) (baseStart_4191222 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191222 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191222 prefixEnd_4191222 := by exact prefixLift 4191222
  have htrace : WordTrace (prefixWord ++ tailWord_4191222) baseStart_4191222 baseEnd_4191222 := by
    simpa [prefixWord, tailWord_4191222, baseEnd_4191222] using wordTrace_append hprefix tailTrace_4191222
  have hstable : (prefixWord ++ tailWord_4191222).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191222).length < 2 ^ (prefixWord ++ tailWord_4191222).sum := by decide
  have hdescent : baseEnd_4191222 < baseStart_4191222 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191286 : List Nat := [5, 1, 2, 1, 1, 3, 2, 2, 2, 1, 3]
def baseStart_4191286 : Nat := 118140960795 + 4191286 * 2 ^ 59
def prefixEnd_4191286 : Nat := 4983230072969 + 3 ^ 40 * 4191286 * 2
def baseEnd_4191286 : Nat := 2152144278460393807949633

theorem tailTrace_4191286 : CollatzResearch.WordTrace tailWord_4191286 prefixEnd_4191286 2152144278460393807949633 := by
  unfold tailWord_4191286
  simp only [CollatzResearch.WordTrace]
  refine ⟨9554297443355881969062107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101912506062462741003329141 9554297443355881969062107)
  ·
    refine ⟨14331446165033822953593161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9554297443355881969062107 14331446165033822953593161)
    ·
      refine ⟨10748584623775367215194871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14331446165033822953593161 10748584623775367215194871)
      ·
        refine ⟨16122876935663050822792307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10748584623775367215194871 16122876935663050822792307)
        ·
          refine ⟨24184315403494576234188461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16122876935663050822792307 24184315403494576234188461)
          ·
            refine ⟨9069118276310466087820673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24184315403494576234188461 9069118276310466087820673)
            ·
              refine ⟨6801838707232849565865505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9069118276310466087820673 6801838707232849565865505)
              ·
                refine ⟨5101379030424637174399129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6801838707232849565865505 5101379030424637174399129)
                ·
                  refine ⟨3826034272818477880799347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5101379030424637174399129 3826034272818477880799347)
                  ·
                    refine ⟨5739051409227716821199021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3826034272818477880799347 5739051409227716821199021)
                    ·
                      refine ⟨2152144278460393807949633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5739051409227716821199021 2152144278460393807949633)
                      ·
                        rfl

theorem cell23_4191286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 3, 2, 2, 2, 1, 3].length) (baseStart_4191286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191286 prefixEnd_4191286 := by exact prefixLift 4191286
  have htrace : WordTrace (prefixWord ++ tailWord_4191286) baseStart_4191286 baseEnd_4191286 := by
    simpa [prefixWord, tailWord_4191286, baseEnd_4191286] using wordTrace_append hprefix tailTrace_4191286
  have hstable : (prefixWord ++ tailWord_4191286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191286).length < 2 ^ (prefixWord ++ tailWord_4191286).sum := by decide
  have hdescent : baseEnd_4191286 < baseStart_4191286 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191302 : List Nat := [6, 1, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_4191302 : Nat := 118140960795 + 4191302 * 2 ^ 59
def prefixEnd_4191302 : Nat := 4983230072969 + 3 ^ 40 * 4191302 * 2
def baseEnd_4191302 : Nat := 717384164716955248449853

theorem tailTrace_4191302 : CollatzResearch.WordTrace tailWord_4191302 prefixEnd_4191302 717384164716955248449853 := by
  unfold tailWord_4191302
  simp only [CollatzResearch.WordTrace]
  refine ⟨4777166958176129569924255, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 101912895107757430825050773 4777166958176129569924255)
  ·
    refine ⟨7165750437264194354886383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 4777166958176129569924255 7165750437264194354886383)
    ·
      refine ⟨10748625655896291532329575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7165750437264194354886383 10748625655896291532329575)
      ·
        refine ⟨16122938483844437298494363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10748625655896291532329575 16122938483844437298494363)
        ·
          refine ⟨24184407725766655947741545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16122938483844437298494363 24184407725766655947741545)
          ·
            refine ⟨18138305794324991960806159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24184407725766655947741545 18138305794324991960806159)
            ·
              refine ⟨27207458691487487941209239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18138305794324991960806159 27207458691487487941209239)
              ·
                refine ⟨40811188037231231911813859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27207458691487487941209239 40811188037231231911813859)
                ·
                  refine ⟨61216782055846847867720789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40811188037231231911813859 61216782055846847867720789)
                  ·
                    refine ⟨717384164716955248449853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61216782055846847867720789 717384164716955248449853)
                    ·
                      rfl

theorem cell23_4191302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_4191302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191302 prefixEnd_4191302 := by exact prefixLift 4191302
  have htrace : WordTrace (prefixWord ++ tailWord_4191302) baseStart_4191302 baseEnd_4191302 := by
    simpa [prefixWord, tailWord_4191302, baseEnd_4191302] using wordTrace_append hprefix tailTrace_4191302
  have hstable : (prefixWord ++ tailWord_4191302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191302).length < 2 ^ (prefixWord ++ tailWord_4191302).sum := by decide
  have hdescent : baseEnd_4191302 < baseStart_4191302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191309 : List Nat := [1, 6, 1, 1, 1, 2, 1, 3, 1, 4, 2]
def baseStart_4191309 : Nat := 118140960795 + 4191309 * 2 ^ 59
def prefixEnd_4191309 : Nat := 4983230072969 + 3 ^ 40 * 4191309 * 2
def baseEnd_4191309 : Nat := 2152156088515447217962027

theorem tailTrace_4191309 : CollatzResearch.WordTrace tailWord_4191309 prefixEnd_4191309 2152156088515447217962027 := by
  unfold tailWord_4191309
  simp only [CollatzResearch.WordTrace]
  refine ⟨152869597972610786433080981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101913065315073857622053987 152869597972610786433080981)
  ·
    refine ⟨7165762404966130614050671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152869597972610786433080981 7165762404966130614050671)
    ·
      refine ⟨10748643607449195921076007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7165762404966130614050671 10748643607449195921076007)
      ·
        refine ⟨16122965411173793881614011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10748643607449195921076007 16122965411173793881614011)
        ·
          refine ⟨24184448116760690822421017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16122965411173793881614011 24184448116760690822421017)
          ·
            refine ⟨18138336087570518116815763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24184448116760690822421017 18138336087570518116815763)
            ·
              refine ⟨27207504131355777175223645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18138336087570518116815763 27207504131355777175223645)
              ·
                refine ⟨10202814049258416440708867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27207504131355777175223645 10202814049258416440708867)
                ·
                  refine ⟨15304221073887624661063301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10202814049258416440708867 15304221073887624661063301)
                  ·
                    refine ⟨2869541451353929623949369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15304221073887624661063301 2869541451353929623949369)
                    ·
                      refine ⟨2152156088515447217962027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2869541451353929623949369 2152156088515447217962027)
                      ·
                        rfl

theorem cell23_4191309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 1, 3, 1, 4, 2].length) (baseStart_4191309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191309 prefixEnd_4191309 := by exact prefixLift 4191309
  have htrace : WordTrace (prefixWord ++ tailWord_4191309) baseStart_4191309 baseEnd_4191309 := by
    simpa [prefixWord, tailWord_4191309, baseEnd_4191309] using wordTrace_append hprefix tailTrace_4191309
  have hstable : (prefixWord ++ tailWord_4191309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191309).length < 2 ^ (prefixWord ++ tailWord_4191309).sum := by decide
  have hdescent : baseEnd_4191309 < baseStart_4191309 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191342 : List Nat := [4, 1, 2, 2, 1, 2, 1, 2, 2, 3, 3]
def baseStart_4191342 : Nat := 118140960795 + 4191342 * 2 ^ 59
def prefixEnd_4191342 : Nat := 4983230072969 + 3 ^ 40 * 4191342 * 2
def baseEnd_4191342 : Nat := 2152173033377045588849375

theorem tailTrace_4191342 : CollatzResearch.WordTrace tailWord_4191342 prefixEnd_4191342 2152173033377045588849375 := by
  unfold tailWord_4191342
  simp only [CollatzResearch.WordTrace]
  refine ⟨19108850197686404133629035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101913867720994155379354853 19108850197686404133629035)
  ·
    refine ⟨28663275296529606200443553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19108850197686404133629035 28663275296529606200443553)
    ·
      refine ⟨21497456472397204650332665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28663275296529606200443553 21497456472397204650332665)
      ·
        refine ⟨16123092354297903487749499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21497456472397204650332665 16123092354297903487749499)
        ·
          refine ⟨24184638531446855231624249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16123092354297903487749499 24184638531446855231624249)
          ·
            refine ⟨18138478898585141423718187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24184638531446855231624249 18138478898585141423718187)
            ·
              refine ⟨27207718347877712135577281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18138478898585141423718187 27207718347877712135577281)
              ·
                refine ⟨20405788760908284101682961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27207718347877712135577281 20405788760908284101682961)
                ·
                  refine ⟨15304341570681213076262221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20405788760908284101682961 15304341570681213076262221)
                  ·
                    refine ⟨5739128089005454903598333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15304341570681213076262221 5739128089005454903598333)
                    ·
                      refine ⟨2152173033377045588849375, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5739128089005454903598333 2152173033377045588849375)
                      ·
                        rfl

theorem cell23_4191342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 1, 2, 2, 3, 3].length) (baseStart_4191342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191342 prefixEnd_4191342 := by exact prefixLift 4191342
  have htrace : WordTrace (prefixWord ++ tailWord_4191342) baseStart_4191342 baseEnd_4191342 := by
    simpa [prefixWord, tailWord_4191342, baseEnd_4191342] using wordTrace_append hprefix tailTrace_4191342
  have hstable : (prefixWord ++ tailWord_4191342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191342).length < 2 ^ (prefixWord ++ tailWord_4191342).sum := by decide
  have hdescent : baseEnd_4191342 < baseStart_4191342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191349 : List Nat := [1, 3, 4, 3, 1, 1, 2, 1, 7]
def baseStart_4191349 : Nat := 118140960795 + 4191349 * 2 ^ 59
def prefixEnd_4191349 : Nat := 4983230072969 + 3 ^ 40 * 4191349 * 2
def baseEnd_4191349 : Nat := 239130736415736340162427

theorem tailTrace_4191349 : CollatzResearch.WordTrace tailWord_4191349 prefixEnd_4191349 239130736415736340162427 := by
  unfold tailWord_4191349
  simp only [CollatzResearch.WordTrace]
  refine ⟨152871056892465873264537101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101914037928310582176358067 152871056892465873264537101)
  ·
    refine ⟨57326646334674702474201413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152871056892465873264537101 57326646334674702474201413)
    ·
      refine ⟨10748746187751506713912765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57326646334674702474201413 10748746187751506713912765)
      ·
        refine ⟨4030779820406815017717287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10748746187751506713912765 4030779820406815017717287)
        ·
          refine ⟨6046169730610222526575931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4030779820406815017717287 6046169730610222526575931)
          ·
            refine ⟨9069254595915333789863897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6046169730610222526575931 9069254595915333789863897)
            ·
              refine ⟨6801940946936500342397923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9069254595915333789863897 6801940946936500342397923)
              ·
                refine ⟨10202911420404750513596885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6801940946936500342397923 10202911420404750513596885)
                ·
                  refine ⟨239130736415736340162427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10202911420404750513596885 239130736415736340162427)
                  ·
                    rfl

theorem cell23_4191349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 2, 1, 7].length) (baseStart_4191349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191349 prefixEnd_4191349 := by exact prefixLift 4191349
  have htrace : WordTrace (prefixWord ++ tailWord_4191349) baseStart_4191349 baseEnd_4191349 := by
    simpa [prefixWord, tailWord_4191349, baseEnd_4191349] using wordTrace_append hprefix tailTrace_4191349
  have hstable : (prefixWord ++ tailWord_4191349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191349).length < 2 ^ (prefixWord ++ tailWord_4191349).sum := by decide
  have hdescent : baseEnd_4191349 < baseStart_4191349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191375 : List Nat := [1, 1, 2, 1, 1, 1, 1, 2, 9, 4]
def baseStart_4191375 : Nat := 118140960795 + 4191375 * 2 ^ 59
def prefixEnd_4191375 : Nat := 4983230072969 + 3 ^ 40 * 4191375 * 2
def baseEnd_4191375 : Nat := 717396659412881319912241

theorem tailTrace_4191375 : CollatzResearch.WordTrace tailWord_4191375 prefixEnd_4191375 717396659412881319912241 := by
  unfold tailWord_4191375
  simp only [CollatzResearch.WordTrace]
  refine ⟨152872005190371679704983579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101914670126914453136655719 152872005190371679704983579)
  ·
    refine ⟨229308007785557519557475369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152872005190371679704983579 229308007785557519557475369)
    ·
      refine ⟨171981005839168139668106527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229308007785557519557475369 171981005839168139668106527)
      ·
        refine ⟨257971508758752209502159791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171981005839168139668106527 257971508758752209502159791)
        ·
          refine ⟨386957263138128314253239687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 257971508758752209502159791 386957263138128314253239687)
          ·
            refine ⟨580435894707192471379859531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 386957263138128314253239687 580435894707192471379859531)
            ·
              refine ⟨870653842060788707069789297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580435894707192471379859531 870653842060788707069789297)
              ·
                refine ⟨652990381545591530302341973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 870653842060788707069789297 652990381545591530302341973)
                ·
                  refine ⟨3826115516868700372865285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 652990381545591530302341973 3826115516868700372865285)
                  ·
                    refine ⟨717396659412881319912241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3826115516868700372865285 717396659412881319912241)
                    ·
                      rfl

theorem cell23_4191375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 2, 9, 4].length) (baseStart_4191375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191375 prefixEnd_4191375 := by exact prefixLift 4191375
  have htrace : WordTrace (prefixWord ++ tailWord_4191375) baseStart_4191375 baseEnd_4191375 := by
    simpa [prefixWord, tailWord_4191375, baseEnd_4191375] using wordTrace_append hprefix tailTrace_4191375
  have hstable : (prefixWord ++ tailWord_4191375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191375).length < 2 ^ (prefixWord ++ tailWord_4191375).sum := by decide
  have hdescent : baseEnd_4191375 < baseStart_4191375 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191399 : List Nat := [1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 4]
def baseStart_4191399 : Nat := 118140960795 + 4191399 * 2 ^ 59
def prefixEnd_4191399 : Nat := 4983230072969 + 3 ^ 40 * 4191399 * 2
def baseEnd_4191399 : Nat := 2152202301774351865836613

theorem tailTrace_4191399 : CollatzResearch.WordTrace tailWord_4191399 prefixEnd_4191399 2152202301774351865836613 := by
  unfold tailWord_4191399
  simp only [CollatzResearch.WordTrace]
  refine ⟨152872880542284731803857251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101915253694856487869238167 152872880542284731803857251)
  ·
    refine ⟨229309320813427097705785877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152872880542284731803857251 229309320813427097705785877)
    ·
      refine ⟨10748874413129395204958713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 229309320813427097705785877 10748874413129395204958713)
      ·
        refine ⟨8061655809847046403719035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10748874413129395204958713 8061655809847046403719035)
        ·
          refine ⟨12092483714770569605578553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8061655809847046403719035 12092483714770569605578553)
          ·
            refine ⟨9069362786077927204183915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12092483714770569605578553 9069362786077927204183915)
            ·
              refine ⟨13604044179116890806275873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9069362786077927204183915 13604044179116890806275873)
              ·
                refine ⟨10203033134337668104706905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13604044179116890806275873 10203033134337668104706905)
                ·
                  refine ⟨7652274850753251078530179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10203033134337668104706905 7652274850753251078530179)
                  ·
                    refine ⟨11478412276129876617795269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7652274850753251078530179 11478412276129876617795269)
                    ·
                      refine ⟨2152202301774351865836613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11478412276129876617795269 2152202301774351865836613)
                      ·
                        rfl

theorem cell23_4191399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 1, 2, 2, 1, 4].length) (baseStart_4191399 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191399 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191399 prefixEnd_4191399 := by exact prefixLift 4191399
  have htrace : WordTrace (prefixWord ++ tailWord_4191399) baseStart_4191399 baseEnd_4191399 := by
    simpa [prefixWord, tailWord_4191399, baseEnd_4191399] using wordTrace_append hprefix tailTrace_4191399
  have hstable : (prefixWord ++ tailWord_4191399).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191399).length < 2 ^ (prefixWord ++ tailWord_4191399).sum := by decide
  have hdescent : baseEnd_4191399 < baseStart_4191399 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191409 : List Nat := [1, 2, 2, 5, 1, 1, 3, 1, 3, 4]
def baseStart_4191409 : Nat := 118140960795 + 4191409 * 2 ^ 59
def prefixEnd_4191409 : Nat := 4983230072969 + 3 ^ 40 * 4191409 * 2
def baseEnd_4191409 : Nat := 717402478860298942237189

theorem tailTrace_4191409 : CollatzResearch.WordTrace tailWord_4191409 prefixEnd_4191409 717402478860298942237189 := by
  unfold tailWord_4191409
  simp only [CollatzResearch.WordTrace]
  refine ⟨152873245272248503511721281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101915496848165669007814187 152873245272248503511721281)
  ·
    refine ⟨114654933954186377633790961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152873245272248503511721281 114654933954186377633790961)
    ·
      refine ⟨85991200465639783225343221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114654933954186377633790961 85991200465639783225343221)
      ·
        refine ⟨8061675043653729677375927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 85991200465639783225343221 8061675043653729677375927)
        ·
          refine ⟨12092512565480594516063891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8061675043653729677375927 12092512565480594516063891)
          ·
            refine ⟨18138768848220891774095837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12092512565480594516063891 18138768848220891774095837)
            ·
              refine ⟨6802038318082834415285939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18138768848220891774095837 6802038318082834415285939)
              ·
                refine ⟨10203057477124251622928909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6802038318082834415285939 10203057477124251622928909)
                ·
                  refine ⟨3826146553921594358598341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10203057477124251622928909 3826146553921594358598341)
                  ·
                    refine ⟨717402478860298942237189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3826146553921594358598341 717402478860298942237189)
                    ·
                      rfl

theorem cell23_4191409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 1, 3, 4].length) (baseStart_4191409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191409 prefixEnd_4191409 := by exact prefixLift 4191409
  have htrace : WordTrace (prefixWord ++ tailWord_4191409) baseStart_4191409 baseEnd_4191409 := by
    simpa [prefixWord, tailWord_4191409, baseEnd_4191409] using wordTrace_append hprefix tailTrace_4191409
  have hstable : (prefixWord ++ tailWord_4191409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191409).length < 2 ^ (prefixWord ++ tailWord_4191409).sum := by decide
  have hdescent : baseEnd_4191409 < baseStart_4191409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191472 : List Nat := [2, 1, 1, 1, 3, 1, 1, 1, 4, 6, 2]
def baseStart_4191472 : Nat := 118140960795 + 4191472 * 2 ^ 59
def prefixEnd_4191472 : Nat := 4983230072969 + 3 ^ 40 * 4191472 * 2
def baseEnd_4191472 : Nat := 2152239785862130080223777

theorem tailTrace_4191472 : CollatzResearch.WordTrace tailWord_4191472 prefixEnd_4191472 2152239785862130080223777 := by
  unfold tailWord_4191472
  simp only [CollatzResearch.WordTrace]
  refine ⟨76437771535510132635632335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101917028714013510180843113 76437771535510132635632335)
  ·
    refine ⟨114656657303265198953448503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76437771535510132635632335 114656657303265198953448503)
    ·
      refine ⟨171984985954897798430172755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114656657303265198953448503 171984985954897798430172755)
      ·
        refine ⟨257977478932346697645259133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171984985954897798430172755 257977478932346697645259133)
        ·
          refine ⟨96741554599630011616972175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 257977478932346697645259133 96741554599630011616972175)
          ·
            refine ⟨145112331899445017425458263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96741554599630011616972175 145112331899445017425458263)
            ·
              refine ⟨217668497849167526138187395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145112331899445017425458263 217668497849167526138187395)
              ·
                refine ⟨326502746773751289207281093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217668497849167526138187395 326502746773751289207281093)
                ·
                  refine ⟨61219265020078366726365205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 326502746773751289207281093 61219265020078366726365205)
                  ·
                    refine ⟨2869653047816173440298369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61219265020078366726365205 2869653047816173440298369)
                    ·
                      refine ⟨2152239785862130080223777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2869653047816173440298369 2152239785862130080223777)
                      ·
                        rfl

theorem cell23_4191472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 1, 4, 6, 2].length) (baseStart_4191472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191472 prefixEnd_4191472 := by exact prefixLift 4191472
  have htrace : WordTrace (prefixWord ++ tailWord_4191472) baseStart_4191472 baseEnd_4191472 := by
    simpa [prefixWord, tailWord_4191472, baseEnd_4191472] using wordTrace_append hprefix tailTrace_4191472
  have hstable : (prefixWord ++ tailWord_4191472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191472).length < 2 ^ (prefixWord ++ tailWord_4191472).sum := by decide
  have hdescent : baseEnd_4191472 < baseStart_4191472 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191482 : List Nat := [3, 1, 1, 1, 1, 4, 4, 1, 1, 6]
def baseStart_4191482 : Nat := 118140960795 + 4191482 * 2 ^ 59
def prefixEnd_4191482 : Nat := 4983230072969 + 3 ^ 40 * 4191482 * 2
def baseEnd_4191482 : Nat := 717414973556225013699577

theorem tailTrace_4191482 : CollatzResearch.WordTrace tailWord_4191482 prefixEnd_4191482 717414973556225013699577 := by
  unfold tailWord_4191482
  simp only [CollatzResearch.WordTrace]
  refine ⟨38218976950246009244782175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101917271867322691319419133 38218976950246009244782175)
  ·
    refine ⟨57328465425369013867173263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38218976950246009244782175 57328465425369013867173263)
    ·
      refine ⟨85992698138053520800759895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57328465425369013867173263 85992698138053520800759895)
      ·
        refine ⟨128989047207080281201139843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 85992698138053520800759895 128989047207080281201139843)
        ·
          refine ⟨193483570810620421801709765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 128989047207080281201139843 193483570810620421801709765)
          ·
            refine ⟨36278169526991329087820581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193483570810620421801709765 36278169526991329087820581)
            ·
              refine ⟨6802156786310874203966359, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36278169526991329087820581 6802156786310874203966359)
              ·
                refine ⟨10203235179466311305949539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6802156786310874203966359 10203235179466311305949539)
                ·
                  refine ⟨15304852769199466958924309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10203235179466311305949539 15304852769199466958924309)
                  ·
                    refine ⟨717414973556225013699577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15304852769199466958924309 717414973556225013699577)
                    ·
                      rfl

theorem cell23_4191482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 4, 1, 1, 6].length) (baseStart_4191482 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191482 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191482 prefixEnd_4191482 := by exact prefixLift 4191482
  have htrace : WordTrace (prefixWord ++ tailWord_4191482) baseStart_4191482 baseEnd_4191482 := by
    simpa [prefixWord, tailWord_4191482, baseEnd_4191482] using wordTrace_append hprefix tailTrace_4191482
  have hstable : (prefixWord ++ tailWord_4191482).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191482).length < 2 ^ (prefixWord ++ tailWord_4191482).sum := by decide
  have hdescent : baseEnd_4191482 < baseStart_4191482 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191515 : List Nat := [1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 6]
def baseStart_4191515 : Nat := 118140960795 + 4191515 * 2 ^ 59
def prefixEnd_4191515 : Nat := 4983230072969 + 3 ^ 40 * 4191515 * 2
def baseEnd_4191515 : Nat := 2152261865530273411986079

theorem tailTrace_4191515 : CollatzResearch.WordTrace tailWord_4191515 prefixEnd_4191515 2152261865530273411986079 := by
  unfold tailWord_4191515
  simp only [CollatzResearch.WordTrace]
  refine ⟨152877111409864483615079999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101918074273242989076719999 152877111409864483615079999)
  ·
    refine ⟨229315667114796725422619999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152877111409864483615079999 229315667114796725422619999)
    ·
      refine ⟨343973500672195088133929999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229315667114796725422619999 343973500672195088133929999)
      ·
        refine ⟨515960251008292632200894999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 343973500672195088133929999 515960251008292632200894999)
        ·
          refine ⟨773940376512438948301342499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 515960251008292632200894999 773940376512438948301342499)
          ·
            refine ⟨1160910564768658422452013749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 773940376512438948301342499 1160910564768658422452013749)
            ·
              refine ⟨108835365447061727104876289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 1160910564768658422452013749 108835365447061727104876289)
              ·
                refine ⟨81626524085296295328657217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108835365447061727104876289 81626524085296295328657217)
                ·
                  refine ⟨61219893063972221496492913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81626524085296295328657217 61219893063972221496492913)
                  ·
                    refine ⟨45914919797979166122369685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61219893063972221496492913 45914919797979166122369685)
                    ·
                      refine ⟨2152261865530273411986079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45914919797979166122369685 2152261865530273411986079)
                      ·
                        rfl

theorem cell23_4191515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 5, 2, 2, 2, 6].length) (baseStart_4191515 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191515 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191515 prefixEnd_4191515 := by exact prefixLift 4191515
  have htrace : WordTrace (prefixWord ++ tailWord_4191515) baseStart_4191515 baseEnd_4191515 := by
    simpa [prefixWord, tailWord_4191515, baseEnd_4191515] using wordTrace_append hprefix tailTrace_4191515
  have hstable : (prefixWord ++ tailWord_4191515).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191515).length < 2 ^ (prefixWord ++ tailWord_4191515).sum := by decide
  have hdescent : baseEnd_4191515 < baseStart_4191515 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191523 : List Nat := [1, 1, 1, 4, 2, 3, 2, 4, 1, 2, 2]
def baseStart_4191523 : Nat := 118140960795 + 4191523 * 2 ^ 59
def prefixEnd_4191523 : Nat := 4983230072969 + 3 ^ 40 * 4191523 * 2
def baseEnd_4191523 : Nat := 2152265973375509380686043

theorem tailTrace_4191523 : CollatzResearch.WordTrace tailWord_4191523 prefixEnd_4191523 2152265973375509380686043 := by
  unfold tailWord_4191523
  simp only [CollatzResearch.WordTrace]
  refine ⟨152877403193835500981371223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101918268795890333987580815 152877403193835500981371223)
  ·
    refine ⟨229316104790753251472056835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152877403193835500981371223 229316104790753251472056835)
    ·
      refine ⟨343974157186129877208085253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229316104790753251472056835 343974157186129877208085253)
      ·
        refine ⟨64495154472399351976515985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 343974157186129877208085253 64495154472399351976515985)
        ·
          refine ⟨48371365854299513982386989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64495154472399351976515985 48371365854299513982386989)
          ·
            refine ⟨18139262195362317743395121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48371365854299513982386989 18139262195362317743395121)
            ·
              refine ⟨13604446646521738307546341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18139262195362317743395121 13604446646521738307546341)
              ·
                refine ⟨2550833746222825932664939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13604446646521738307546341 2550833746222825932664939)
                ·
                  refine ⟨3826250619334238898997409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2550833746222825932664939 3826250619334238898997409)
                  ·
                    refine ⟨2869687964500679174248057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3826250619334238898997409 2869687964500679174248057)
                    ·
                      refine ⟨2152265973375509380686043, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2869687964500679174248057 2152265973375509380686043)
                      ·
                        rfl

theorem cell23_4191523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 3, 2, 4, 1, 2, 2].length) (baseStart_4191523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191523 prefixEnd_4191523 := by exact prefixLift 4191523
  have htrace : WordTrace (prefixWord ++ tailWord_4191523) baseStart_4191523 baseEnd_4191523 := by
    simpa [prefixWord, tailWord_4191523, baseEnd_4191523] using wordTrace_append hprefix tailTrace_4191523
  have hstable : (prefixWord ++ tailWord_4191523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191523).length < 2 ^ (prefixWord ++ tailWord_4191523).sum := by decide
  have hdescent : baseEnd_4191523 < baseStart_4191523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191539 : List Nat := [1, 1, 1, 2, 5, 2, 3, 1, 1, 3, 3]
def baseStart_4191539 : Nat := 118140960795 + 4191539 * 2 ^ 59
def prefixEnd_4191539 : Nat := 4983230072969 + 3 ^ 40 * 4191539 * 2
def baseEnd_4191539 : Nat := 2152274189065981318085969

theorem tailTrace_4191539 : CollatzResearch.WordTrace tailWord_4191539 prefixEnd_4191539 2152274189065981318085969 := by
  unfold tailWord_4191539
  simp only [CollatzResearch.WordTrace]
  refine ⟨152877986761777535713953671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101918657841185023809302447 152877986761777535713953671)
  ·
    refine ⟨229316980142666303570930507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152877986761777535713953671 229316980142666303570930507)
    ·
      refine ⟨343975470213999455356395761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229316980142666303570930507 343975470213999455356395761)
      ·
        refine ⟨257981602660499591517296821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 343975470213999455356395761 257981602660499591517296821)
        ·
          refine ⟨24185775249421836704746577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 257981602660499591517296821 24185775249421836704746577)
          ·
            refine ⟨18139331437066377528559933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24185775249421836704746577 18139331437066377528559933)
            ·
              refine ⟨6802249288899891573209975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18139331437066377528559933 6802249288899891573209975)
              ·
                refine ⟨10203373933349837359814963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6802249288899891573209975 10203373933349837359814963)
                ·
                  refine ⟨15305060900024756039722445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10203373933349837359814963 15305060900024756039722445)
                  ·
                    refine ⟨5739397837509283514895917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15305060900024756039722445 5739397837509283514895917)
                    ·
                      refine ⟨2152274189065981318085969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5739397837509283514895917 2152274189065981318085969)
                      ·
                        rfl

theorem cell23_4191539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3, 3].length) (baseStart_4191539 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191539 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191539 prefixEnd_4191539 := by exact prefixLift 4191539
  have htrace : WordTrace (prefixWord ++ tailWord_4191539) baseStart_4191539 baseEnd_4191539 := by
    simpa [prefixWord, tailWord_4191539, baseEnd_4191539] using wordTrace_append hprefix tailTrace_4191539
  have hstable : (prefixWord ++ tailWord_4191539).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191539).length < 2 ^ (prefixWord ++ tailWord_4191539).sum := by decide
  have hdescent : baseEnd_4191539 < baseStart_4191539 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191566 : List Nat := [4, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2]
def baseStart_4191566 : Nat := 118140960795 + 4191566 * 2 ^ 59
def prefixEnd_4191566 : Nat := 4983230072969 + 3 ^ 40 * 4191566 * 2
def baseEnd_4191566 : Nat := 2152288053043652712448345

theorem tailTrace_4191566 : CollatzResearch.WordTrace tailWord_4191566 prefixEnd_4191566 2152288053043652712448345 := by
  unfold tailWord_4191566
  simp only [CollatzResearch.WordTrace]
  refine ⟨19109871441584964915648319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101919314355119812883457701 19109871441584964915648319)
  ·
    refine ⟨28664807162377447373472479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19109871441584964915648319 28664807162377447373472479)
    ·
      refine ⟨42997210743566171060208719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28664807162377447373472479 42997210743566171060208719)
      ·
        refine ⟨64495816115349256590313079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 42997210743566171060208719 64495816115349256590313079)
        ·
          refine ⟨96743724173023884885469619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64495816115349256590313079 96743724173023884885469619)
          ·
            refine ⟨145115586259535827328204429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96743724173023884885469619 145115586259535827328204429)
            ·
              refine ⟨54418344847325935248076661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145115586259535827328204429 54418344847325935248076661)
              ·
                refine ⟨5101719829436806429507187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54418344847325935248076661 5101719829436806429507187)
                ·
                  refine ⟨7652579744155209644260781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5101719829436806429507187 7652579744155209644260781)
                  ·
                    refine ⟨2869717404058203616597793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7652579744155209644260781 2869717404058203616597793)
                    ·
                      refine ⟨2152288053043652712448345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2869717404058203616597793 2152288053043652712448345)
                      ·
                        rfl

theorem cell23_4191566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 5, 1, 3, 2].length) (baseStart_4191566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191566 prefixEnd_4191566 := by exact prefixLift 4191566
  have htrace : WordTrace (prefixWord ++ tailWord_4191566) baseStart_4191566 baseEnd_4191566 := by
    simpa [prefixWord, tailWord_4191566, baseEnd_4191566] using wordTrace_append hprefix tailTrace_4191566
  have hstable : (prefixWord ++ tailWord_4191566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191566).length < 2 ^ (prefixWord ++ tailWord_4191566).sum := by decide
  have hdescent : baseEnd_4191566 < baseStart_4191566 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191602 : List Nat := [3, 2, 1, 2, 1, 2, 2, 1, 9]
def baseStart_4191602 : Nat := 118140960795 + 4191602 * 2 ^ 59
def prefixEnd_4191602 : Nat := 4983230072969 + 3 ^ 40 * 4191602 * 2
def baseEnd_4191602 : Nat := 239145170927468285733131

theorem tailTrace_4191602 : CollatzResearch.WordTrace tailWord_4191602 prefixEnd_4191602 239145170927468285733131 := by
  unfold tailWord_4191602
  simp only [CollatzResearch.WordTrace]
  refine ⟨38220071140137324368374265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101920189707032864982331373 38220071140137324368374265)
  ·
    refine ⟨28665053355102993276280699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38220071140137324368374265 28665053355102993276280699)
    ·
      refine ⟨42997580032654489914421049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28665053355102993276280699 42997580032654489914421049)
      ·
        refine ⟨32248185024490867435815787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42997580032654489914421049 32248185024490867435815787)
        ·
          refine ⟨48372277536736301153723681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32248185024490867435815787 48372277536736301153723681)
          ·
            refine ⟨36279208152552225865292761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48372277536736301153723681 36279208152552225865292761)
            ·
              refine ⟨27209406114414169398969571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36279208152552225865292761 27209406114414169398969571)
              ·
                refine ⟨40814109171621254098454357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27209406114414169398969571 40814109171621254098454357)
                ·
                  refine ⟨239145170927468285733131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40814109171621254098454357 239145170927468285733131)
                  ·
                    rfl

theorem cell23_4191602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_4191602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191602 prefixEnd_4191602 := by exact prefixLift 4191602
  have htrace : WordTrace (prefixWord ++ tailWord_4191602) baseStart_4191602 baseEnd_4191602 := by
    simpa [prefixWord, tailWord_4191602, baseEnd_4191602] using wordTrace_append hprefix tailTrace_4191602
  have hstable : (prefixWord ++ tailWord_4191602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191602).length < 2 ^ (prefixWord ++ tailWord_4191602).sum := by decide
  have hdescent : baseEnd_4191602 < baseStart_4191602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191689 : List Nat := [1, 2, 1, 1, 2, 1, 3, 3, 4, 2, 3]
def baseStart_4191689 : Nat := 118140960795 + 4191689 * 2 ^ 59
def prefixEnd_4191689 : Nat := 4983230072969 + 3 ^ 40 * 4191689 * 2
def baseEnd_4191689 : Nat := 2152351211164155731210279

theorem tailTrace_4191689 : CollatzResearch.WordTrace tailWord_4191689 prefixEnd_4191689 2152351211164155731210279 := by
  unfold tailWord_4191689
  simp only [CollatzResearch.WordTrace]
  refine ⟨152883457711234111331914121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101922305140822740887942747 152883457711234111331914121)
  ·
    refine ⟨114662593283425583498935591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152883457711234111331914121 114662593283425583498935591)
    ·
      refine ⟨171993889925138375248403387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114662593283425583498935591 171993889925138375248403387)
      ·
        refine ⟨257990834887707562872605081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 171993889925138375248403387 257990834887707562872605081)
        ·
          refine ⟨193493126165780672154453811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 257990834887707562872605081 193493126165780672154453811)
          ·
            refine ⟨290239689248671008231680717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193493126165780672154453811 290239689248671008231680717)
            ·
              refine ⟨108839883468251628086880269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290239689248671008231680717 108839883468251628086880269)
              ·
                refine ⟨40814956300594360532580101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108839883468251628086880269 40814956300594360532580101)
                ·
                  refine ⟨7652804306361442599858769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40814956300594360532580101 7652804306361442599858769)
                  ·
                    refine ⟨5739603229771081949894077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7652804306361442599858769 5739603229771081949894077)
                    ·
                      refine ⟨2152351211164155731210279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5739603229771081949894077 2152351211164155731210279)
                      ·
                        rfl

theorem cell23_4191689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 3, 3, 4, 2, 3].length) (baseStart_4191689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191689 prefixEnd_4191689 := by exact prefixLift 4191689
  have htrace : WordTrace (prefixWord ++ tailWord_4191689) baseStart_4191689 baseEnd_4191689 := by
    simpa [prefixWord, tailWord_4191689, baseEnd_4191689] using wordTrace_append hprefix tailTrace_4191689
  have hstable : (prefixWord ++ tailWord_4191689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191689).length < 2 ^ (prefixWord ++ tailWord_4191689).sum := by decide
  have hdescent : baseEnd_4191689 < baseStart_4191689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191730 : List Nat := [3, 2, 1, 4, 1, 1, 3, 3, 1, 4]
def baseStart_4191730 : Nat := 118140960795 + 4191730 * 2 ^ 59
def prefixEnd_4191730 : Nat := 4983230072969 + 3 ^ 40 * 4191730 * 2
def baseEnd_4191730 : Nat := 717457421290330023599197

theorem tailTrace_4191730 : CollatzResearch.WordTrace tailWord_4191730 prefixEnd_4191730 717457421290330023599197 := by
  unfold tailWord_4191730
  simp only [CollatzResearch.WordTrace]
  refine ⟨38221238276021393833539161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101923302069390383556104429 38221238276021393833539161)
  ·
    refine ⟨28665928707016045375154371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38221238276021393833539161 28665928707016045375154371)
    ·
      refine ⟨42998893060524068062731557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28665928707016045375154371 42998893060524068062731557)
      ·
        refine ⟨8062292448848262761762167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 42998893060524068062731557 8062292448848262761762167)
        ·
          refine ⟨12093438673272394142643251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8062292448848262761762167 12093438673272394142643251)
          ·
            refine ⟨18140158009908591213964877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12093438673272394142643251 18140158009908591213964877)
            ·
              refine ⟨6802559253715721705236829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18140158009908591213964877 6802559253715721705236829)
              ·
                refine ⟨2550959720143395639463811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6802559253715721705236829 2550959720143395639463811)
                ·
                  refine ⟨3826439580215093459195717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2550959720143395639463811 3826439580215093459195717)
                  ·
                    refine ⟨717457421290330023599197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3826439580215093459195717 717457421290330023599197)
                    ·
                      rfl

theorem cell23_4191730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_4191730 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191730 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191730 prefixEnd_4191730 := by exact prefixLift 4191730
  have htrace : WordTrace (prefixWord ++ tailWord_4191730) baseStart_4191730 baseEnd_4191730 := by
    simpa [prefixWord, tailWord_4191730, baseEnd_4191730] using wordTrace_append hprefix tailTrace_4191730
  have hstable : (prefixWord ++ tailWord_4191730).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191730).length < 2 ^ (prefixWord ++ tailWord_4191730).sum := by decide
  have hdescent : baseEnd_4191730 < baseStart_4191730 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191774 : List Nat := [4, 3, 3, 1, 1, 1, 2, 1, 2, 2, 3]
def baseStart_4191774 : Nat := 118140960795 + 4191774 * 2 ^ 59
def prefixEnd_4191774 : Nat := 4983230072969 + 3 ^ 40 * 4191774 * 2
def baseEnd_4191774 : Nat := 2152394857019787898647389

theorem tailTrace_4191774 : CollatzResearch.WordTrace tailWord_4191774 prefixEnd_4191774 2152394857019787898647389 := by
  unfold tailWord_4191774
  simp only [CollatzResearch.WordTrace]
  refine ⟨19110819739490771356094797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101924371943950780565838917 19110819739490771356094797)
  ·
    refine ⟨7166557402309039258535549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19110819739490771356094797 7166557402309039258535549)
    ·
      refine ⟨2687459025865889721950831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7166557402309039258535549 2687459025865889721950831)
      ·
        refine ⟨4031188538798834582926247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2687459025865889721950831 4031188538798834582926247)
        ·
          refine ⟨6046782808198251874389371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4031188538798834582926247 6046782808198251874389371)
          ·
            refine ⟨9070174212297377811584057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6046782808198251874389371 9070174212297377811584057)
            ·
              refine ⟨6802630659223033358688043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9070174212297377811584057 6802630659223033358688043)
              ·
                refine ⟨10203945988834550038032065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6802630659223033358688043 10203945988834550038032065)
                ·
                  refine ⟨7652959491625912528524049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10203945988834550038032065 7652959491625912528524049)
                  ·
                    refine ⟨5739719618719434396393037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7652959491625912528524049 5739719618719434396393037)
                    ·
                      refine ⟨2152394857019787898647389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5739719618719434396393037 2152394857019787898647389)
                      ·
                        rfl

theorem cell23_4191774_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 1, 1, 2, 1, 2, 2, 3].length) (baseStart_4191774 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191774 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191774 prefixEnd_4191774 := by exact prefixLift 4191774
  have htrace : WordTrace (prefixWord ++ tailWord_4191774) baseStart_4191774 baseEnd_4191774 := by
    simpa [prefixWord, tailWord_4191774, baseEnd_4191774] using wordTrace_append hprefix tailTrace_4191774
  have hstable : (prefixWord ++ tailWord_4191774).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191774).length < 2 ^ (prefixWord ++ tailWord_4191774).sum := by decide
  have hdescent : baseEnd_4191774 < baseStart_4191774 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191774) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191786 : List Nat := [3, 1, 4, 1, 1, 1, 3, 2, 1, 6]
def baseStart_4191786 : Nat := 118140960795 + 4191786 * 2 ^ 59
def prefixEnd_4191786 : Nat := 4983230072969 + 3 ^ 40 * 4191786 * 2
def baseEnd_4191786 : Nat := 717467006262547283899111

theorem tailTrace_4191786 : CollatzResearch.WordTrace tailWord_4191786 prefixEnd_4191786 717467006262547283899111 := by
  unfold tailWord_4191786
  simp only [CollatzResearch.WordTrace]
  refine ⟨38221748897970674224548803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101924663727921797932130141 38221748897970674224548803)
  ·
    refine ⟨57332623346956011336823205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38221748897970674224548803 57332623346956011336823205)
    ·
      refine ⟨10749866877554252125654351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57332623346956011336823205 10749866877554252125654351)
      ·
        refine ⟨16124800316331378188481527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10749866877554252125654351 16124800316331378188481527)
        ·
          refine ⟨24187200474497067282722291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16124800316331378188481527 24187200474497067282722291)
          ·
            refine ⟨36280800711745600924083437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24187200474497067282722291 36280800711745600924083437)
            ·
              refine ⟨13605300266904600346531289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36280800711745600924083437 13605300266904600346531289)
              ·
                refine ⟨10203975200178450259898467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13605300266904600346531289 10203975200178450259898467)
                ·
                  refine ⟨15305962800267675389847701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10203975200178450259898467 15305962800267675389847701)
                  ·
                    refine ⟨717467006262547283899111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15305962800267675389847701 717467006262547283899111)
                    ·
                      rfl

theorem cell23_4191786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_4191786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191786 prefixEnd_4191786 := by exact prefixLift 4191786
  have htrace : WordTrace (prefixWord ++ tailWord_4191786) baseStart_4191786 baseEnd_4191786 := by
    simpa [prefixWord, tailWord_4191786, baseEnd_4191786] using wordTrace_append hprefix tailTrace_4191786
  have hstable : (prefixWord ++ tailWord_4191786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191786).length < 2 ^ (prefixWord ++ tailWord_4191786).sum := by decide
  have hdescent : baseEnd_4191786 < baseStart_4191786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191790 : List Nat := [4, 1, 3, 1, 2, 2, 3, 1, 1, 5]
def baseStart_4191790 : Nat := 118140960795 + 4191790 * 2 ^ 59
def prefixEnd_4191790 : Nat := 4983230072969 + 3 ^ 40 * 4191790 * 2
def baseEnd_4191790 : Nat := 717467690903419945349105

theorem tailTrace_4191790 : CollatzResearch.WordTrace tailWord_4191790 prefixEnd_4191790 717467690903419945349105 := by
  unfold tailWord_4191790
  simp only [CollatzResearch.WordTrace]
  refine ⟨19110892685483525697667603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101924760989245470387560549 19110892685483525697667603)
  ·
    refine ⟨28666339028225288546501405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19110892685483525697667603 28666339028225288546501405)
    ·
      refine ⟨10749877135584483204938027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28666339028225288546501405 10749877135584483204938027)
      ·
        refine ⟨16124815703376724807407041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10749877135584483204938027 16124815703376724807407041)
        ·
          refine ⟨12093611777532543605555281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16124815703376724807407041 12093611777532543605555281)
          ·
            refine ⟨9070208833149407704166461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12093611777532543605555281 9070208833149407704166461)
            ·
              refine ⟨3401328312431027889062423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9070208833149407704166461 3401328312431027889062423)
              ·
                refine ⟨5101992468646541833593635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3401328312431027889062423 5101992468646541833593635)
                ·
                  refine ⟨7652988702969812750390453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5101992468646541833593635 7652988702969812750390453)
                  ·
                    refine ⟨717467690903419945349105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7652988702969812750390453 717467690903419945349105)
                    ·
                      rfl

theorem cell23_4191790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_4191790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191790 prefixEnd_4191790 := by exact prefixLift 4191790
  have htrace : WordTrace (prefixWord ++ tailWord_4191790) baseStart_4191790 baseEnd_4191790 := by
    simpa [prefixWord, tailWord_4191790, baseEnd_4191790] using wordTrace_append hprefix tailTrace_4191790
  have hstable : (prefixWord ++ tailWord_4191790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191790).length < 2 ^ (prefixWord ++ tailWord_4191790).sum := by decide
  have hdescent : baseEnd_4191790 < baseStart_4191790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191804 : List Nat := [2, 2, 2, 2, 4, 2, 2, 2, 1, 1, 3]
def baseStart_4191804 : Nat := 118140960795 + 4191804 * 2 ^ 59
def prefixEnd_4191804 : Nat := 4983230072969 + 3 ^ 40 * 4191804 * 2
def baseEnd_4191804 : Nat := 2152410261439422781272251

theorem tailTrace_4191804 : CollatzResearch.WordTrace tailWord_4191804 prefixEnd_4191804 2152410261439422781272251 := by
  unfold tailWord_4191804
  simp only [CollatzResearch.WordTrace]
  refine ⟨76443826052908742986175233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101925101403878323981566977 76443826052908742986175233)
  ·
    refine ⟨57332869539681557239631425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76443826052908742986175233 57332869539681557239631425)
    ·
      refine ⟨42999652154761167929723569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57332869539681557239631425 42999652154761167929723569)
      ·
        refine ⟨32249739116070875947292677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42999652154761167929723569 32249739116070875947292677)
        ·
          refine ⟨6046826084263289240117377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32249739116070875947292677 6046826084263289240117377)
          ·
            refine ⟨4535119563197466930088033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6046826084263289240117377 4535119563197466930088033)
            ·
              refine ⟨3401339672398100197566025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4535119563197466930088033 3401339672398100197566025)
              ·
                refine ⟨2551004754298575148174519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3401339672398100197566025 2551004754298575148174519)
                ·
                  refine ⟨3826507131447862722261779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2551004754298575148174519 3826507131447862722261779)
                  ·
                    refine ⟨5739760697171794083392669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3826507131447862722261779 5739760697171794083392669)
                    ·
                      refine ⟨2152410261439422781272251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5739760697171794083392669 2152410261439422781272251)
                      ·
                        rfl

theorem cell23_4191804_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 2, 1, 1, 3].length) (baseStart_4191804 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191804 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191804 prefixEnd_4191804 := by exact prefixLift 4191804
  have htrace : WordTrace (prefixWord ++ tailWord_4191804) baseStart_4191804 baseEnd_4191804 := by
    simpa [prefixWord, tailWord_4191804, baseEnd_4191804] using wordTrace_append hprefix tailTrace_4191804
  have hstable : (prefixWord ++ tailWord_4191804).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191804).length < 2 ^ (prefixWord ++ tailWord_4191804).sum := by decide
  have hdescent : baseEnd_4191804 < baseStart_4191804 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191804) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191829 : List Nat := [1, 3, 2, 2, 1, 1, 1, 1, 4, 7]
def baseStart_4191829 : Nat := 118140960795 + 4191829 * 2 ^ 59
def prefixEnd_4191829 : Nat := 4983230072969 + 3 ^ 40 * 4191829 * 2
def baseEnd_4191829 : Nat := 717474366151928394486545

theorem tailTrace_4191829 : CollatzResearch.WordTrace tailWord_4191829 prefixEnd_4191829 717474366151928394486545 := by
  unfold tailWord_4191829
  simp only [CollatzResearch.WordTrace]
  refine ⟨152888563930726915242010541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101925709287151276828007027 152888563930726915242010541)
  ·
    refine ⟨57333211474022593215753953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152888563930726915242010541 57333211474022593215753953)
    ·
      refine ⟨42999908605516944911815465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57333211474022593215753953 42999908605516944911815465)
      ·
        refine ⟨32249931454137708683861599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 42999908605516944911815465 32249931454137708683861599)
        ·
          refine ⟨48374897181206563025792399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32249931454137708683861599 48374897181206563025792399)
          ·
            refine ⟨72562345771809844538688599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48374897181206563025792399 72562345771809844538688599)
            ·
              refine ⟨108843518657714766808032899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72562345771809844538688599 108843518657714766808032899)
              ·
                refine ⟨163265277986572150212049349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108843518657714766808032899 163265277986572150212049349)
                ·
                  refine ⟨30612239622482278164759253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163265277986572150212049349 30612239622482278164759253)
                  ·
                    refine ⟨717474366151928394486545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30612239622482278164759253 717474366151928394486545)
                    ·
                      rfl

theorem cell23_4191829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 1, 4, 7].length) (baseStart_4191829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191829 prefixEnd_4191829 := by exact prefixLift 4191829
  have htrace : WordTrace (prefixWord ++ tailWord_4191829) baseStart_4191829 baseEnd_4191829 := by
    simpa [prefixWord, tailWord_4191829, baseEnd_4191829] using wordTrace_append hprefix tailTrace_4191829
  have hstable : (prefixWord ++ tailWord_4191829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191829).length < 2 ^ (prefixWord ++ tailWord_4191829).sum := by decide
  have hdescent : baseEnd_4191829 < baseStart_4191829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191889 : List Nat := [1, 2, 2, 1, 1, 1, 1, 5, 9]
def baseStart_4191889 : Nat := 118140960795 + 4191889 * 2 ^ 59
def prefixEnd_4191889 : Nat := 4983230072969 + 3 ^ 40 * 4191889 * 2
def baseEnd_4191889 : Nat := 239161545255006105412151

theorem tailTrace_4191889 : CollatzResearch.WordTrace tailWord_4191889 prefixEnd_4191889 239161545255006105412151 := by
  unfold tailWord_4191889
  simp only [CollatzResearch.WordTrace]
  refine ⟨152890752310509545489194721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101927168207006363659463147 152890752310509545489194721)
  ·
    refine ⟨114668064232882159116896041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152890752310509545489194721 114668064232882159116896041)
    ·
      refine ⟨86001048174661619337672031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114668064232882159116896041 86001048174661619337672031)
      ·
        refine ⟨129001572261992429006508047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86001048174661619337672031 129001572261992429006508047)
        ·
          refine ⟨193502358392988643509762071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129001572261992429006508047 193502358392988643509762071)
          ·
            refine ⟨290253537589482965264643107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193502358392988643509762071 290253537589482965264643107)
            ·
              refine ⟨435380306384224447896964661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290253537589482965264643107 435380306384224447896964661)
              ·
                refine ⟨40816903723521041990340437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 435380306384224447896964661 40816903723521041990340437)
                ·
                  refine ⟨239161545255006105412151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40816903723521041990340437 239161545255006105412151)
                  ·
                    rfl

theorem cell23_4191889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 5, 9].length) (baseStart_4191889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191889 prefixEnd_4191889 := by exact prefixLift 4191889
  have htrace : WordTrace (prefixWord ++ tailWord_4191889) baseStart_4191889 baseEnd_4191889 := by
    simpa [prefixWord, tailWord_4191889, baseEnd_4191889] using wordTrace_append hprefix tailTrace_4191889
  have hstable : (prefixWord ++ tailWord_4191889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191889).length < 2 ^ (prefixWord ++ tailWord_4191889).sum := by decide
  have hdescent : baseEnd_4191889 < baseStart_4191889 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191917 : List Nat := [1, 5, 2, 1, 1, 1, 2, 4, 2, 2, 2]
def baseStart_4191917 : Nat := 118140960795 + 4191917 * 2 ^ 59
def prefixEnd_4191917 : Nat := 4983230072969 + 3 ^ 40 * 4191917 * 2
def baseEnd_4191917 : Nat := 2152468284753380839159231

theorem tailTrace_4191917 : CollatzResearch.WordTrace tailWord_4191917 prefixEnd_4191917 2152468284753380839159231 := by
  unfold tailWord_4191917
  simp only [CollatzResearch.WordTrace]
  refine ⟨152891773554408106271214005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101927849036272070847476003 152891773554408106271214005)
  ·
    refine ⟨14333603770725759962926313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152891773554408106271214005 14333603770725759962926313)
    ·
      refine ⟨10750202828044319972194735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14333603770725759962926313 10750202828044319972194735)
      ·
        refine ⟨16125304242066479958292103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10750202828044319972194735 16125304242066479958292103)
        ·
          refine ⟨24187956363099719937438155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16125304242066479958292103 24187956363099719937438155)
          ·
            refine ⟨36281934544649579906157233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24187956363099719937438155 36281934544649579906157233)
            ·
              refine ⟨27211450908487184929617925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36281934544649579906157233 27211450908487184929617925)
              ·
                refine ⟨5102147045341347174303361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27211450908487184929617925 5102147045341347174303361)
                ·
                  refine ⟨3826610284006010380727521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5102147045341347174303361 3826610284006010380727521)
                  ·
                    refine ⟨2869957713004507785545641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3826610284006010380727521 2869957713004507785545641)
                    ·
                      refine ⟨2152468284753380839159231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2869957713004507785545641 2152468284753380839159231)
                      ·
                        rfl

theorem cell23_4191917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 4, 2, 2, 2].length) (baseStart_4191917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191917 prefixEnd_4191917 := by exact prefixLift 4191917
  have htrace : WordTrace (prefixWord ++ tailWord_4191917) baseStart_4191917 baseEnd_4191917 := by
    simpa [prefixWord, tailWord_4191917, baseEnd_4191917] using wordTrace_append hprefix tailTrace_4191917
  have hstable : (prefixWord ++ tailWord_4191917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191917).length < 2 ^ (prefixWord ++ tailWord_4191917).sum := by decide
  have hdescent : baseEnd_4191917 < baseStart_4191917 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191934 : List Nat := [4, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2]
def baseStart_4191934 : Nat := 118140960795 + 4191934 * 2 ^ 59
def prefixEnd_4191934 : Nat := 4983230072969 + 3 ^ 40 * 4191934 * 2
def baseEnd_4191934 : Nat := 2152477013924507272646653

theorem tailTrace_4191934 : CollatzResearch.WordTrace tailWord_4191934 prefixEnd_4191934 2152477013924507272646653 := by
  unfold tailWord_4191934
  simp only [CollatzResearch.WordTrace]
  refine ⟨19111549199418314771822857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101928262396897678783055237 19111549199418314771822857)
  ·
    refine ⟨14333661899563736078867143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19111549199418314771822857 14333661899563736078867143)
    ·
      refine ⟨21500492849345604118300715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14333661899563736078867143 21500492849345604118300715)
      ·
        refine ⟨32250739274018406177451073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21500492849345604118300715 32250739274018406177451073)
        ·
          refine ⟨24188054455513804633088305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32250739274018406177451073 24188054455513804633088305)
          ·
            refine ⟨18141040841635353474816229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24188054455513804633088305 18141040841635353474816229)
            ·
              refine ⟨3401445157806628776528043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18141040841635353474816229 3401445157806628776528043)
              ·
                refine ⟨5102167736709943164792065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3401445157806628776528043 5102167736709943164792065)
                ·
                  refine ⟨3826625802532457373594049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5102167736709943164792065 3826625802532457373594049)
                  ·
                    refine ⟨2869969351899343030195537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3826625802532457373594049 2869969351899343030195537)
                    ·
                      refine ⟨2152477013924507272646653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2869969351899343030195537 2152477013924507272646653)
                      ·
                        rfl

theorem cell23_4191934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2].length) (baseStart_4191934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191934 prefixEnd_4191934 := by exact prefixLift 4191934
  have htrace : WordTrace (prefixWord ++ tailWord_4191934) baseStart_4191934 baseEnd_4191934 := by
    simpa [prefixWord, tailWord_4191934, baseEnd_4191934] using wordTrace_append hprefix tailTrace_4191934
  have hstable : (prefixWord ++ tailWord_4191934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191934).length < 2 ^ (prefixWord ++ tailWord_4191934).sum := by decide
  have hdescent : baseEnd_4191934 < baseStart_4191934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191936 : List Nat := [2, 1, 1, 2, 4, 1, 1, 2, 4, 5]
def baseStart_4191936 : Nat := 118140960795 + 4191936 * 2 ^ 59
def prefixEnd_4191936 : Nat := 4983230072969 + 3 ^ 40 * 4191936 * 2
def baseEnd_4191936 : Nat := 717492680295272088273881

theorem tailTrace_4191936 : CollatzResearch.WordTrace tailWord_4191936 prefixEnd_4191936 717492680295272088273881 := by
  unfold tailWord_4191936
  simp only [CollatzResearch.WordTrace]
  refine ⟨76446233270669636258077831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101928311027559515010770441 76446233270669636258077831)
  ·
    refine ⟨114669349906004454387116747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76446233270669636258077831 114669349906004454387116747)
    ·
      refine ⟨172004024859006681580675121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114669349906004454387116747 172004024859006681580675121)
      ·
        refine ⟨129003018644255011185506341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172004024859006681580675121 129003018644255011185506341)
        ·
          refine ⟨24188065995797814597282439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129003018644255011185506341 24188065995797814597282439)
          ·
            refine ⟨36282098993696721895923659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24188065995797814597282439 36282098993696721895923659)
            ·
              refine ⟨54423148490545082843885489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36282098993696721895923659 54423148490545082843885489)
              ·
                refine ⟨40817361367908812132914117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54423148490545082843885489 40817361367908812132914117)
                ·
                  refine ⟨7653255256482902274921397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40817361367908812132914117 7653255256482902274921397)
                  ·
                    refine ⟨717492680295272088273881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7653255256482902274921397 717492680295272088273881)
                    ·
                      rfl

theorem cell23_4191936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 4, 1, 1, 2, 4, 5].length) (baseStart_4191936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191936 prefixEnd_4191936 := by exact prefixLift 4191936
  have htrace : WordTrace (prefixWord ++ tailWord_4191936) baseStart_4191936 baseEnd_4191936 := by
    simpa [prefixWord, tailWord_4191936, baseEnd_4191936] using wordTrace_append hprefix tailTrace_4191936
  have hstable : (prefixWord ++ tailWord_4191936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191936).length < 2 ^ (prefixWord ++ tailWord_4191936).sum := by decide
  have hdescent : baseEnd_4191936 < baseStart_4191936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191938 : List Nat := [3, 5, 1, 2, 1, 2, 1, 2, 1, 3, 2]
def baseStart_4191938 : Nat := 118140960795 + 4191938 * 2 ^ 59
def prefixEnd_4191938 : Nat := 4983230072969 + 3 ^ 40 * 4191938 * 2
def baseEnd_4191938 : Nat := 2152479067847125256996635

theorem tailTrace_4191938 : CollatzResearch.WordTrace tailWord_4191938 prefixEnd_4191938 2152479067847125256996635 := by
  unfold tailWord_4191938
  simp only [CollatzResearch.WordTrace]
  refine ⟨38223134871833006714432117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101928359658221351238485645 38223134871833006714432117)
  ·
    refine ⟨3583418894234344379478011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 38223134871833006714432117 3583418894234344379478011)
    ·
      refine ⟨5375128341351516569217017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3583418894234344379478011 5375128341351516569217017)
      ·
        refine ⟨4031346256013637426912763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5375128341351516569217017 4031346256013637426912763)
        ·
          refine ⟨6047019384020456140369145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4031346256013637426912763 6047019384020456140369145)
          ·
            refine ⟨4535264538015342105276859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6047019384020456140369145 4535264538015342105276859)
            ·
              refine ⟨6802896807023013157915289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4535264538015342105276859 6802896807023013157915289)
              ·
                refine ⟨5102172605267259868436467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6802896807023013157915289 5102172605267259868436467)
                ·
                  refine ⟨7653258907900889802654701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5102172605267259868436467 7653258907900889802654701)
                  ·
                    refine ⟨2869972090462833675995513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7653258907900889802654701 2869972090462833675995513)
                    ·
                      refine ⟨2152479067847125256996635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2869972090462833675995513 2152479067847125256996635)
                      ·
                        rfl

theorem cell23_4191938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 2, 1, 3, 2].length) (baseStart_4191938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191938 prefixEnd_4191938 := by exact prefixLift 4191938
  have htrace : WordTrace (prefixWord ++ tailWord_4191938) baseStart_4191938 baseEnd_4191938 := by
    simpa [prefixWord, tailWord_4191938, baseEnd_4191938] using wordTrace_append hprefix tailTrace_4191938
  have hstable : (prefixWord ++ tailWord_4191938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191938).length < 2 ^ (prefixWord ++ tailWord_4191938).sum := by decide
  have hdescent : baseEnd_4191938 < baseStart_4191938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191953 : List Nat := [1, 2, 2, 1, 2, 5, 2, 1, 2, 5]
def baseStart_4191953 : Nat := 118140960795 + 4191953 * 2 ^ 59
def prefixEnd_4191953 : Nat := 4983230072969 + 3 ^ 40 * 4191953 * 2
def baseEnd_4191953 : Nat := 717495590018980899436355

theorem tailTrace_4191953 : CollatzResearch.WordTrace tailWord_4191953 prefixEnd_4191953 717495590018980899436355 := by
  unfold tailWord_4191953
  simp only [CollatzResearch.WordTrace]
  refine ⟨152893086582277684419524513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101928724388185122946349675 152893086582277684419524513)
  ·
    refine ⟨114669814936708263314643385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152893086582277684419524513 114669814936708263314643385)
    ·
      refine ⟨86002361202531197485982539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114669814936708263314643385 86002361202531197485982539)
      ·
        refine ⟨129003541803796796228973809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86002361202531197485982539 129003541803796796228973809)
        ·
          refine ⟨96752656352847597171730357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129003541803796796228973809 96752656352847597171730357)
          ·
            refine ⟨9070561533079462234849721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96752656352847597171730357 9070561533079462234849721)
            ·
              refine ⟨6802921149809596676137291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9070561533079462234849721 6802921149809596676137291)
              ·
                refine ⟨10204381724714395014205937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6802921149809596676137291 10204381724714395014205937)
                ·
                  refine ⟨7653286293535796260654453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10204381724714395014205937 7653286293535796260654453)
                  ·
                    refine ⟨717495590018980899436355, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7653286293535796260654453 717495590018980899436355)
                    ·
                      rfl

theorem cell23_4191953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 5, 2, 1, 2, 5].length) (baseStart_4191953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191953 prefixEnd_4191953 := by exact prefixLift 4191953
  have htrace : WordTrace (prefixWord ++ tailWord_4191953) baseStart_4191953 baseEnd_4191953 := by
    simpa [prefixWord, tailWord_4191953, baseEnd_4191953] using wordTrace_append hprefix tailTrace_4191953
  have hstable : (prefixWord ++ tailWord_4191953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191953).length < 2 ^ (prefixWord ++ tailWord_4191953).sum := by decide
  have hdescent : baseEnd_4191953 < baseStart_4191953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191973 : List Nat := [1, 3, 1, 4, 1, 1, 1, 4, 2, 1, 4]
def baseStart_4191973 : Nat := 118140960795 + 4191973 * 2 ^ 59
def prefixEnd_4191973 : Nat := 4983230072969 + 3 ^ 40 * 4191973 * 2
def baseEnd_4191973 : Nat := 2152497039670032620058973

theorem tailTrace_4191973 : CollatzResearch.WordTrace tailWord_4191973 prefixEnd_4191973 2152497039670032620058973 := by
  unfold tailWord_4191973
  simp only [CollatzResearch.WordTrace]
  refine ⟨152893816042205227835252573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101929210694803485223501715 152893816042205227835252573)
  ·
    refine ⟨57335181015826960438219715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152893816042205227835252573 57335181015826960438219715)
    ·
      refine ⟨86002771523740440657329573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57335181015826960438219715 86002771523740440657329573)
      ·
        refine ⟨16125519660701332623249295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86002771523740440657329573 16125519660701332623249295)
        ·
          refine ⟨24188279491051998934873943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16125519660701332623249295 24188279491051998934873943)
          ·
            refine ⟨36282419236577998402310915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24188279491051998934873943 36282419236577998402310915)
            ·
              refine ⟨54423628854866997603466373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36282419236577998402310915 54423628854866997603466373)
              ·
                refine ⟨10204430410287562050649945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54423628854866997603466373 10204430410287562050649945)
                ·
                  refine ⟨7653322807715671537987459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10204430410287562050649945 7653322807715671537987459)
                  ·
                    refine ⟨11479984211573507306981189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7653322807715671537987459 11479984211573507306981189)
                    ·
                      refine ⟨2152497039670032620058973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11479984211573507306981189 2152497039670032620058973)
                      ·
                        rfl

theorem cell23_4191973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_4191973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191973 prefixEnd_4191973 := by exact prefixLift 4191973
  have htrace : WordTrace (prefixWord ++ tailWord_4191973) baseStart_4191973 baseEnd_4191973 := by
    simpa [prefixWord, tailWord_4191973, baseEnd_4191973] using wordTrace_append hprefix tailTrace_4191973
  have hstable : (prefixWord ++ tailWord_4191973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191973).length < 2 ^ (prefixWord ++ tailWord_4191973).sum := by decide
  have hdescent : baseEnd_4191973 < baseStart_4191973 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191983 : List Nat := [1, 1, 2, 1, 5, 1, 2, 3, 3, 4]
def baseStart_4191983 : Nat := 118140960795 + 4191983 * 2 ^ 59
def prefixEnd_4191983 : Nat := 4983230072969 + 3 ^ 40 * 4191983 * 2
def baseEnd_4191983 : Nat := 717500724825525860311309

theorem tailTrace_4191983 : CollatzResearch.WordTrace tailWord_4191983 prefixEnd_4191983 717500724825525860311309 := by
  unfold tailWord_4191983
  simp only [CollatzResearch.WordTrace]
  refine ⟨152894180772168999543116603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101929453848112666362077735 152894180772168999543116603)
  ·
    refine ⟨229341271158253499314674905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152894180772168999543116603 229341271158253499314674905)
    ·
      refine ⟨172005953368690124486006179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229341271158253499314674905 172005953368690124486006179)
      ·
        refine ⟨258008930053035186729009269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172005953368690124486006179 258008930053035186729009269)
        ·
          refine ⟨24188337192472048755844619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 258008930053035186729009269 24188337192472048755844619)
          ·
            refine ⟨36282505788708073133766929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24188337192472048755844619 36282505788708073133766929)
            ·
              refine ⟨27211879341531054850325197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36282505788708073133766929 27211879341531054850325197)
              ·
                refine ⟨10204454753074145568871949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27211879341531054850325197 10204454753074145568871949)
                ·
                  refine ⟨3826670532402804588326981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10204454753074145568871949 3826670532402804588326981)
                  ·
                    refine ⟨717500724825525860311309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3826670532402804588326981 717500724825525860311309)
                    ·
                      rfl

theorem cell23_4191983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 3, 3, 4].length) (baseStart_4191983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191983 prefixEnd_4191983 := by exact prefixLift 4191983
  have htrace : WordTrace (prefixWord ++ tailWord_4191983) baseStart_4191983 baseEnd_4191983 := by
    simpa [prefixWord, tailWord_4191983, baseEnd_4191983] using wordTrace_append hprefix tailTrace_4191983
  have hstable : (prefixWord ++ tailWord_4191983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191983).length < 2 ^ (prefixWord ++ tailWord_4191983).sum := by decide
  have hdescent : baseEnd_4191983 < baseStart_4191983 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4191990 : List Nat := [5, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2]
def baseStart_4191990 : Nat := 118140960795 + 4191990 * 2 ^ 59
def prefixEnd_4191990 : Nat := 4983230072969 + 3 ^ 40 * 4191990 * 2
def baseEnd_4191990 : Nat := 2152505768841159053546395

theorem tailTrace_4191990 : CollatzResearch.WordTrace tailWord_4191990 prefixEnd_4191990 2152505768841159053546395 := by
  unfold tailWord_4191990
  simp only [CollatzResearch.WordTrace]
  refine ⟨9555902255196477483663839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101929624055429093159080949 9555902255196477483663839)
  ·
    refine ⟨14333853382794716225495759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9555902255196477483663839 14333853382794716225495759)
    ·
      refine ⟨21500780074192074338243639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14333853382794716225495759 21500780074192074338243639)
      ·
        refine ⟨32251170111288111507365459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21500780074192074338243639 32251170111288111507365459)
        ·
          refine ⟨48376755166932167261048189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32251170111288111507365459 48376755166932167261048189)
          ·
            refine ⟨18141283187599562722893071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48376755166932167261048189 18141283187599562722893071)
            ·
              refine ⟨27211924781399344084339607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18141283187599562722893071 27211924781399344084339607)
              ·
                refine ⟨40817887172099016126509411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27211924781399344084339607 40817887172099016126509411)
                ·
                  refine ⟨61226830758148524189764117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40817887172099016126509411 61226830758148524189764117)
                  ·
                    refine ⟨2870007691788212071395193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61226830758148524189764117 2870007691788212071395193)
                    ·
                      refine ⟨2152505768841159053546395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2870007691788212071395193 2152505768841159053546395)
                      ·
                        rfl

theorem cell23_4191990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 1, 1, 6, 2].length) (baseStart_4191990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4191990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4191990 prefixEnd_4191990 := by exact prefixLift 4191990
  have htrace : WordTrace (prefixWord ++ tailWord_4191990) baseStart_4191990 baseEnd_4191990 := by
    simpa [prefixWord, tailWord_4191990, baseEnd_4191990] using wordTrace_append hprefix tailTrace_4191990
  have hstable : (prefixWord ++ tailWord_4191990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4191990).length < 2 ^ (prefixWord ++ tailWord_4191990).sum := by decide
  have hdescent : baseEnd_4191990 < baseStart_4191990 := by decide
  rcases family_descends (prefixWord ++ tailWord_4191990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192007 : List Nat := [1, 1, 4, 4, 2, 2, 1, 1, 2, 1, 4]
def baseStart_4192007 : Nat := 118140960795 + 4192007 * 2 ^ 59
def prefixEnd_4192007 : Nat := 4983230072969 + 3 ^ 40 * 4192007 * 2
def baseEnd_4192007 : Nat := 2152514498012285487033817

theorem tailTrace_4192007 : CollatzResearch.WordTrace tailWord_4192007 prefixEnd_4192007 2152514498012285487033817 := by
  unfold tailWord_4192007
  simp only [CollatzResearch.WordTrace]
  refine ⟨152895056124082051641990275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101930037416054701094660183 152895056124082051641990275)
  ·
    refine ⟨229342584186123077462985413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152895056124082051641990275 229342584186123077462985413)
    ·
      refine ⟨43001734534898077024309765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229342584186123077462985413 43001734534898077024309765)
      ·
        refine ⟨8062825225293389442058081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43001734534898077024309765 8062825225293389442058081)
        ·
          refine ⟨6047118918970042081543561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8062825225293389442058081 6047118918970042081543561)
          ·
            refine ⟨4535339189227531561157671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6047118918970042081543561 4535339189227531561157671)
            ·
              refine ⟨6803008783841297341736507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4535339189227531561157671 6803008783841297341736507)
              ·
                refine ⟨10204513175761946012604761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6803008783841297341736507 10204513175761946012604761)
                ·
                  refine ⟨7653384881821459509453571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10204513175761946012604761 7653384881821459509453571)
                  ·
                    refine ⟨11480077322732189264180357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7653384881821459509453571 11480077322732189264180357)
                    ·
                      refine ⟨2152514498012285487033817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11480077322732189264180357 2152514498012285487033817)
                      ·
                        rfl

theorem cell23_4192007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 2, 2, 1, 1, 2, 1, 4].length) (baseStart_4192007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192007 prefixEnd_4192007 := by exact prefixLift 4192007
  have htrace : WordTrace (prefixWord ++ tailWord_4192007) baseStart_4192007 baseEnd_4192007 := by
    simpa [prefixWord, tailWord_4192007, baseEnd_4192007] using wordTrace_append hprefix tailTrace_4192007
  have hstable : (prefixWord ++ tailWord_4192007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192007).length < 2 ^ (prefixWord ++ tailWord_4192007).sum := by decide
  have hdescent : baseEnd_4192007 < baseStart_4192007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192010 : List Nat := [3, 1, 2, 2, 1, 3, 3, 1, 2, 2, 3]
def baseStart_4192010 : Nat := 118140960795 + 4192010 * 2 ^ 59
def prefixEnd_4192010 : Nat := 4983230072969 + 3 ^ 40 * 4192010 * 2
def baseEnd_4192010 : Nat := 2152516038454248975296303

theorem tailTrace_4192010 : CollatzResearch.WordTrace tailWord_4192010 prefixEnd_4192010 2152516038454248975296303 := by
  unfold tailWord_4192010
  simp only [CollatzResearch.WordTrace]
  refine ⟨38223791385767795788587371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101930110362047455436232989 38223791385767795788587371)
  ·
    refine ⟨57335687078651693682881057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38223791385767795788587371 57335687078651693682881057)
    ·
      refine ⟨43001765308988770262160793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57335687078651693682881057 43001765308988770262160793)
      ·
        refine ⟨32251323981741577696620595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43001765308988770262160793 32251323981741577696620595)
        ·
          refine ⟨48376985972612366544930893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32251323981741577696620595 48376985972612366544930893)
          ·
            refine ⟨18141369739729637454349085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48376985972612366544930893 18141369739729637454349085)
            ·
              refine ⟨6803013652398614045380907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18141369739729637454349085 6803013652398614045380907)
              ·
                refine ⟨10204520478597921068071361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6803013652398614045380907 10204520478597921068071361)
                ·
                  refine ⟨7653390358948440801053521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10204520478597921068071361 7653390358948440801053521)
                  ·
                    refine ⟨5740042769211330600790141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7653390358948440801053521 5740042769211330600790141)
                    ·
                      refine ⟨2152516038454248975296303, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5740042769211330600790141 2152516038454248975296303)
                      ·
                        rfl

theorem cell23_4192010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 3, 3, 1, 2, 2, 3].length) (baseStart_4192010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192010 prefixEnd_4192010 := by exact prefixLift 4192010
  have htrace : WordTrace (prefixWord ++ tailWord_4192010) baseStart_4192010 baseEnd_4192010 := by
    simpa [prefixWord, tailWord_4192010, baseEnd_4192010] using wordTrace_append hprefix tailTrace_4192010
  have hstable : (prefixWord ++ tailWord_4192010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192010).length < 2 ^ (prefixWord ++ tailWord_4192010).sum := by decide
  have hdescent : baseEnd_4192010 < baseStart_4192010 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192050 : List Nat := [3, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2]
def baseStart_4192050 : Nat := 118140960795 + 4192050 * 2 ^ 59
def prefixEnd_4192050 : Nat := 4983230072969 + 3 ^ 40 * 4192050 * 2
def baseEnd_4192050 : Nat := 2152536577680428818796119

theorem tailTrace_4192050 : CollatzResearch.WordTrace tailWord_4192050 prefixEnd_4192050 2152536577680428818796119 := by
  unfold tailWord_4192050
  simp only [CollatzResearch.WordTrace]
  refine ⟨38224156115731567496451401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101931082975284179990537069 38224156115731567496451401)
  ·
    refine ⟨28668117086798675622338551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38224156115731567496451401 28668117086798675622338551)
    ·
      refine ⟨43002175630198013433507827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28668117086798675622338551 43002175630198013433507827)
      ·
        refine ⟨64503263445297020150261741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43002175630198013433507827 64503263445297020150261741)
        ·
          refine ⟨24188723791986382556348153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64503263445297020150261741 24188723791986382556348153)
          ·
            refine ⟨18141542843989786917261115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24188723791986382556348153 18141542843989786917261115)
            ·
              refine ⟨27212314265984680375891673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18141542843989786917261115 27212314265984680375891673)
              ·
                refine ⟨20409235699488510281918755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27212314265984680375891673 20409235699488510281918755)
                ·
                  refine ⟨30613853549232765422878133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20409235699488510281918755 30613853549232765422878133)
                  ·
                    refine ⟨2870048770240571758394825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30613853549232765422878133 2870048770240571758394825)
                    ·
                      refine ⟨2152536577680428818796119, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2870048770240571758394825 2152536577680428818796119)
                      ·
                        rfl

theorem cell23_4192050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 1, 5, 2].length) (baseStart_4192050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192050 prefixEnd_4192050 := by exact prefixLift 4192050
  have htrace : WordTrace (prefixWord ++ tailWord_4192050) baseStart_4192050 baseEnd_4192050 := by
    simpa [prefixWord, tailWord_4192050, baseEnd_4192050] using wordTrace_append hprefix tailTrace_4192050
  have hstable : (prefixWord ++ tailWord_4192050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192050).length < 2 ^ (prefixWord ++ tailWord_4192050).sum := by decide
  have hdescent : baseEnd_4192050 < baseStart_4192050 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192073 : List Nat := [1, 2, 1, 1, 2, 4, 1, 1, 6, 4]
def baseStart_4192073 : Nat := 118140960795 + 4192073 * 2 ^ 59
def prefixEnd_4192073 : Nat := 4983230072969 + 3 ^ 40 * 4192073 * 2
def baseEnd_4192073 : Nat := 717516129245160742936171

theorem tailTrace_4192073 : CollatzResearch.WordTrace tailWord_4192073 prefixEnd_4192073 717516129245160742936171 := by
  unfold tailWord_4192073
  simp only [CollatzResearch.WordTrace]
  refine ⟨152897463341842944913892873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101931642227895296609261915 152897463341842944913892873)
  ·
    refine ⟨114673097506382208685419655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152897463341842944913892873 114673097506382208685419655)
    ·
      refine ⟨172009646259573313028129483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114673097506382208685419655 172009646259573313028129483)
      ·
        refine ⟨258014469389359969542194225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172009646259573313028129483 258014469389359969542194225)
        ·
          refine ⟨193510852042019977156645669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258014469389359969542194225 193510852042019977156645669)
          ·
            refine ⟨36283284757878745716871063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193510852042019977156645669 36283284757878745716871063)
            ·
              refine ⟨54424927136818118575306595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36283284757878745716871063 54424927136818118575306595)
              ·
                refine ⟨81637390705227177862959893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54424927136818118575306595 81637390705227177862959893)
                ·
                  refine ⟨3826752689307523962326245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81637390705227177862959893 3826752689307523962326245)
                  ·
                    refine ⟨717516129245160742936171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3826752689307523962326245 717516129245160742936171)
                    ·
                      rfl

theorem cell23_4192073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 1, 1, 6, 4].length) (baseStart_4192073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192073 prefixEnd_4192073 := by exact prefixLift 4192073
  have htrace : WordTrace (prefixWord ++ tailWord_4192073) baseStart_4192073 baseEnd_4192073 := by
    simpa [prefixWord, tailWord_4192073, baseEnd_4192073] using wordTrace_append hprefix tailTrace_4192073
  have hstable : (prefixWord ++ tailWord_4192073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192073).length < 2 ^ (prefixWord ++ tailWord_4192073).sum := by decide
  have hdescent : baseEnd_4192073 < baseStart_4192073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192077 : List Nat := [1, 6, 1, 2, 1, 1, 2, 3, 1, 5]
def baseStart_4192077 : Nat := 118140960795 + 4192077 * 2 ^ 59
def prefixEnd_4192077 : Nat := 4983230072969 + 3 ^ 40 * 4192077 * 2
def baseEnd_4192077 : Nat := 717516813886033404386165

theorem tailTrace_4192077 : CollatzResearch.WordTrace tailWord_4192077 prefixEnd_4192077 717516813886033404386165 := by
  unfold tailWord_4192077
  simp only [CollatzResearch.WordTrace]
  refine ⟨152897609233828453597038485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101931739489218969064692323 152897609233828453597038485)
  ·
    refine ⟨7167075432835708762361179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152897609233828453597038485 7167075432835708762361179)
    ·
      refine ⟨10750613149253563143541769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7167075432835708762361179 10750613149253563143541769)
      ·
        refine ⟨8062959861940172357656327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10750613149253563143541769 8062959861940172357656327)
        ·
          refine ⟨12094439792910258536484491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8062959861940172357656327 12094439792910258536484491)
          ·
            refine ⟨18141659689365387804726737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12094439792910258536484491 18141659689365387804726737)
            ·
              refine ⟨13606244767024040853545053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18141659689365387804726737 13606244767024040853545053)
              ·
                refine ⟨5102341787634015320079395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13606244767024040853545053 5102341787634015320079395)
                ·
                  refine ⟨7653512681451022980119093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5102341787634015320079395 7653512681451022980119093)
                  ·
                    refine ⟨717516813886033404386165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7653512681451022980119093 717516813886033404386165)
                    ·
                      rfl

theorem cell23_4192077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 1, 5].length) (baseStart_4192077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192077 prefixEnd_4192077 := by exact prefixLift 4192077
  have htrace : WordTrace (prefixWord ++ tailWord_4192077) baseStart_4192077 baseEnd_4192077 := by
    simpa [prefixWord, tailWord_4192077, baseEnd_4192077] using wordTrace_append hprefix tailTrace_4192077
  have hstable : (prefixWord ++ tailWord_4192077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192077).length < 2 ^ (prefixWord ++ tailWord_4192077).sum := by decide
  have hdescent : baseEnd_4192077 < baseStart_4192077 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192083 : List Nat := [1, 1, 1, 2, 1, 1, 3, 1, 7, 2, 3]
def baseStart_4192083 : Nat := 118140960795 + 4192083 * 2 ^ 59
def prefixEnd_4192083 : Nat := 4983230072969 + 3 ^ 40 * 4192083 * 2
def baseEnd_4192083 : Nat := 2152553522542027189683467

theorem tailTrace_4192083 : CollatzResearch.WordTrace tailWord_4192083 prefixEnd_4192083 2152553522542027189683467 := by
  unfold tailWord_4192083
  simp only [CollatzResearch.WordTrace]
  refine ⟨152897828071806716621756903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101931885381204477747837935 152897828071806716621756903)
  ·
    refine ⟨229346742107710074932635355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152897828071806716621756903 229346742107710074932635355)
    ·
      refine ⟨344020113161565112398953033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229346742107710074932635355 344020113161565112398953033)
      ·
        refine ⟨258015084871173834299214775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344020113161565112398953033 258015084871173834299214775)
        ·
          refine ⟨387022627306760751448822163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258015084871173834299214775 387022627306760751448822163)
          ·
            refine ⟨580533940960141127173233245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387022627306760751448822163 580533940960141127173233245)
            ·
              refine ⟨217700227860052922689962467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 580533940960141127173233245 217700227860052922689962467)
              ·
                refine ⟨326550341790079384034943701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 217700227860052922689962467 326550341790079384034943701)
                ·
                  refine ⟨7653523635704985563318993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 326550341790079384034943701 7653523635704985563318993)
                  ·
                    refine ⟨5740142726778739172489245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7653523635704985563318993 5740142726778739172489245)
                    ·
                      refine ⟨2152553522542027189683467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5740142726778739172489245 2152553522542027189683467)
                      ·
                        rfl

theorem cell23_4192083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 1, 7, 2, 3].length) (baseStart_4192083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192083 prefixEnd_4192083 := by exact prefixLift 4192083
  have htrace : WordTrace (prefixWord ++ tailWord_4192083) baseStart_4192083 baseEnd_4192083 := by
    simpa [prefixWord, tailWord_4192083, baseEnd_4192083] using wordTrace_append hprefix tailTrace_4192083
  have hstable : (prefixWord ++ tailWord_4192083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192083).length < 2 ^ (prefixWord ++ tailWord_4192083).sum := by decide
  have hdescent : baseEnd_4192083 < baseStart_4192083 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192090 : List Nat := [3, 1, 1, 2, 1, 3, 2, 4, 2, 4]
def baseStart_4192090 : Nat := 118140960795 + 4192090 * 2 ^ 59
def prefixEnd_4192090 : Nat := 4983230072969 + 3 ^ 40 * 4192090 * 2
def baseEnd_4192090 : Nat := 717519038968869554098645

theorem tailTrace_4192090 : CollatzResearch.WordTrace tailWord_4192090 prefixEnd_4192090 717519038968869554098645 := by
  unfold tailWord_4192090
  simp only [CollatzResearch.WordTrace]
  refine ⟨38224520845695339204315431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101932055588520904544841149 38224520845695339204315431)
  ·
    refine ⟨57336781268543008806473147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38224520845695339204315431 57336781268543008806473147)
    ·
      refine ⟨86005171902814513209709721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57336781268543008806473147 86005171902814513209709721)
      ·
        refine ⟨64503878927110884907282291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86005171902814513209709721 64503878927110884907282291)
        ·
          refine ⟨96755818390666327360923437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64503878927110884907282291 96755818390666327360923437)
          ·
            refine ⟨36283431896499872760346289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96755818390666327360923437 36283431896499872760346289)
            ·
              refine ⟨27212573922374904570259717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36283431896499872760346289 27212573922374904570259717)
              ·
                refine ⟨5102357610445294606923697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27212573922374904570259717 5102357610445294606923697)
                ·
                  refine ⟨3826768207833970955192773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5102357610445294606923697 3826768207833970955192773)
                  ·
                    refine ⟨717519038968869554098645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3826768207833970955192773 717519038968869554098645)
                    ·
                      rfl

theorem cell23_4192090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 4, 2, 4].length) (baseStart_4192090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192090 prefixEnd_4192090 := by exact prefixLift 4192090
  have htrace : WordTrace (prefixWord ++ tailWord_4192090) baseStart_4192090 baseEnd_4192090 := by
    simpa [prefixWord, tailWord_4192090, baseEnd_4192090] using wordTrace_append hprefix tailTrace_4192090
  have hstable : (prefixWord ++ tailWord_4192090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192090).length < 2 ^ (prefixWord ++ tailWord_4192090).sum := by decide
  have hdescent : baseEnd_4192090 < baseStart_4192090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192103 : List Nat := [1, 1, 5, 1, 2, 1, 4, 8]
def baseStart_4192103 : Nat := 118140960795 + 4192103 * 2 ^ 59
def prefixEnd_4192103 : Nat := 4983230072969 + 3 ^ 40 * 4192103 * 2
def baseEnd_4192103 : Nat := 79724584894633967090125

theorem tailTrace_4192103 : CollatzResearch.WordTrace tailWord_4192103 prefixEnd_4192103 79724584894633967090125 := by
  unfold tailWord_4192103
  simp only [CollatzResearch.WordTrace]
  refine ⟨152898557531734260037484963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101932371687822840024989975 152898557531734260037484963)
  ·
    refine ⟨229347836297601390056227445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152898557531734260037484963 229347836297601390056227445)
    ·
      refine ⟨21501359652900130317771323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 229347836297601390056227445 21501359652900130317771323)
      ·
        refine ⟨32252039479350195476656985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21501359652900130317771323 32252039479350195476656985)
        ·
          refine ⟨24189029609512646607492739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32252039479350195476656985 24189029609512646607492739)
          ·
            refine ⟨36283544414268969911239109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24189029609512646607492739 36283544414268969911239109)
            ·
              refine ⟨6803164577675431858357333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36283544414268969911239109 6803164577675431858357333)
              ·
                refine ⟨79724584894633967090125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 6803164577675431858357333 79724584894633967090125)
                ·
                  rfl

theorem cell23_4192103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 4, 8].length) (baseStart_4192103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192103 prefixEnd_4192103 := by exact prefixLift 4192103
  have htrace : WordTrace (prefixWord ++ tailWord_4192103) baseStart_4192103 baseEnd_4192103 := by
    simpa [prefixWord, tailWord_4192103, baseEnd_4192103] using wordTrace_append hprefix tailTrace_4192103
  have hstable : (prefixWord ++ tailWord_4192103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192103).length < 2 ^ (prefixWord ++ tailWord_4192103).sum := by decide
  have hdescent : baseEnd_4192103 < baseStart_4192103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192110 : List Nat := [4, 1, 2, 3, 1, 1, 2, 1, 1, 1, 6]
def baseStart_4192110 : Nat := 118140960795 + 4192110 * 2 ^ 59
def prefixEnd_4192110 : Nat := 4983230072969 + 3 ^ 40 * 4192110 * 2
def baseEnd_4192110 : Nat := 2152567386519698584045843

theorem tailTrace_4192110 : CollatzResearch.WordTrace tailWord_4192110 prefixEnd_4192110 2152567386519698584045843 := by
  unfold tailWord_4192110
  simp only [CollatzResearch.WordTrace]
  refine ⟨19112351605338612529123723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101932541895139266821993189 19112351605338612529123723)
  ·
    refine ⟨28668527408007918793685585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19112351605338612529123723 28668527408007918793685585)
    ·
      refine ⟨21501395556005939095264189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28668527408007918793685585 21501395556005939095264189)
      ·
        refine ⟨8063023333502227160724071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21501395556005939095264189 8063023333502227160724071)
        ·
          refine ⟨12094535000253340741086107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8063023333502227160724071 12094535000253340741086107)
          ·
            refine ⟨18141802500380011111629161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12094535000253340741086107 18141802500380011111629161)
            ·
              refine ⟨13606351875285008333721871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18141802500380011111629161 13606351875285008333721871)
              ·
                refine ⟨20409527812927512500582807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13606351875285008333721871 20409527812927512500582807)
                ·
                  refine ⟨30614291719391268750874211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20409527812927512500582807 30614291719391268750874211)
                  ·
                    refine ⟨45921437579086903126311317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30614291719391268750874211 45921437579086903126311317)
                    ·
                      refine ⟨2152567386519698584045843, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45921437579086903126311317 2152567386519698584045843)
                      ·
                        rfl

theorem cell23_4192110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 2, 1, 1, 1, 6].length) (baseStart_4192110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192110 prefixEnd_4192110 := by exact prefixLift 4192110
  have htrace : WordTrace (prefixWord ++ tailWord_4192110) baseStart_4192110 baseEnd_4192110 := by
    simpa [prefixWord, tailWord_4192110, baseEnd_4192110] using wordTrace_append hprefix tailTrace_4192110
  have hstable : (prefixWord ++ tailWord_4192110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192110).length < 2 ^ (prefixWord ++ tailWord_4192110).sum := by decide
  have hdescent : baseEnd_4192110 < baseStart_4192110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192148 : List Nat := [2, 4, 2, 1, 1, 2, 4, 2, 1, 2, 2]
def baseStart_4192148 : Nat := 118140960795 + 4192148 * 2 ^ 59
def prefixEnd_4192148 : Nat := 4983230072969 + 3 ^ 40 * 4192148 * 2
def baseEnd_4192148 : Nat := 2152586898784569435370669

theorem tailTrace_4192148 : CollatzResearch.WordTrace tailWord_4192148 prefixEnd_4192148 2152586898784569435370669 := by
  unfold tailWord_4192148
  simp only [CollatzResearch.WordTrace]
  refine ⟨76450099408285616361436549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101933465877714155148582065 76450099408285616361436549)
  ·
    refine ⟨14334393639053553067769353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76450099408285616361436549 14334393639053553067769353)
    ·
      refine ⟨10750795229290164800827015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14334393639053553067769353 10750795229290164800827015)
      ·
        refine ⟨16126192843935247201240523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10750795229290164800827015 16126192843935247201240523)
        ·
          refine ⟨24189289265902870801860785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16126192843935247201240523 24189289265902870801860785)
          ·
            refine ⟨18141966949427153101395589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24189289265902870801860785 18141966949427153101395589)
            ·
              refine ⟨3401618803017591206511673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18141966949427153101395589 3401618803017591206511673)
              ·
                refine ⟨2551214102263193404883755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3401618803017591206511673 2551214102263193404883755)
                ·
                  refine ⟨3826821153394790107325633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2551214102263193404883755 3826821153394790107325633)
                  ·
                    refine ⟨2870115865046092580494225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3826821153394790107325633 2870115865046092580494225)
                    ·
                      refine ⟨2152586898784569435370669, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2870115865046092580494225 2152586898784569435370669)
                      ·
                        rfl

theorem cell23_4192148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 4, 2, 1, 2, 2].length) (baseStart_4192148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192148 prefixEnd_4192148 := by exact prefixLift 4192148
  have htrace : WordTrace (prefixWord ++ tailWord_4192148) baseStart_4192148 baseEnd_4192148 := by
    simpa [prefixWord, tailWord_4192148, baseEnd_4192148] using wordTrace_append hprefix tailTrace_4192148
  have hstable : (prefixWord ++ tailWord_4192148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192148).length < 2 ^ (prefixWord ++ tailWord_4192148).sum := by decide
  have hdescent : baseEnd_4192148 < baseStart_4192148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192153 : List Nat := [1, 2, 1, 2, 1, 3, 3, 1, 2, 3, 4]
def baseStart_4192153 : Nat := 118140960795 + 4192153 * 2 ^ 59
def prefixEnd_4192153 : Nat := 4983230072969 + 3 ^ 40 * 4192153 * 2
def baseEnd_4192153 : Nat := 2152589466187841915808145

theorem tailTrace_4192153 : CollatzResearch.WordTrace tailWord_4192153 prefixEnd_4192153 2152589466187841915808145 := by
  unfold tailWord_4192153
  simp only [CollatzResearch.WordTrace]
  refine ⟨152900381181553118576805113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101933587454368745717870075 152900381181553118576805113)
  ·
    refine ⟨114675285886164838932603835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152900381181553118576805113 114675285886164838932603835)
    ·
      refine ⟨172012928829247258398905753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114675285886164838932603835 172012928829247258398905753)
      ·
        refine ⟨129009696621935443799179315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172012928829247258398905753 129009696621935443799179315)
        ·
          refine ⟨193514544932903165698768973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129009696621935443799179315 193514544932903165698768973)
          ·
            refine ⟨72567954349838687137038365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193514544932903165698768973 72567954349838687137038365)
            ·
              refine ⟨27212982881189507676389387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72567954349838687137038365 27212982881189507676389387)
              ·
                refine ⟨40819474321784261514584081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27212982881189507676389387 40819474321784261514584081)
                ·
                  refine ⟨30614605741338196135938061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40819474321784261514584081 30614605741338196135938061)
                  ·
                    refine ⟨11480477153001823550976773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30614605741338196135938061 11480477153001823550976773)
                    ·
                      refine ⟨2152589466187841915808145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11480477153001823550976773 2152589466187841915808145)
                      ·
                        rfl

theorem cell23_4192153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 3, 1, 2, 3, 4].length) (baseStart_4192153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192153 prefixEnd_4192153 := by exact prefixLift 4192153
  have htrace : WordTrace (prefixWord ++ tailWord_4192153) baseStart_4192153 baseEnd_4192153 := by
    simpa [prefixWord, tailWord_4192153, baseEnd_4192153] using wordTrace_append hprefix tailTrace_4192153
  have hstable : (prefixWord ++ tailWord_4192153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192153).length < 2 ^ (prefixWord ++ tailWord_4192153).sum := by decide
  have hdescent : baseEnd_4192153 < baseStart_4192153 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192157 : List Nat := [1, 4, 2, 1, 2, 2, 1, 2, 3, 3, 2]
def baseStart_4192157 : Nat := 118140960795 + 4192157 * 2 ^ 59
def prefixEnd_4192157 : Nat := 4983230072969 + 3 ^ 40 * 4192157 * 2
def baseEnd_4192157 : Nat := 2152591520110459900158127

theorem tailTrace_4192157 : CollatzResearch.WordTrace tailWord_4192157 prefixEnd_4192157 2152591520110459900158127 := by
  unfold tailWord_4192157
  simp only [CollatzResearch.WordTrace]
  refine ⟨152900527073538627259950725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101933684715692418173300483 152900527073538627259950725)
  ·
    refine ⟨28668848826288492611240761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152900527073538627259950725 28668848826288492611240761)
    ·
      refine ⟨21501636619716369458430571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28668848826288492611240761 21501636619716369458430571)
      ·
        refine ⟨32252454929574554187645857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21501636619716369458430571 32252454929574554187645857)
        ·
          refine ⟨24189341197180915640734393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32252454929574554187645857 24189341197180915640734393)
          ·
            refine ⟨18142005897885686730550795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24189341197180915640734393 18142005897885686730550795)
            ·
              refine ⟨27213008846828530095826193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18142005897885686730550795 27213008846828530095826193)
              ·
                refine ⟨20409756635121397571869645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27213008846828530095826193 20409756635121397571869645)
                ·
                  refine ⟨7653658738170524089451117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20409756635121397571869645 7653658738170524089451117)
                  ·
                    refine ⟨2870122026813946533544169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7653658738170524089451117 2870122026813946533544169)
                    ·
                      refine ⟨2152591520110459900158127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2870122026813946533544169 2152591520110459900158127)
                      ·
                        rfl

theorem cell23_4192157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 3, 3, 2].length) (baseStart_4192157 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192157 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192157 prefixEnd_4192157 := by exact prefixLift 4192157
  have htrace : WordTrace (prefixWord ++ tailWord_4192157) baseStart_4192157 baseEnd_4192157 := by
    simpa [prefixWord, tailWord_4192157, baseEnd_4192157] using wordTrace_append hprefix tailTrace_4192157
  have hstable : (prefixWord ++ tailWord_4192157).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192157).length < 2 ^ (prefixWord ++ tailWord_4192157).sum := by decide
  have hdescent : baseEnd_4192157 < baseStart_4192157 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192183 : List Nat := [1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 4]
def baseStart_4192183 : Nat := 118140960795 + 4192183 * 2 ^ 59
def prefixEnd_4192183 : Nat := 4983230072969 + 3 ^ 40 * 4192183 * 2
def baseEnd_4192183 : Nat := 2152604870607476798433007

theorem tailTrace_4192183 : CollatzResearch.WordTrace tailWord_4192183 prefixEnd_4192183 2152604870607476798433007 := by
  unfold tailWord_4192183
  simp only [CollatzResearch.WordTrace]
  refine ⟨152901475371444433700397203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101934316914296289133598135 152901475371444433700397203)
  ·
    refine ⟨229352213057166650550595805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152901475371444433700397203 229352213057166650550595805)
    ·
      refine ⟨86007079896437493956473427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229352213057166650550595805 86007079896437493956473427)
      ·
        refine ⟨129010619844656240934710141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86007079896437493956473427 129010619844656240934710141)
        ·
          refine ⟨48378982441746090350516303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129010619844656240934710141 48378982441746090350516303)
          ·
            refine ⟨72568473662619135525774455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48378982441746090350516303 72568473662619135525774455)
            ·
              refine ⟨108852710493928703288661683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72568473662619135525774455 108852710493928703288661683)
              ·
                refine ⟨163279065740893054932992525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108852710493928703288661683 163279065740893054932992525)
                ·
                  refine ⟨61229649652834895599872197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163279065740893054932992525 61229649652834895599872197)
                  ·
                    refine ⟨11480559309906542924976037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61229649652834895599872197 11480559309906542924976037)
                    ·
                      refine ⟨2152604870607476798433007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11480559309906542924976037 2152604870607476798433007)
                      ·
                        rfl

theorem cell23_4192183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 1, 1, 3, 4, 4].length) (baseStart_4192183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192183 prefixEnd_4192183 := by exact prefixLift 4192183
  have htrace : WordTrace (prefixWord ++ tailWord_4192183) baseStart_4192183 baseEnd_4192183 := by
    simpa [prefixWord, tailWord_4192183, baseEnd_4192183] using wordTrace_append hprefix tailTrace_4192183
  have hstable : (prefixWord ++ tailWord_4192183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192183).length < 2 ^ (prefixWord ++ tailWord_4192183).sum := by decide
  have hdescent : baseEnd_4192183 < baseStart_4192183 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192200 : List Nat := [2, 1, 3, 1, 4, 1, 1, 2, 2, 2, 4]
def baseStart_4192200 : Nat := 118140960795 + 4192200 * 2 ^ 59
def prefixEnd_4192200 : Nat := 4983230072969 + 3 ^ 40 * 4192200 * 2
def baseEnd_4192200 : Nat := 2152613599778603231920429

theorem tailTrace_4192200 : CollatzResearch.WordTrace tailWord_4192200 prefixEnd_4192200 2152613599778603231920429 := by
  unfold tailWord_4192200
  simp only [CollatzResearch.WordTrace]
  refine ⟨76451047706191422801883027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101934730274921897069177369 76451047706191422801883027)
  ·
    refine ⟨114676571559287134202824541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76451047706191422801883027 114676571559287134202824541)
    ·
      refine ⟨43003714334732675326059203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114676571559287134202824541 43003714334732675326059203)
      ·
        refine ⟨64505571502099012989088805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43003714334732675326059203 64505571502099012989088805)
        ·
          refine ⟨12094794656643564935454151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64505571502099012989088805 12094794656643564935454151)
          ·
            refine ⟨18142191984965347403181227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12094794656643564935454151 18142191984965347403181227)
            ·
              refine ⟨27213287977448021104771841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18142191984965347403181227 27213287977448021104771841)
              ·
                refine ⟨20409965983086015828578881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27213287977448021104771841 20409965983086015828578881)
                ·
                  refine ⟨15307474487314511871434161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20409965983086015828578881 15307474487314511871434161)
                  ·
                    refine ⟨11480605865485883903575621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15307474487314511871434161 11480605865485883903575621)
                    ·
                      refine ⟨2152613599778603231920429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11480605865485883903575621 2152613599778603231920429)
                      ·
                        rfl

theorem cell23_4192200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_4192200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192200 prefixEnd_4192200 := by exact prefixLift 4192200
  have htrace : WordTrace (prefixWord ++ tailWord_4192200) baseStart_4192200 baseEnd_4192200 := by
    simpa [prefixWord, tailWord_4192200, baseEnd_4192200] using wordTrace_append hprefix tailTrace_4192200
  have hstable : (prefixWord ++ tailWord_4192200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192200).length < 2 ^ (prefixWord ++ tailWord_4192200).sum := by decide
  have hdescent : baseEnd_4192200 < baseStart_4192200 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192204 : List Nat := [2, 2, 1, 4, 1, 3, 1, 1, 4, 2, 2]
def baseStart_4192204 : Nat := 118140960795 + 4192204 * 2 ^ 59
def prefixEnd_4192204 : Nat := 4983230072969 + 3 ^ 40 * 4192204 * 2
def baseEnd_4192204 : Nat := 2152615653701221216270411

theorem tailTrace_4192204 : CollatzResearch.WordTrace tailWord_4192204 prefixEnd_4192204 2152615653701221216270411 := by
  unfold tailWord_4192204
  simp only [CollatzResearch.WordTrace]
  refine ⟨76451120652184177143455833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101934827536245569524607777 76451120652184177143455833)
  ·
    refine ⟨57338340489138132857591875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76451120652184177143455833 57338340489138132857591875)
    ·
      refine ⟨86007510733707199286387813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57338340489138132857591875 86007510733707199286387813)
      ·
        refine ⟨16126408262570099866197715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86007510733707199286387813 16126408262570099866197715)
        ·
          refine ⟨24189612393855149799296573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16126408262570099866197715 24189612393855149799296573)
          ·
            refine ⟨9071104647695681174736215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24189612393855149799296573 9071104647695681174736215)
            ·
              refine ⟨13606656971543521762104323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9071104647695681174736215 13606656971543521762104323)
              ·
                refine ⟨20409985457315282643156485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13606656971543521762104323 20409985457315282643156485)
                ·
                  refine ⟨3826872273246615495591841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20409985457315282643156485 3826872273246615495591841)
                  ·
                    refine ⟨2870154204934961621693881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3826872273246615495591841 2870154204934961621693881)
                    ·
                      refine ⟨2152615653701221216270411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2870154204934961621693881 2152615653701221216270411)
                      ·
                        rfl

theorem cell23_4192204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 1, 4, 2, 2].length) (baseStart_4192204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192204 prefixEnd_4192204 := by exact prefixLift 4192204
  have htrace : WordTrace (prefixWord ++ tailWord_4192204) baseStart_4192204 baseEnd_4192204 := by
    simpa [prefixWord, tailWord_4192204, baseEnd_4192204] using wordTrace_append hprefix tailTrace_4192204
  have hstable : (prefixWord ++ tailWord_4192204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192204).length < 2 ^ (prefixWord ++ tailWord_4192204).sum := by decide
  have hdescent : baseEnd_4192204 < baseStart_4192204 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192221 : List Nat := [1, 4, 3, 1, 3, 2, 1, 1, 1, 4, 2]
def baseStart_4192221 : Nat := 118140960795 + 4192221 * 2 ^ 59
def prefixEnd_4192221 : Nat := 4983230072969 + 3 ^ 40 * 4192221 * 2
def baseEnd_4192221 : Nat := 2152624382872347649757833

theorem tailTrace_4192221 : CollatzResearch.WordTrace tailWord_4192221 prefixEnd_4192221 2152624382872347649757833 := by
  unfold tailWord_4192221
  simp only [CollatzResearch.WordTrace]
  refine ⟨152902861345306766190280517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101935240896871177460187011 152902861345306766190280517)
  ·
    refine ⟨28669286502245018660677597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152902861345306766190280517 28669286502245018660677597)
    ·
      refine ⟨10750982438341881997754099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28669286502245018660677597 10750982438341881997754099)
      ·
        refine ⟨16126473657512822996631149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10750982438341881997754099 16126473657512822996631149)
        ·
          refine ⟨6047427621567308623736681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16126473657512822996631149 6047427621567308623736681)
          ·
            refine ⟨4535570716175481467802511, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6047427621567308623736681 4535570716175481467802511)
            ·
              refine ⟨6803356074263222201703767, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4535570716175481467802511 6803356074263222201703767)
              ·
                refine ⟨10205034111394833302555651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6803356074263222201703767 10205034111394833302555651)
                ·
                  refine ⟨15307551167092249953833477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10205034111394833302555651 15307551167092249953833477)
                  ·
                    refine ⟨2870165843829796866343777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15307551167092249953833477 2870165843829796866343777)
                    ·
                      refine ⟨2152624382872347649757833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2870165843829796866343777 2152624382872347649757833)
                      ·
                        rfl

theorem cell23_4192221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 3, 2, 1, 1, 1, 4, 2].length) (baseStart_4192221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192221 prefixEnd_4192221 := by exact prefixLift 4192221
  have htrace : WordTrace (prefixWord ++ tailWord_4192221) baseStart_4192221 baseEnd_4192221 := by
    simpa [prefixWord, tailWord_4192221, baseEnd_4192221] using wordTrace_append hprefix tailTrace_4192221
  have hstable : (prefixWord ++ tailWord_4192221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192221).length < 2 ^ (prefixWord ++ tailWord_4192221).sum := by decide
  have hdescent : baseEnd_4192221 < baseStart_4192221 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192283 : List Nat := [1, 1, 1, 1, 1, 1, 3, 4, 10]
def baseStart_4192283 : Nat := 118140960795 + 4192283 * 2 ^ 59
def prefixEnd_4192283 : Nat := 4983230072969 + 3 ^ 40 * 4192283 * 2
def baseEnd_4192283 : Nat := 239184024296991823020283

theorem tailTrace_4192283 : CollatzResearch.WordTrace tailWord_4192283 prefixEnd_4192283 239184024296991823020283 := by
  unfold tailWord_4192283
  simp only [CollatzResearch.WordTrace]
  refine ⟨152905122671082150779037503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101936748447388100519358335 152905122671082150779037503)
  ·
    refine ⟨229357684006623226168556255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152905122671082150779037503 229357684006623226168556255)
    ·
      refine ⟨344036526009934839252834383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229357684006623226168556255 344036526009934839252834383)
      ·
        refine ⟨516054789014902258879251575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344036526009934839252834383 516054789014902258879251575)
        ·
          refine ⟨774082183522353388318877363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516054789014902258879251575 774082183522353388318877363)
          ·
            refine ⟨1161123275283530082478316045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 774082183522353388318877363 1161123275283530082478316045)
            ·
              refine ⟨435421228231323780929368517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1161123275283530082478316045 435421228231323780929368517)
              ·
                refine ⟨81641480293373208924256597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 435421228231323780929368517 81641480293373208924256597)
                ·
                  refine ⟨239184024296991823020283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 81641480293373208924256597 239184024296991823020283)
                  ·
                    rfl

theorem cell23_4192283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 3, 4, 10].length) (baseStart_4192283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192283 prefixEnd_4192283 := by exact prefixLift 4192283
  have htrace : WordTrace (prefixWord ++ tailWord_4192283) baseStart_4192283 baseEnd_4192283 := by
    simpa [prefixWord, tailWord_4192283, baseEnd_4192283] using wordTrace_append hprefix tailTrace_4192283
  have hstable : (prefixWord ++ tailWord_4192283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192283).length < 2 ^ (prefixWord ++ tailWord_4192283).sum := by decide
  have hdescent : baseEnd_4192283 < baseStart_4192283 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192317 : List Nat := [1, 4, 1, 3, 1, 1, 4, 2, 6]
def baseStart_4192317 : Nat := 118140960795 + 4192317 * 2 ^ 59
def prefixEnd_4192317 : Nat := 4983230072969 + 3 ^ 40 * 4192317 * 2
def baseEnd_4192317 : Nat := 239185964112797697128599

theorem tailTrace_4192317 : CollatzResearch.WordTrace tailWord_4192317 prefixEnd_4192317 239185964112797697128599 := by
  unfold tailWord_4192317
  simp only [CollatzResearch.WordTrace]
  refine ⟨152906362752958974585775205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101937575168639316390516803 152906362752958974585775205)
  ·
    refine ⟨28669943016179807734832851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152906362752958974585775205 28669943016179807734832851)
    ·
      refine ⟨43004914524269711602249277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28669943016179807734832851 43004914524269711602249277)
      ·
        refine ⟨16126842946601141850843479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43004914524269711602249277 16126842946601141850843479)
        ·
          refine ⟨24190264419901712776265219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16126842946601141850843479 24190264419901712776265219)
          ·
            refine ⟨36285396629852569164397829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24190264419901712776265219 36285396629852569164397829)
            ·
              refine ⟨6803511868097356718324593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36285396629852569164397829 6803511868097356718324593)
              ·
                refine ⟨5102633901073017538743445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6803511868097356718324593 5102633901073017538743445)
                ·
                  refine ⟨239185964112797697128599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5102633901073017538743445 239185964112797697128599)
                  ·
                    rfl

theorem cell23_4192317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 4, 2, 6].length) (baseStart_4192317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192317 prefixEnd_4192317 := by exact prefixLift 4192317
  have htrace : WordTrace (prefixWord ++ tailWord_4192317) baseStart_4192317 baseEnd_4192317 := by
    simpa [prefixWord, tailWord_4192317, baseEnd_4192317] using wordTrace_append hprefix tailTrace_4192317
  have hstable : (prefixWord ++ tailWord_4192317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192317).length < 2 ^ (prefixWord ++ tailWord_4192317).sum := by decide
  have hdescent : baseEnd_4192317 < baseStart_4192317 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192321 : List Nat := [1, 2, 5, 1, 2, 2, 1, 4, 1, 4]
def baseStart_4192321 : Nat := 118140960795 + 4192321 * 2 ^ 59
def prefixEnd_4192321 : Nat := 4983230072969 + 3 ^ 40 * 4192321 * 2
def baseEnd_4192321 : Nat := 717558576979265752835791

theorem tailTrace_4192321 : CollatzResearch.WordTrace tailWord_4192321 prefixEnd_4192321 717558576979265752835791 := by
  unfold tailWord_4192321
  simp only [CollatzResearch.WordTrace]
  refine ⟨152906508644944483268920817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101937672429962988845947211 152906508644944483268920817)
  ·
    refine ⟨114679881483708362451690613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152906508644944483268920817 114679881483708362451690613)
    ·
      refine ⟨10751238889097658979845995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114679881483708362451690613 10751238889097658979845995)
      ·
        refine ⟨16126858333646488469768993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10751238889097658979845995 16126858333646488469768993)
        ·
          refine ⟨12095143750234866352326745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16126858333646488469768993 12095143750234866352326745)
          ·
            refine ⟨9071357812676149764245059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12095143750234866352326745 9071357812676149764245059)
            ·
              refine ⟨13607036719014224646367589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9071357812676149764245059 13607036719014224646367589)
              ·
                refine ⟨2551319384815167121193923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13607036719014224646367589 2551319384815167121193923)
                ·
                  refine ⟨3826979077222750681790885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2551319384815167121193923 3826979077222750681790885)
                  ·
                    refine ⟨717558576979265752835791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3826979077222750681790885 717558576979265752835791)
                    ·
                      rfl

theorem cell23_4192321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_4192321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192321 prefixEnd_4192321 := by exact prefixLift 4192321
  have htrace : WordTrace (prefixWord ++ tailWord_4192321) baseStart_4192321 baseEnd_4192321 := by
    simpa [prefixWord, tailWord_4192321, baseEnd_4192321] using wordTrace_append hprefix tailTrace_4192321
  have hstable : (prefixWord ++ tailWord_4192321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192321).length < 2 ^ (prefixWord ++ tailWord_4192321).sum := by decide
  have hdescent : baseEnd_4192321 < baseStart_4192321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192337 : List Nat := [1, 2, 2, 1, 3, 1, 1, 4, 1, 5, 2]
def baseStart_4192337 : Nat := 118140960795 + 4192337 * 2 ^ 59
def prefixEnd_4192337 : Nat := 4983230072969 + 3 ^ 40 * 4192337 * 2
def baseEnd_4192337 : Nat := 2152683946628269195907299

theorem tailTrace_4192337 : CollatzResearch.WordTrace tailWord_4192337 prefixEnd_4192337 2152683946628269195907299 := by
  unfold tailWord_4192337
  simp only [CollatzResearch.WordTrace]
  refine ⟨152907092212886518001503265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101938061475257678667668843 152907092212886518001503265)
  ·
    refine ⟨114680319159664888501127449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152907092212886518001503265 114680319159664888501127449)
    ·
      refine ⟨86010239369748666375845587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114680319159664888501127449 86010239369748666375845587)
      ·
        refine ⟨129015359054622999563768381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86010239369748666375845587 129015359054622999563768381)
        ·
          refine ⟨48380759645483624836413143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129015359054622999563768381 48380759645483624836413143)
          ·
            refine ⟨72571139468225437254619715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48380759645483624836413143 72571139468225437254619715)
            ·
              refine ⟨108856709202338155881929573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72571139468225437254619715 108856709202338155881929573)
              ·
                refine ⟨20410632975438404227861795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 108856709202338155881929573 20410632975438404227861795)
                ·
                  refine ⟨30615949463157606341792693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20410632975438404227861795 30615949463157606341792693)
                  ·
                    refine ⟨2870245262171025594543065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30615949463157606341792693 2870245262171025594543065)
                    ·
                      refine ⟨2152683946628269195907299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2870245262171025594543065 2152683946628269195907299)
                      ·
                        rfl

theorem cell23_4192337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 1, 4, 1, 5, 2].length) (baseStart_4192337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192337 prefixEnd_4192337 := by exact prefixLift 4192337
  have htrace : WordTrace (prefixWord ++ tailWord_4192337) baseStart_4192337 baseEnd_4192337 := by
    simpa [prefixWord, tailWord_4192337, baseEnd_4192337] using wordTrace_append hprefix tailTrace_4192337
  have hstable : (prefixWord ++ tailWord_4192337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192337).length < 2 ^ (prefixWord ++ tailWord_4192337).sum := by decide
  have hdescent : baseEnd_4192337 < baseStart_4192337 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192340 : List Nat := [2, 4, 1, 1, 1, 1, 1, 1, 1, 3, 7]
def baseStart_4192340 : Nat := 118140960795 + 4192340 * 2 ^ 59
def prefixEnd_4192340 : Nat := 4983230072969 + 3 ^ 40 * 4192340 * 2
def baseEnd_4192340 : Nat := 2152685487070232684169785

theorem tailTrace_4192340 : CollatzResearch.WordTrace tailWord_4192340 prefixEnd_4192340 2152685487070232684169785 := by
  unfold tailWord_4192340
  simp only [CollatzResearch.WordTrace]
  refine ⟨76453600815937824756931237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101938134421250433009241649 76453600815937824756931237)
  ·
    refine ⟨14335050152988342141924607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76453600815937824756931237 14335050152988342141924607)
    ·
      refine ⟨21502575229482513212886911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14335050152988342141924607 21502575229482513212886911)
      ·
        refine ⟨32253862844223769819330367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21502575229482513212886911 32253862844223769819330367)
        ·
          refine ⟨48380794266335654728995551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32253862844223769819330367 48380794266335654728995551)
          ·
            refine ⟨72571191399503482093493327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48380794266335654728995551 72571191399503482093493327)
            ·
              refine ⟨108856787099255223140239991, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72571191399503482093493327 108856787099255223140239991)
              ·
                refine ⟨163285180648882834710359987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108856787099255223140239991 163285180648882834710359987)
                ·
                  refine ⟨244927770973324252065539981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163285180648882834710359987 244927770973324252065539981)
                  ·
                    refine ⟨91847914114996594524577493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 244927770973324252065539981 91847914114996594524577493)
                    ·
                      refine ⟨2152685487070232684169785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91847914114996594524577493 2152685487070232684169785)
                      ·
                        rfl

theorem cell23_4192340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_4192340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192340 prefixEnd_4192340 := by exact prefixLift 4192340
  have htrace : WordTrace (prefixWord ++ tailWord_4192340) baseStart_4192340 baseEnd_4192340 := by
    simpa [prefixWord, tailWord_4192340, baseEnd_4192340] using wordTrace_append hprefix tailTrace_4192340
  have hstable : (prefixWord ++ tailWord_4192340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192340).length < 2 ^ (prefixWord ++ tailWord_4192340).sum := by decide
  have hdescent : baseEnd_4192340 < baseStart_4192340 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192344 : List Nat := [2, 1, 2, 2, 1, 5, 1, 2, 3, 1, 3]
def baseStart_4192344 : Nat := 118140960795 + 4192344 * 2 ^ 59
def prefixEnd_4192344 : Nat := 4983230072969 + 3 ^ 40 * 4192344 * 2
def baseEnd_4192344 : Nat := 2152687540992850668519767

theorem tailTrace_4192344 : CollatzResearch.WordTrace tailWord_4192344 prefixEnd_4192344 2152687540992850668519767 := by
  unfold tailWord_4192344
  simp only [CollatzResearch.WordTrace]
  refine ⟨76453673761930579098504043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101938231682574105464672057 76453673761930579098504043)
  ·
    refine ⟨114680510642895868647756065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76453673761930579098504043 114680510642895868647756065)
    ·
      refine ⟨86010382982171901485817049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114680510642895868647756065 86010382982171901485817049)
      ·
        refine ⟨64507787236628926114362787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86010382982171901485817049 64507787236628926114362787)
        ·
          refine ⟨96761680854943389171544181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64507787236628926114362787 96761680854943389171544181)
          ·
            refine ⟨9071407580150942734832267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96761680854943389171544181 9071407580150942734832267)
            ·
              refine ⟨13607111370226414102248401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9071407580150942734832267 13607111370226414102248401)
              ·
                refine ⟨10205333527669810576686301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13607111370226414102248401 10205333527669810576686301)
                ·
                  refine ⟨3827000072876178966257363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10205333527669810576686301 3827000072876178966257363)
                  ·
                    refine ⟨5740500109314268449386045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3827000072876178966257363 5740500109314268449386045)
                    ·
                      refine ⟨2152687540992850668519767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5740500109314268449386045 2152687540992850668519767)
                      ·
                        rfl

theorem cell23_4192344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 5, 1, 2, 3, 1, 3].length) (baseStart_4192344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192344 prefixEnd_4192344 := by exact prefixLift 4192344
  have htrace : WordTrace (prefixWord ++ tailWord_4192344) baseStart_4192344 baseEnd_4192344 := by
    simpa [prefixWord, tailWord_4192344, baseEnd_4192344] using wordTrace_append hprefix tailTrace_4192344
  have hstable : (prefixWord ++ tailWord_4192344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192344).length < 2 ^ (prefixWord ++ tailWord_4192344).sum := by decide
  have hdescent : baseEnd_4192344 < baseStart_4192344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192361 : List Nat := [1, 2, 1, 1, 1, 5, 4, 3, 1, 1, 3]
def baseStart_4192361 : Nat := 118140960795 + 4192361 * 2 ^ 59
def prefixEnd_4192361 : Nat := 4983230072969 + 3 ^ 40 * 4192361 * 2
def baseEnd_4192361 : Nat := 2152696270163977102007189

theorem tailTrace_4192361 : CollatzResearch.WordTrace tailWord_4192361 prefixEnd_4192361 2152696270163977102007189 := by
  unfold tailWord_4192361
  simp only [CollatzResearch.WordTrace]
  refine ⟨152907967564799570100376937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101938645043199713400251291 152907967564799570100376937)
  ·
    refine ⟨114680975673599677575282703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152907967564799570100376937 114680975673599677575282703)
    ·
      refine ⟨172021463510399516362924055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114680975673599677575282703 172021463510399516362924055)
      ·
        refine ⟨258032195265599274544386083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172021463510399516362924055 258032195265599274544386083)
        ·
          refine ⟨387048292898398911816579125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258032195265599274544386083 387048292898398911816579125)
          ·
            refine ⟨36285777459224897982804293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 387048292898398911816579125 36285777459224897982804293)
            ·
              refine ⟨6803583273604668371775805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36285777459224897982804293 6803583273604668371775805)
              ·
                refine ⟨2551343727601750639415927, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6803583273604668371775805 2551343727601750639415927)
                ·
                  refine ⟨3827015591402625959123891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2551343727601750639415927 3827015591402625959123891)
                  ·
                    refine ⟨5740523387103938938685837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3827015591402625959123891 5740523387103938938685837)
                    ·
                      refine ⟨2152696270163977102007189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5740523387103938938685837 2152696270163977102007189)
                      ·
                        rfl

theorem cell23_4192361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 4, 3, 1, 1, 3].length) (baseStart_4192361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192361 prefixEnd_4192361 := by exact prefixLift 4192361
  have htrace : WordTrace (prefixWord ++ tailWord_4192361) baseStart_4192361 baseEnd_4192361 := by
    simpa [prefixWord, tailWord_4192361, baseEnd_4192361] using wordTrace_append hprefix tailTrace_4192361
  have hstable : (prefixWord ++ tailWord_4192361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192361).length < 2 ^ (prefixWord ++ tailWord_4192361).sum := by decide
  have hdescent : baseEnd_4192361 < baseStart_4192361 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192364 : List Nat := [2, 2, 1, 1, 3, 3, 4, 1, 1, 5]
def baseStart_4192364 : Nat := 118140960795 + 4192364 * 2 ^ 59
def prefixEnd_4192364 : Nat := 4983230072969 + 3 ^ 40 * 4192364 * 2
def baseEnd_4192364 : Nat := 717565936868646863423225

theorem tailTrace_4192364 : CollatzResearch.WordTrace tailWord_4192364 prefixEnd_4192364 717565936868646863423225 := by
  unfold tailWord_4192364
  simp only [CollatzResearch.WordTrace]
  refine ⟨76454038491894350806368073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101938717989192467741824097 76454038491894350806368073)
  ·
    refine ⟨57340528868920763104776055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76454038491894350806368073 57340528868920763104776055)
    ·
      refine ⟨86010793303381144657164083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57340528868920763104776055 86010793303381144657164083)
      ·
        refine ⟨129016189955071716985746125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86010793303381144657164083 129016189955071716985746125)
        ·
          refine ⟨48381071233151893869654797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129016189955071716985746125 48381071233151893869654797)
          ·
            refine ⟨18142901712431960201120549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48381071233151893869654797 18142901712431960201120549)
            ·
              refine ⟨3401794071080992537710103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18142901712431960201120549 3401794071080992537710103)
              ·
                refine ⟨5102691106621488806565155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3401794071080992537710103 5102691106621488806565155)
                ·
                  refine ⟨7654036659932233209847733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5102691106621488806565155 7654036659932233209847733)
                  ·
                    refine ⟨717565936868646863423225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7654036659932233209847733 717565936868646863423225)
                    ·
                      rfl

theorem cell23_4192364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 5].length) (baseStart_4192364 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192364 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192364 prefixEnd_4192364 := by exact prefixLift 4192364
  have htrace : WordTrace (prefixWord ++ tailWord_4192364) baseStart_4192364 baseEnd_4192364 := by
    simpa [prefixWord, tailWord_4192364, baseEnd_4192364] using wordTrace_append hprefix tailTrace_4192364
  have hstable : (prefixWord ++ tailWord_4192364).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192364).length < 2 ^ (prefixWord ++ tailWord_4192364).sum := by decide
  have hdescent : baseEnd_4192364 < baseStart_4192364 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192387 : List Nat := [1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 5]
def baseStart_4192387 : Nat := 118140960795 + 4192387 * 2 ^ 59
def prefixEnd_4192387 : Nat := 4983230072969 + 3 ^ 40 * 4192387 * 2
def baseEnd_4192387 : Nat := 2152709620660994000282069

theorem tailTrace_4192387 : CollatzResearch.WordTrace tailWord_4192387 prefixEnd_4192387 2152709620660994000282069 := by
  unfold tailWord_4192387
  simp only [CollatzResearch.WordTrace]
  refine ⟨152908915862705376540823415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101939277241803584360548943 152908915862705376540823415)
  ·
    refine ⟨229363373794058064811235123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152908915862705376540823415 229363373794058064811235123)
    ·
      refine ⟨344045060691087097216852685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229363373794058064811235123 344045060691087097216852685)
      ·
        refine ⟨129016897759157661456319757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 344045060691087097216852685 129016897759157661456319757)
        ·
          refine ⟨48381336659684123046119909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129016897759157661456319757 48381336659684123046119909)
          ·
            refine ⟨9071500623690773071147483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48381336659684123046119909 9071500623690773071147483)
            ·
              refine ⟨13607250935536159606721225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9071500623690773071147483 13607250935536159606721225)
              ·
                refine ⟨10205438201652119705040919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13607250935536159606721225 10205438201652119705040919)
                ·
                  refine ⟨15308157302478179557561379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10205438201652119705040919 15308157302478179557561379)
                  ·
                    refine ⟨22962235953717269336342069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15308157302478179557561379 22962235953717269336342069)
                    ·
                      refine ⟨2152709620660994000282069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22962235953717269336342069 2152709620660994000282069)
                      ·
                        rfl

theorem cell23_4192387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 1, 2, 1, 1, 5].length) (baseStart_4192387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192387 prefixEnd_4192387 := by exact prefixLift 4192387
  have htrace : WordTrace (prefixWord ++ tailWord_4192387) baseStart_4192387 baseEnd_4192387 := by
    simpa [prefixWord, tailWord_4192387, baseEnd_4192387] using wordTrace_append hprefix tailTrace_4192387
  have hstable : (prefixWord ++ tailWord_4192387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192387).length < 2 ^ (prefixWord ++ tailWord_4192387).sum := by decide
  have hdescent : baseEnd_4192387 < baseStart_4192387 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192394 : List Nat := [3, 1, 2, 3, 1, 4, 1, 1, 1, 6]
def baseStart_4192394 : Nat := 118140960795 + 4192394 * 2 ^ 59
def prefixEnd_4192394 : Nat := 4983230072969 + 3 ^ 40 * 4192394 * 2
def baseEnd_4192394 : Nat := 717571071675191824298179

theorem tailTrace_4192394 : CollatzResearch.WordTrace tailWord_4192394 prefixEnd_4192394 717571071675191824298179 := by
  unfold tailWord_4192394
  simp only [CollatzResearch.WordTrace]
  refine ⟨38227292793420004184082059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101939447449120011157552157 38227292793420004184082059)
  ·
    refine ⟨57340939190130006276123089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38227292793420004184082059 57340939190130006276123089)
    ·
      refine ⟨43005704392597504707092317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57340939190130006276123089 43005704392597504707092317)
      ·
        refine ⟨16127139147224064265159619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43005704392597504707092317 16127139147224064265159619)
        ·
          refine ⟨24190708720836096397739429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16127139147224064265159619 24190708720836096397739429)
          ·
            refine ⟨4535757885156768074576143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24190708720836096397739429 4535757885156768074576143)
            ·
              refine ⟨6803636827735152111864215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4535757885156768074576143 6803636827735152111864215)
              ·
                refine ⟨10205455241602728167796323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6803636827735152111864215 10205455241602728167796323)
                ·
                  refine ⟨15308182862404092251694485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10205455241602728167796323 15308182862404092251694485)
                  ·
                    refine ⟨717571071675191824298179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15308182862404092251694485 717571071675191824298179)
                    ·
                      rfl

theorem cell23_4192394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_4192394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192394 prefixEnd_4192394 := by exact prefixLift 4192394
  have htrace : WordTrace (prefixWord ++ tailWord_4192394) baseStart_4192394 baseEnd_4192394 := by
    simpa [prefixWord, tailWord_4192394, baseEnd_4192394] using wordTrace_append hprefix tailTrace_4192394
  have hstable : (prefixWord ++ tailWord_4192394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192394).length < 2 ^ (prefixWord ++ tailWord_4192394).sum := by decide
  have hdescent : baseEnd_4192394 < baseStart_4192394 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192406 : List Nat := [5, 3, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_4192406 : Nat := 118140960795 + 4192406 * 2 ^ 59
def prefixEnd_4192406 : Nat := 4983230072969 + 3 ^ 40 * 4192406 * 2
def baseEnd_4192406 : Nat := 717573125597809808648161

theorem tailTrace_4192406 : CollatzResearch.WordTrace tailWord_4192406 prefixEnd_4192406 717573125597809808648161 := by
  unfold tailWord_4192406
  simp only [CollatzResearch.WordTrace]
  refine ⟨9556850553102283924110317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 101939739233091028523843381 9556850553102283924110317)
  ·
    refine ⟨3583818957413356471541369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 9556850553102283924110317 3583818957413356471541369)
    ·
      refine ⟨2687864218060017353656027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3583818957413356471541369 2687864218060017353656027)
      ·
        refine ⟨4031796327090026030484041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2687864218060017353656027 4031796327090026030484041)
        ·
          refine ⟨3023847245317519522863031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4031796327090026030484041 3023847245317519522863031)
          ·
            refine ⟨4535770867976279284294547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3023847245317519522863031 4535770867976279284294547)
            ·
              refine ⟨6803656301964418926441821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4535770867976279284294547 6803656301964418926441821)
              ·
                refine ⟨2551371113236657097415683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6803656301964418926441821 2551371113236657097415683)
                ·
                  refine ⟨3827056669854985646123525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2551371113236657097415683 3827056669854985646123525)
                  ·
                    refine ⟨717573125597809808648161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3827056669854985646123525 717573125597809808648161)
                    ·
                      rfl

theorem cell23_4192406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_4192406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192406 prefixEnd_4192406 := by exact prefixLift 4192406
  have htrace : WordTrace (prefixWord ++ tailWord_4192406) baseStart_4192406 baseEnd_4192406 := by
    simpa [prefixWord, tailWord_4192406, baseEnd_4192406] using wordTrace_append hprefix tailTrace_4192406
  have hstable : (prefixWord ++ tailWord_4192406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192406).length < 2 ^ (prefixWord ++ tailWord_4192406).sum := by decide
  have hdescent : baseEnd_4192406 < baseStart_4192406 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192407 : List Nat := [1, 1, 3, 3, 4, 1, 1, 9]
def baseStart_4192407 : Nat := 118140960795 + 4192407 * 2 ^ 59
def prefixEnd_4192407 : Nat := 4983230072969 + 3 ^ 40 * 4192407 * 2
def baseEnd_4192407 : Nat := 79730366306447552667851

theorem tailTrace_4192407 : CollatzResearch.WordTrace tailWord_4192407 prefixEnd_4192407 79730366306447552667851 := by
  unfold tailWord_4192407
  simp only [CollatzResearch.WordTrace]
  refine ⟨152909645322632919956551475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101939763548421946637700983 152909645322632919956551475)
  ·
    refine ⟨229364467983949379934827213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152909645322632919956551475 229364467983949379934827213)
    ·
      refine ⟨86011675493981017475560205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229364467983949379934827213 86011675493981017475560205)
      ·
        refine ⟨32254378310242881553335077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86011675493981017475560205 32254378310242881553335077)
        ·
          refine ⟨6047695933170540291250327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32254378310242881553335077 6047695933170540291250327)
          ·
            refine ⟨9071543899755810436875491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6047695933170540291250327 9071543899755810436875491)
            ·
              refine ⟨13607315849633715655313237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9071543899755810436875491 13607315849633715655313237)
              ·
                refine ⟨79730366306447552667851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13607315849633715655313237 79730366306447552667851)
                ·
                  rfl

theorem cell23_4192407_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 4, 1, 1, 9].length) (baseStart_4192407 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192407 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192407 prefixEnd_4192407 := by exact prefixLift 4192407
  have htrace : WordTrace (prefixWord ++ tailWord_4192407) baseStart_4192407 baseEnd_4192407 := by
    simpa [prefixWord, tailWord_4192407, baseEnd_4192407] using wordTrace_append hprefix tailTrace_4192407
  have hstable : (prefixWord ++ tailWord_4192407).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192407).length < 2 ^ (prefixWord ++ tailWord_4192407).sum := by decide
  have hdescent : baseEnd_4192407 < baseStart_4192407 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192407) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192427 : List Nat := [1, 1, 1, 1, 2, 1, 1, 1, 3, 9, 2]
def baseStart_4192427 : Nat := 118140960795 + 4192427 * 2 ^ 59
def prefixEnd_4192427 : Nat := 4983230072969 + 3 ^ 40 * 4192427 * 2
def baseEnd_4192427 : Nat := 2152730159887173843781885

theorem tailTrace_4192427 : CollatzResearch.WordTrace tailWord_4192427 prefixEnd_4192427 2152730159887173843781885 := by
  unfold tailWord_4192427
  simp only [CollatzResearch.WordTrace]
  refine ⟨152910374782560463372279535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101940249855040308914853023 152910374782560463372279535)
  ·
    refine ⟨229365562173840695058419303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152910374782560463372279535 229365562173840695058419303)
    ·
      refine ⟨344048343260761042587628955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229365562173840695058419303 344048343260761042587628955)
      ·
        refine ⟨516072514891141563881443433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344048343260761042587628955 516072514891141563881443433)
        ·
          refine ⟨387054386168356172911082575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 516072514891141563881443433 387054386168356172911082575)
          ·
            refine ⟨580581579252534259366623863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387054386168356172911082575 580581579252534259366623863)
            ·
              refine ⟨870872368878801389049935795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 580581579252534259366623863 870872368878801389049935795)
              ·
                refine ⟨1306308553318202083574903693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 870872368878801389049935795 1306308553318202083574903693)
                ·
                  refine ⟨489865707494325781340588885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1306308553318202083574903693 489865707494325781340588885)
                  ·
                    refine ⟨2870306879849565125042513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 489865707494325781340588885 2870306879849565125042513)
                    ·
                      refine ⟨2152730159887173843781885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2870306879849565125042513 2152730159887173843781885)
                      ·
                        rfl

theorem cell23_4192427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 3, 9, 2].length) (baseStart_4192427 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192427 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192427 prefixEnd_4192427 := by exact prefixLift 4192427
  have htrace : WordTrace (prefixWord ++ tailWord_4192427) baseStart_4192427 baseEnd_4192427 := by
    simpa [prefixWord, tailWord_4192427, baseEnd_4192427] using wordTrace_append hprefix tailTrace_4192427
  have hstable : (prefixWord ++ tailWord_4192427).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192427).length < 2 ^ (prefixWord ++ tailWord_4192427).sum := by decide
  have hdescent : baseEnd_4192427 < baseStart_4192427 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192434 : List Nat := [3, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3]
def baseStart_4192434 : Nat := 118140960795 + 4192434 * 2 ^ 59
def prefixEnd_4192434 : Nat := 4983230072969 + 3 ^ 40 * 4192434 * 2
def baseEnd_4192434 : Nat := 2152733754251755316394353

theorem tailTrace_4192434 : CollatzResearch.WordTrace tailWord_4192434 prefixEnd_4192434 2152733754251755316394353 := by
  unfold tailWord_4192434
  simp only [CollatzResearch.WordTrace]
  refine ⟨38227657523383775891946089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101940420062356735711856237 38227657523383775891946089)
  ·
    refine ⟨28670743142537831918959567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38227657523383775891946089 28670743142537831918959567)
    ·
      refine ⟨43006114713806747878439351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28670743142537831918959567 43006114713806747878439351)
      ·
        refine ⟨64509172070710121817659027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43006114713806747878439351 64509172070710121817659027)
        ·
          refine ⟨96763758106065182726488541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64509172070710121817659027 96763758106065182726488541)
          ·
            refine ⟨36286409289774443522433203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96763758106065182726488541 36286409289774443522433203)
            ·
              refine ⟨54429613934661665283649805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36286409289774443522433203 54429613934661665283649805)
              ·
                refine ⟨20411105225498124481368677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54429613934661665283649805 20411105225498124481368677)
                ·
                  refine ⟨3827082229780898340256627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20411105225498124481368677 3827082229780898340256627)
                  ·
                    refine ⟨5740623344671347510384941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3827082229780898340256627 5740623344671347510384941)
                    ·
                      refine ⟨2152733754251755316394353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5740623344671347510384941 2152733754251755316394353)
                      ·
                        rfl

theorem cell23_4192434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 4, 1, 3].length) (baseStart_4192434 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192434 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192434 prefixEnd_4192434 := by exact prefixLift 4192434
  have htrace : WordTrace (prefixWord ++ tailWord_4192434) baseStart_4192434 baseEnd_4192434 := by
    simpa [prefixWord, tailWord_4192434, baseEnd_4192434] using wordTrace_append hprefix tailTrace_4192434
  have hstable : (prefixWord ++ tailWord_4192434).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192434).length < 2 ^ (prefixWord ++ tailWord_4192434).sum := by decide
  have hdescent : baseEnd_4192434 < baseStart_4192434 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192474 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2]
def baseStart_4192474 : Nat := 118140960795 + 4192474 * 2 ^ 59
def prefixEnd_4192474 : Nat := 4983230072969 + 3 ^ 40 * 4192474 * 2
def baseEnd_4192474 : Nat := 2152754293477935159894169

theorem tailTrace_4192474 : CollatzResearch.WordTrace tailWord_4192474 prefixEnd_4192474 2152754293477935159894169 := by
  unfold tailWord_4192474
  simp only [CollatzResearch.WordTrace]
  refine ⟨38228022253347547599810119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101941392675593460266160317 38228022253347547599810119)
  ·
    refine ⟨57342033380021321399715179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38228022253347547599810119 57342033380021321399715179)
    ·
      refine ⟨86013050070031982099572769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57342033380021321399715179 86013050070031982099572769)
      ·
        refine ⟨64509787552523986574679577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86013050070031982099572769 64509787552523986574679577)
        ·
          refine ⟨48382340664392989931009683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64509787552523986574679577 48382340664392989931009683)
          ·
            refine ⟨72573510996589484896514525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48382340664392989931009683 72573510996589484896514525)
            ·
              refine ⟨27215066623721056836192947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72573510996589484896514525 27215066623721056836192947)
              ·
                refine ⟨40822599935581585254289421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27215066623721056836192947 40822599935581585254289421)
                ·
                  refine ⟨15308474975843094470358533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40822599935581585254289421 15308474975843094470358533)
                  ·
                    refine ⟨2870339057970580213192225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15308474975843094470358533 2870339057970580213192225)
                    ·
                      refine ⟨2152754293477935159894169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2870339057970580213192225 2152754293477935159894169)
                      ·
                        rfl

theorem cell23_4192474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 3, 4, 2].length) (baseStart_4192474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192474 prefixEnd_4192474 := by exact prefixLift 4192474
  have htrace : WordTrace (prefixWord ++ tailWord_4192474) baseStart_4192474 baseEnd_4192474 := by
    simpa [prefixWord, tailWord_4192474, baseEnd_4192474] using wordTrace_append hprefix tailTrace_4192474
  have hstable : (prefixWord ++ tailWord_4192474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192474).length < 2 ^ (prefixWord ++ tailWord_4192474).sum := by decide
  have hdescent : baseEnd_4192474 < baseStart_4192474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192508 : List Nat := [2, 2, 2, 1, 4, 1, 2, 3, 2, 2, 2]
def baseStart_4192508 : Nat := 118140960795 + 4192508 * 2 ^ 59
def prefixEnd_4192508 : Nat := 4983230072969 + 3 ^ 40 * 4192508 * 2
def baseEnd_4192508 : Nat := 2152771751820188026869013

theorem tailTrace_4192508 : CollatzResearch.WordTrace tailWord_4192508 prefixEnd_4192508 2152771751820188026869013 := by
  unfold tailWord_4192508
  simp only [CollatzResearch.WordTrace]
  refine ⟨76456664547633507102989089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101942219396844676137318785 76456664547633507102989089)
  ·
    refine ⟨57342498410725130327241817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76456664547633507102989089 57342498410725130327241817)
    ·
      refine ⟨43006873808043847745431363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57342498410725130327241817 43006873808043847745431363)
      ·
        refine ⟨64510310712065771618147045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43006873808043847745431363 64510310712065771618147045)
        ·
          refine ⟨12095683258512332178402571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64510310712065771618147045 12095683258512332178402571)
          ·
            refine ⟨18143524887768498267603857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12095683258512332178402571 18143524887768498267603857)
            ·
              refine ⟨13607643665826373700702893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18143524887768498267603857 13607643665826373700702893)
              ·
                refine ⟨5102866374684890137763585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13607643665826373700702893 5102866374684890137763585)
                ·
                  refine ⟨3827149781013667603322689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5102866374684890137763585 3827149781013667603322689)
                  ·
                    refine ⟨2870362335760250702492017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3827149781013667603322689 2870362335760250702492017)
                    ·
                      refine ⟨2152771751820188026869013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2870362335760250702492017 2152771751820188026869013)
                      ·
                        rfl

theorem cell23_4192508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 3, 2, 2, 2].length) (baseStart_4192508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192508 prefixEnd_4192508 := by exact prefixLift 4192508
  have htrace : WordTrace (prefixWord ++ tailWord_4192508) baseStart_4192508 baseEnd_4192508 := by
    simpa [prefixWord, tailWord_4192508, baseEnd_4192508] using wordTrace_append hprefix tailTrace_4192508
  have hstable : (prefixWord ++ tailWord_4192508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192508).length < 2 ^ (prefixWord ++ tailWord_4192508).sum := by decide
  have hdescent : baseEnd_4192508 < baseStart_4192508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192514 : List Nat := [3, 4, 1, 1, 2, 1, 1, 1, 9]
def baseStart_4192514 : Nat := 118140960795 + 4192514 * 2 ^ 59
def prefixEnd_4192514 : Nat := 4983230072969 + 3 ^ 40 * 4192514 * 2
def baseEnd_4192514 : Nat := 239197203633790555932665

theorem tailTrace_4192514 : CollatzResearch.WordTrace tailWord_4192514 prefixEnd_4192514 239197203633790555932665 := by
  unfold tailWord_4192514
  simp only [CollatzResearch.WordTrace]
  refine ⟨38228386983311319307674149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101942365288830184820464397 38228386983311319307674149)
  ·
    refine ⟨7167822559370872370188903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38228386983311319307674149 7167822559370872370188903)
    ·
      refine ⟨10751733839056308555283355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7167822559370872370188903 10751733839056308555283355)
      ·
        refine ⟨16127600758584462832925033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10751733839056308555283355 16127600758584462832925033)
        ·
          refine ⟨12095700568938347124693775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16127600758584462832925033 12095700568938347124693775)
          ·
            refine ⟨18143550853407520687040663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12095700568938347124693775 18143550853407520687040663)
            ·
              refine ⟨27215326280111281030560995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18143550853407520687040663 27215326280111281030560995)
              ·
                refine ⟨40822989420166921545841493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27215326280111281030560995 40822989420166921545841493)
                ·
                  refine ⟨239197203633790555932665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 40822989420166921545841493 239197203633790555932665)
                  ·
                    rfl

theorem cell23_4192514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_4192514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192514 prefixEnd_4192514 := by exact prefixLift 4192514
  have htrace : WordTrace (prefixWord ++ tailWord_4192514) baseStart_4192514 baseEnd_4192514 := by
    simpa [prefixWord, tailWord_4192514, baseEnd_4192514] using wordTrace_append hprefix tailTrace_4192514
  have hstable : (prefixWord ++ tailWord_4192514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192514).length < 2 ^ (prefixWord ++ tailWord_4192514).sum := by decide
  have hdescent : baseEnd_4192514 < baseStart_4192514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192542 : List Nat := [4, 3, 2, 1, 1, 1, 3, 2, 2, 2, 2]
def baseStart_4192542 : Nat := 118140960795 + 4192542 * 2 ^ 59
def prefixEnd_4192542 : Nat := 4983230072969 + 3 ^ 40 * 4192542 * 2
def baseEnd_4192542 : Nat := 2152789210162440893843857

theorem tailTrace_4192542 : CollatzResearch.WordTrace tailWord_4192542 prefixEnd_4192542 2152789210162440893843857 := by
  unfold tailWord_4192542
  simp only [CollatzResearch.WordTrace]
  refine ⟨19114321147142979751589485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101943046118095892008477253 19114321147142979751589485)
  ·
    refine ⟨7167870430178617406846057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19114321147142979751589485 7167870430178617406846057)
    ·
      refine ⟨5375902822633963055134543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7167870430178617406846057 5375902822633963055134543)
      ·
        refine ⟨8063854233950944582701815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5375902822633963055134543 8063854233950944582701815)
        ·
          refine ⟨12095781350926416874052723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8063854233950944582701815 12095781350926416874052723)
          ·
            refine ⟨18143672026389625311079085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12095781350926416874052723 18143672026389625311079085)
            ·
              refine ⟨6803877009896109491654657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18143672026389625311079085 6803877009896109491654657)
              ·
                refine ⟨5102907757422082118740993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6803877009896109491654657 5102907757422082118740993)
                ·
                  refine ⟨3827180818066561589055745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5102907757422082118740993 3827180818066561589055745)
                  ·
                    refine ⟨2870385613549921191791809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3827180818066561589055745 2870385613549921191791809)
                    ·
                      refine ⟨2152789210162440893843857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2870385613549921191791809 2152789210162440893843857)
                      ·
                        rfl

theorem cell23_4192542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 2, 2, 2, 2].length) (baseStart_4192542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192542 prefixEnd_4192542 := by exact prefixLift 4192542
  have htrace : WordTrace (prefixWord ++ tailWord_4192542) baseStart_4192542 baseEnd_4192542 := by
    simpa [prefixWord, tailWord_4192542, baseEnd_4192542] using wordTrace_append hprefix tailTrace_4192542
  have hstable : (prefixWord ++ tailWord_4192542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192542).length < 2 ^ (prefixWord ++ tailWord_4192542).sum := by decide
  have hdescent : baseEnd_4192542 < baseStart_4192542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192584 : List Nat := [2, 1, 3, 1, 1, 2, 4, 1, 1, 4, 3]
def baseStart_4192584 : Nat := 118140960795 + 4192584 * 2 ^ 59
def prefixEnd_4192584 : Nat := 4983230072969 + 3 ^ 40 * 4192584 * 2
def baseEnd_4192584 : Nat := 2152810776349929729518663

theorem tailTrace_4192584 : CollatzResearch.WordTrace tailWord_4192584 prefixEnd_4192584 2152810776349929729518663 := by
  unfold tailWord_4192584
  simp only [CollatzResearch.WordTrace]
  refine ⟨76458050521495839592872403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101944067361994452790496537 76458050521495839592872403)
  ·
    refine ⟨114687075782243759389308605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76458050521495839592872403 114687075782243759389308605)
    ·
      refine ⟨43007653418341409770990727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114687075782243759389308605 43007653418341409770990727)
      ·
        refine ⟨64511480127512114656486091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43007653418341409770990727 64511480127512114656486091)
        ·
          refine ⟨96767220191268171984729137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64511480127512114656486091 96767220191268171984729137)
          ·
            refine ⟨72575415143451128988546853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96767220191268171984729137 72575415143451128988546853)
            ·
              refine ⟨13607890339397086685352535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72575415143451128988546853 13607890339397086685352535)
              ·
                refine ⟨20411835509095630028028803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13607890339397086685352535 20411835509095630028028803)
                ·
                  refine ⟨30617753263643445042043205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20411835509095630028028803 30617753263643445042043205)
                  ·
                    refine ⟨5740828736933145945383101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30617753263643445042043205 5740828736933145945383101)
                    ·
                      refine ⟨2152810776349929729518663, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5740828736933145945383101 2152810776349929729518663)
                      ·
                        rfl

theorem cell23_4192584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 2, 4, 1, 1, 4, 3].length) (baseStart_4192584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192584 prefixEnd_4192584 := by exact prefixLift 4192584
  have htrace : WordTrace (prefixWord ++ tailWord_4192584) baseStart_4192584 baseEnd_4192584 := by
    simpa [prefixWord, tailWord_4192584, baseEnd_4192584] using wordTrace_append hprefix tailTrace_4192584
  have hstable : (prefixWord ++ tailWord_4192584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192584).length < 2 ^ (prefixWord ++ tailWord_4192584).sum := by decide
  have hdescent : baseEnd_4192584 < baseStart_4192584 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192591 : List Nat := [1, 1, 2, 1, 1, 2, 1, 9, 1, 4]
def baseStart_4192591 : Nat := 118140960795 + 4192591 * 2 ^ 59
def prefixEnd_4192591 : Nat := 4983230072969 + 3 ^ 40 * 4192591 * 2
def baseEnd_4192591 : Nat := 717604790238170400710377

theorem tailTrace_4192591 : CollatzResearch.WordTrace tailWord_4192591 prefixEnd_4192591 717604790238170400710377 := by
  unfold tailWord_4192591
  simp only [CollatzResearch.WordTrace]
  refine ⟨152916356353966319381249627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101944237569310879587499751 152916356353966319381249627)
  ·
    refine ⟨229374534530949479071874441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152916356353966319381249627 229374534530949479071874441)
    ·
      refine ⟨172030900898212109303905831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229374534530949479071874441 172030900898212109303905831)
      ·
        refine ⟨258046351347318163955858747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172030900898212109303905831 258046351347318163955858747)
        ·
          refine ⟨387069527020977245933788121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258046351347318163955858747 387069527020977245933788121)
          ·
            refine ⟨290302145265732934450341091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387069527020977245933788121 290302145265732934450341091)
            ·
              refine ⟨435453217898599401675511637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290302145265732934450341091 435453217898599401675511637)
              ·
                refine ⟨2551483698624605869192451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 435453217898599401675511637 2551483698624605869192451)
                ·
                  refine ⟨3827225547936908803788677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2551483698624605869192451 3827225547936908803788677)
                  ·
                    refine ⟨717604790238170400710377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3827225547936908803788677 717604790238170400710377)
                    ·
                      rfl

theorem cell23_4192591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 9, 1, 4].length) (baseStart_4192591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192591 prefixEnd_4192591 := by exact prefixLift 4192591
  have htrace : WordTrace (prefixWord ++ tailWord_4192591) baseStart_4192591 baseEnd_4192591 := by
    simpa [prefixWord, tailWord_4192591, baseEnd_4192591] using wordTrace_append hprefix tailTrace_4192591
  have hstable : (prefixWord ++ tailWord_4192591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192591).length < 2 ^ (prefixWord ++ tailWord_4192591).sum := by decide
  have hdescent : baseEnd_4192591 < baseStart_4192591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192607 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 8]
def baseStart_4192607 : Nat := 118140960795 + 4192607 * 2 ^ 59
def prefixEnd_4192607 : Nat := 4983230072969 + 3 ^ 40 * 4192607 * 2
def baseEnd_4192607 : Nat := 2152822586404983139531057

theorem tailTrace_4192607 : CollatzResearch.WordTrace tailWord_4192607 prefixEnd_4192607 2152822586404983139531057 := by
  unfold tailWord_4192607
  simp only [CollatzResearch.WordTrace]
  refine ⟨152916939921908354113832075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101944626614605569409221383 152916939921908354113832075)
  ·
    refine ⟨229375409882862531170748113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152916939921908354113832075 229375409882862531170748113)
    ·
      refine ⟨172031557412146898378061085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229375409882862531170748113 172031557412146898378061085)
      ·
        refine ⟨64511834029555086891772907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172031557412146898378061085 64511834029555086891772907)
        ·
          refine ⟨96767751044332630337659361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64511834029555086891772907 96767751044332630337659361)
          ·
            refine ⟨72575813283249472753244521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96767751044332630337659361 72575813283249472753244521)
            ·
              refine ⟨54431859962437104564933391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72575813283249472753244521 54431859962437104564933391)
              ·
                refine ⟨81647789943655656847400087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54431859962437104564933391 81647789943655656847400087)
                ·
                  refine ⟨122471684915483485271100131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81647789943655656847400087 122471684915483485271100131)
                  ·
                    refine ⟨183707527373225227906650197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 122471684915483485271100131 183707527373225227906650197)
                    ·
                      refine ⟨2152822586404983139531057, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 183707527373225227906650197 2152822586404983139531057)
                      ·
                        rfl

theorem cell23_4192607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 1, 1, 8].length) (baseStart_4192607 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192607 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192607 prefixEnd_4192607 := by exact prefixLift 4192607
  have htrace : WordTrace (prefixWord ++ tailWord_4192607) baseStart_4192607 baseEnd_4192607 := by
    simpa [prefixWord, tailWord_4192607, baseEnd_4192607] using wordTrace_append hprefix tailTrace_4192607
  have hstable : (prefixWord ++ tailWord_4192607).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192607).length < 2 ^ (prefixWord ++ tailWord_4192607).sum := by decide
  have hdescent : baseEnd_4192607 < baseStart_4192607 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192608 : List Nat := [2, 1, 1, 3, 5, 2, 1, 1, 3, 4]
def baseStart_4192608 : Nat := 118140960795 + 4192608 * 2 ^ 59
def prefixEnd_4192608 : Nat := 4983230072969 + 3 ^ 40 * 4192608 * 2
def baseEnd_4192608 : Nat := 717607699961879211872851

theorem tailTrace_4192608 : CollatzResearch.WordTrace tailWord_4192608 prefixEnd_4192608 717607699961879211872851 := by
  unfold tailWord_4192608
  simp only [CollatzResearch.WordTrace]
  refine ⟨76458488197452365642309239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101944650929936487523078985 76458488197452365642309239)
  ·
    refine ⟨114687732296178548463463859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76458488197452365642309239 114687732296178548463463859)
    ·
      refine ⟨172031598444267822695195789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114687732296178548463463859 172031598444267822695195789)
      ·
        refine ⟨64511849416600433510698421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172031598444267822695195789 64511849416600433510698421)
        ·
          refine ⟨6047985882806290641627977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 64511849416600433510698421 6047985882806290641627977)
          ·
            refine ⟨4535989412104717981220983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6047985882806290641627977 4535989412104717981220983)
            ·
              refine ⟨6803984118157076971831475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4535989412104717981220983 6803984118157076971831475)
              ·
                refine ⟨10205976177235615457747213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6803984118157076971831475 10205976177235615457747213)
                ·
                  refine ⟨3827241066463355796655205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10205976177235615457747213 3827241066463355796655205)
                  ·
                    refine ⟨717607699961879211872851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3827241066463355796655205 717607699961879211872851)
                    ·
                      rfl

theorem cell23_4192608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 1, 3, 4].length) (baseStart_4192608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192608 prefixEnd_4192608 := by exact prefixLift 4192608
  have htrace : WordTrace (prefixWord ++ tailWord_4192608) baseStart_4192608 baseEnd_4192608 := by
    simpa [prefixWord, tailWord_4192608, baseEnd_4192608] using wordTrace_append hprefix tailTrace_4192608
  have hstable : (prefixWord ++ tailWord_4192608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192608).length < 2 ^ (prefixWord ++ tailWord_4192608).sum := by decide
  have hdescent : baseEnd_4192608 < baseStart_4192608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192627 : List Nat := [1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 7]
def baseStart_4192627 : Nat := 118140960795 + 4192627 * 2 ^ 59
def prefixEnd_4192627 : Nat := 4983230072969 + 3 ^ 40 * 4192627 * 2
def baseEnd_4192627 : Nat := 2152832856018073061280965

theorem tailTrace_4192627 : CollatzResearch.WordTrace tailWord_4192627 prefixEnd_4192627 2152832856018073061280965 := by
  unfold tailWord_4192627
  simp only [CollatzResearch.WordTrace]
  refine ⟨152917669381835897529560135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101945112921223931686373423 152917669381835897529560135)
  ·
    refine ⟨229376504072753846294340203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152917669381835897529560135 229376504072753846294340203)
    ·
      refine ⟨344064756109130769441510305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229376504072753846294340203 344064756109130769441510305)
      ·
        refine ⟨258048567081848077081132729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344064756109130769441510305 258048567081848077081132729)
        ·
          refine ⟨193536425311386057810849547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258048567081848077081132729 193536425311386057810849547)
          ·
            refine ⟨290304637967079086716274321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193536425311386057810849547 290304637967079086716274321)
            ·
              refine ⟨217728478475309315037205741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290304637967079086716274321 217728478475309315037205741)
              ·
                refine ⟨81648179428240993138952153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217728478475309315037205741 81648179428240993138952153)
                ·
                  refine ⟨61236134571180744854214115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81648179428240993138952153 61236134571180744854214115)
                  ·
                    refine ⟨91854201856771117281321173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61236134571180744854214115 91854201856771117281321173)
                    ·
                      refine ⟨2152832856018073061280965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91854201856771117281321173 2152832856018073061280965)
                      ·
                        rfl

theorem cell23_4192627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 1, 7].length) (baseStart_4192627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192627 prefixEnd_4192627 := by exact prefixLift 4192627
  have htrace : WordTrace (prefixWord ++ tailWord_4192627) baseStart_4192627 baseEnd_4192627 := by
    simpa [prefixWord, tailWord_4192627, baseEnd_4192627] using wordTrace_append hprefix tailTrace_4192627
  have hstable : (prefixWord ++ tailWord_4192627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192627).length < 2 ^ (prefixWord ++ tailWord_4192627).sum := by decide
  have hdescent : baseEnd_4192627 < baseStart_4192627 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192692 : List Nat := [2, 5, 2, 2, 1, 1, 1, 1, 1, 5, 2]
def baseStart_4192692 : Nat := 118140960795 + 4192692 * 2 ^ 59
def prefixEnd_4192692 : Nat := 4983230072969 + 3 ^ 40 * 4192692 * 2
def baseEnd_4192692 : Nat := 2152866232260615306968167

theorem tailTrace_4192692 : CollatzResearch.WordTrace tailWord_4192692 prefixEnd_4192692 2152866232260615306968167 := by
  unfold tailWord_4192692
  simp only [CollatzResearch.WordTrace]
  refine ⟨76460020063300206815338165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101946693417733609087117553 76460020063300206815338165)
  ·
    refine ⟨7168126880934394388937953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76460020063300206815338165 7168126880934394388937953)
    ·
      refine ⟨5376095160700795791703465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7168126880934394388937953 5376095160700795791703465)
      ·
        refine ⟨4032071370525596843777599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5376095160700795791703465 4032071370525596843777599)
        ·
          refine ⟨6048107055788395265666399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4032071370525596843777599 6048107055788395265666399)
          ·
            refine ⟨9072160583682592898499599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6048107055788395265666399 9072160583682592898499599)
            ·
              refine ⟨13608240875523889347749399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9072160583682592898499599 13608240875523889347749399)
              ·
                refine ⟨20412361313285834021624099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13608240875523889347749399 20412361313285834021624099)
                ·
                  refine ⟨30618541969928751032436149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20412361313285834021624099 30618541969928751032436149)
                  ·
                    refine ⟨2870488309680820409290889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30618541969928751032436149 2870488309680820409290889)
                    ·
                      refine ⟨2152866232260615306968167, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2870488309680820409290889 2152866232260615306968167)
                      ·
                        rfl

theorem cell23_4192692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 1, 5, 2].length) (baseStart_4192692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192692 prefixEnd_4192692 := by exact prefixLift 4192692
  have htrace : WordTrace (prefixWord ++ tailWord_4192692) baseStart_4192692 baseEnd_4192692 := by
    simpa [prefixWord, tailWord_4192692, baseEnd_4192692] using wordTrace_append hprefix tailTrace_4192692
  have hstable : (prefixWord ++ tailWord_4192692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192692).length < 2 ^ (prefixWord ++ tailWord_4192692).sum := by decide
  have hdescent : baseEnd_4192692 < baseStart_4192692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192701 : List Nat := [1, 4, 1, 2, 2, 2, 2, 2, 1, 2, 4]
def baseStart_4192701 : Nat := 118140960795 + 4192701 * 2 ^ 59
def prefixEnd_4192701 : Nat := 4983230072969 + 3 ^ 40 * 4192701 * 2
def baseEnd_4192701 : Nat := 2152870853586505771755625

theorem tailTrace_4192701 : CollatzResearch.WordTrace tailWord_4192701 prefixEnd_4192701 2152870853586505771755625 := by
  unfold tailWord_4192701
  simp only [CollatzResearch.WordTrace]
  refine ⟨152920368383567808167753957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101946912255711872111835971 152920368383567808167753957)
  ·
    refine ⟨28672569071918964031453867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152920368383567808167753957 28672569071918964031453867)
    ·
      refine ⟨43008853607878446047180801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28672569071918964031453867 43008853607878446047180801)
      ·
        refine ⟨32256640205908834535385601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43008853607878446047180801 32256640205908834535385601)
        ·
          refine ⟨24192480154431625901539201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32256640205908834535385601 24192480154431625901539201)
          ·
            refine ⟨18144360115823719426154401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24192480154431625901539201 18144360115823719426154401)
            ·
              refine ⟨13608270086867789569615801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18144360115823719426154401 13608270086867789569615801)
              ·
                refine ⟨10206202565150842177211851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13608270086867789569615801 10206202565150842177211851)
                ·
                  refine ⟨15309303847726263265817777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10206202565150842177211851 15309303847726263265817777)
                  ·
                    refine ⟨11481977885794697449363333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15309303847726263265817777 11481977885794697449363333)
                    ·
                      refine ⟨2152870853586505771755625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11481977885794697449363333 2152870853586505771755625)
                      ·
                        rfl

theorem cell23_4192701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 2, 2, 1, 2, 4].length) (baseStart_4192701 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192701 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192701 prefixEnd_4192701 := by exact prefixLift 4192701
  have htrace : WordTrace (prefixWord ++ tailWord_4192701) baseStart_4192701 baseEnd_4192701 := by
    simpa [prefixWord, tailWord_4192701, baseEnd_4192701] using wordTrace_append hprefix tailTrace_4192701
  have hstable : (prefixWord ++ tailWord_4192701).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192701).length < 2 ^ (prefixWord ++ tailWord_4192701).sum := by decide
  have hdescent : baseEnd_4192701 < baseStart_4192701 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192831 : List Nat := [1, 1, 2, 2, 3, 2, 1, 4, 2, 5]
def baseStart_4192831 : Nat := 118140960795 + 4192831 * 2 ^ 59
def prefixEnd_4192831 : Nat := 4983230072969 + 3 ^ 40 * 4192831 * 2
def baseEnd_4192831 : Nat := 717645868690530087710009

theorem tailTrace_4192831 : CollatzResearch.WordTrace tailWord_4192831 prefixEnd_4192831 717645868690530087710009 := by
  unfold tailWord_4192831
  simp only [CollatzResearch.WordTrace]
  refine ⟨152925109873096840369986347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101950073248731226913324231 152925109873096840369986347)
  ·
    refine ⟨229387664809645260554979521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152925109873096840369986347 229387664809645260554979521)
    ·
      refine ⟨172040748607233945416234641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229387664809645260554979521 172040748607233945416234641)
      ·
        refine ⟨129030561455425459062175981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172040748607233945416234641 129030561455425459062175981)
        ·
          refine ⟨48386460545784547148315993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129030561455425459062175981 48386460545784547148315993)
          ·
            refine ⟨36289845409338410361236995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48386460545784547148315993 36289845409338410361236995)
            ·
              refine ⟨54434768114007615541855493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36289845409338410361236995 54434768114007615541855493)
              ·
                refine ⟨10206519021376427914097905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54434768114007615541855493 10206519021376427914097905)
                ·
                  refine ⟨7654889266032320935573429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10206519021376427914097905 7654889266032320935573429)
                  ·
                    refine ⟨717645868690530087710009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7654889266032320935573429 717645868690530087710009)
                    ·
                      rfl

theorem cell23_4192831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 1, 4, 2, 5].length) (baseStart_4192831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192831 prefixEnd_4192831 := by exact prefixLift 4192831
  have htrace : WordTrace (prefixWord ++ tailWord_4192831) baseStart_4192831 baseEnd_4192831 := by
    simpa [prefixWord, tailWord_4192831, baseEnd_4192831] using wordTrace_append hprefix tailTrace_4192831
  have hstable : (prefixWord ++ tailWord_4192831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192831).length < 2 ^ (prefixWord ++ tailWord_4192831).sum := by decide
  have hdescent : baseEnd_4192831 < baseStart_4192831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192845 : List Nat := [1, 6, 1, 1, 2, 2, 1, 1, 2, 3, 3]
def baseStart_4192845 : Nat := 118140960795 + 4192845 * 2 ^ 59
def prefixEnd_4192845 : Nat := 4983230072969 + 3 ^ 40 * 4192845 * 2
def baseEnd_4192845 : Nat := 2152944794800753208354963

theorem tailTrace_4192845 : CollatzResearch.WordTrace tailWord_4192845 prefixEnd_4192845 2152944794800753208354963 := by
  unfold tailWord_4192845
  simp only [CollatzResearch.WordTrace]
  refine ⟨152925620495046120760995989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101950413663364080507330659 152925620495046120760995989)
  ·
    refine ⟨7168388460705286910671687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152925620495046120760995989 7168388460705286910671687)
    ·
      refine ⟨10752582691057930366007531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7168388460705286910671687 10752582691057930366007531)
      ·
        refine ⟨16128874036586895549011297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10752582691057930366007531 16128874036586895549011297)
        ·
          refine ⟨12096655527440171661758473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16128874036586895549011297 12096655527440171661758473)
          ·
            refine ⟨9072491645580128746318855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12096655527440171661758473 9072491645580128746318855)
            ·
              refine ⟨13608737468370193119478283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9072491645580128746318855 13608737468370193119478283)
              ·
                refine ⟨20413106202555289679217425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13608737468370193119478283 20413106202555289679217425)
                ·
                  refine ⟨15309829651916467259413069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20413106202555289679217425 15309829651916467259413069)
                  ·
                    refine ⟨5741186119468675222279901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15309829651916467259413069 5741186119468675222279901)
                    ·
                      refine ⟨2152944794800753208354963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5741186119468675222279901 2152944794800753208354963)
                      ·
                        rfl

theorem cell23_4192845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 2, 1, 1, 2, 3, 3].length) (baseStart_4192845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192845 prefixEnd_4192845 := by exact prefixLift 4192845
  have htrace : WordTrace (prefixWord ++ tailWord_4192845) baseStart_4192845 baseEnd_4192845 := by
    simpa [prefixWord, tailWord_4192845, baseEnd_4192845] using wordTrace_append hprefix tailTrace_4192845
  have hstable : (prefixWord ++ tailWord_4192845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192845).length < 2 ^ (prefixWord ++ tailWord_4192845).sum := by decide
  have hdescent : baseEnd_4192845 < baseStart_4192845 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192868 : List Nat := [2, 3, 1, 1, 2, 2, 1, 2, 1, 6, 2]
def baseStart_4192868 : Nat := 118140960795 + 4192868 * 2 ^ 59
def prefixEnd_4192868 : Nat := 4983230072969 + 3 ^ 40 * 4192868 * 2
def baseEnd_4192868 : Nat := 2152956604855806618367357

theorem tailTrace_4192868 : CollatzResearch.WordTrace tailWord_4192868 prefixEnd_4192868 2152956604855806618367357 := by
  unfold tailWord_4192868
  simp only [CollatzResearch.WordTrace]
  refine ⟨76463229686981397844541629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101950972915975197126055505 76463229686981397844541629)
  ·
    refine ⟨28673711132618024191703111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76463229686981397844541629 28673711132618024191703111)
    ·
      refine ⟨43010566698927036287554667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28673711132618024191703111 43010566698927036287554667)
      ·
        refine ⟨64515850048390554431332001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43010566698927036287554667 64515850048390554431332001)
        ·
          refine ⟨48386887536292915823499001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64515850048390554431332001 48386887536292915823499001)
          ·
            refine ⟨36290165652219686867624251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48386887536292915823499001 36290165652219686867624251)
            ·
              refine ⟨54435248478329530301436377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36290165652219686867624251 54435248478329530301436377)
              ·
                refine ⟨40826436358747147726077283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54435248478329530301436377 40826436358747147726077283)
                ·
                  refine ⟨61239654538120721589115925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40826436358747147726077283 61239654538120721589115925)
                  ·
                    refine ⟨2870608806474408824489809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 61239654538120721589115925 2870608806474408824489809)
                    ·
                      refine ⟨2152956604855806618367357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2870608806474408824489809 2152956604855806618367357)
                      ·
                        rfl

theorem cell23_4192868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 2, 1, 6, 2].length) (baseStart_4192868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192868 prefixEnd_4192868 := by exact prefixLift 4192868
  have htrace : WordTrace (prefixWord ++ tailWord_4192868) baseStart_4192868 baseEnd_4192868 := by
    simpa [prefixWord, tailWord_4192868, baseEnd_4192868] using wordTrace_append hprefix tailTrace_4192868
  have hstable : (prefixWord ++ tailWord_4192868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192868).length < 2 ^ (prefixWord ++ tailWord_4192868).sum := by decide
  have hdescent : baseEnd_4192868 < baseStart_4192868 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192891 : List Nat := [1, 1, 1, 1, 1, 4, 2, 6, 6]
def baseStart_4192891 : Nat := 118140960795 + 4192891 * 2 ^ 59
def prefixEnd_4192891 : Nat := 4983230072969 + 3 ^ 40 * 4192891 * 2
def baseEnd_4192891 : Nat := 239218712767873336486639

theorem tailTrace_4192891 : CollatzResearch.WordTrace tailWord_4192891 prefixEnd_4192891 239218712767873336486639 := by
  unfold tailWord_4192891
  simp only [CollatzResearch.WordTrace]
  refine ⟨152927298252879470617170527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101951532168586313744780351 152927298252879470617170527)
  ·
    refine ⟨229390947379319205925755791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152927298252879470617170527 229390947379319205925755791)
    ·
      refine ⟨344086421068978808888633687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229390947379319205925755791 344086421068978808888633687)
      ·
        refine ⟨516129631603468213332950531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344086421068978808888633687 516129631603468213332950531)
        ·
          refine ⟨774194447405202319999425797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516129631603468213332950531 774194447405202319999425797)
          ·
            refine ⟨145161458888475434999892337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 774194447405202319999425797 145161458888475434999892337)
            ·
              refine ⟨108871094166356576249919253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145161458888475434999892337 108871094166356576249919253)
              ·
                refine ⟨5103332539047964511714965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 108871094166356576249919253 5103332539047964511714965)
                ·
                  refine ⟨239218712767873336486639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5103332539047964511714965 239218712767873336486639)
                  ·
                    rfl

theorem cell23_4192891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 2, 6, 6].length) (baseStart_4192891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192891 prefixEnd_4192891 := by exact prefixLift 4192891
  have htrace : WordTrace (prefixWord ++ tailWord_4192891) baseStart_4192891 baseEnd_4192891 := by
    simpa [prefixWord, tailWord_4192891, baseEnd_4192891] using wordTrace_append hprefix tailTrace_4192891
  have hstable : (prefixWord ++ tailWord_4192891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192891).length < 2 ^ (prefixWord ++ tailWord_4192891).sum := by decide
  have hdescent : baseEnd_4192891 < baseStart_4192891 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192929 : List Nat := [1, 2, 3, 3, 3, 2, 1, 3, 1, 4]
def baseStart_4192929 : Nat := 118140960795 + 4192929 * 2 ^ 59
def prefixEnd_4192929 : Nat := 4983230072969 + 3 ^ 40 * 4192929 * 2
def baseEnd_4192929 : Nat := 717662642391910293234859

theorem tailTrace_4192929 : CollatzResearch.WordTrace tailWord_4192929 prefixEnd_4192929 717662642391910293234859 := by
  unfold tailWord_4192929
  simp only [CollatzResearch.WordTrace]
  refine ⟨152928684226741803107053841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101952456151161202071369227 152928684226741803107053841)
  ·
    refine ⟨114696513170056352330290381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152928684226741803107053841 114696513170056352330290381)
    ·
      refine ⟨43011192438771132123858893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114696513170056352330290381 43011192438771132123858893)
      ·
        refine ⟨16129197164539174546447085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43011192438771132123858893 16129197164539174546447085)
        ·
          refine ⟨6048448936702190454917657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16129197164539174546447085 6048448936702190454917657)
          ·
            refine ⟨4536336702526642841188243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6048448936702190454917657 4536336702526642841188243)
            ·
              refine ⟨6804505053789964261782365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4536336702526642841188243 6804505053789964261782365)
              ·
                refine ⟨2551689395171236598168387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6804505053789964261782365 2551689395171236598168387)
                ·
                  refine ⟨3827534092756854897252581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2551689395171236598168387 3827534092756854897252581)
                  ·
                    refine ⟨717662642391910293234859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3827534092756854897252581 717662642391910293234859)
                    ·
                      rfl

theorem cell23_4192929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 3, 2, 1, 3, 1, 4].length) (baseStart_4192929 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192929 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192929 prefixEnd_4192929 := by exact prefixLift 4192929
  have htrace : WordTrace (prefixWord ++ tailWord_4192929) baseStart_4192929 baseEnd_4192929 := by
    simpa [prefixWord, tailWord_4192929, baseEnd_4192929] using wordTrace_append hprefix tailTrace_4192929
  have hstable : (prefixWord ++ tailWord_4192929).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192929).length < 2 ^ (prefixWord ++ tailWord_4192929).sum := by decide
  have hdescent : baseEnd_4192929 < baseStart_4192929 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192972 : List Nat := [2, 2, 1, 5, 1, 3, 1, 2, 1, 5]
def baseStart_4192972 : Nat := 118140960795 + 4192972 * 2 ^ 59
def prefixEnd_4192972 : Nat := 4983230072969 + 3 ^ 40 * 4192972 * 2
def baseEnd_4192972 : Nat := 717670002281291403822293

theorem tailTrace_4192972 : CollatzResearch.WordTrace tailWord_4192972 prefixEnd_4192972 717670002281291403822293 := by
  unfold tailWord_4192972
  simp only [CollatzResearch.WordTrace]
  refine ⟨76465126282793010725434585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101953501710390680967246113 76465126282793010725434585)
  ·
    refine ⟨57348844712094758044075939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76465126282793010725434585 57348844712094758044075939)
    ·
      refine ⟨86023267068142137066113909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57348844712094758044075939 86023267068142137066113909)
      ·
        refine ⟨8064681287638325349948179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86023267068142137066113909 8064681287638325349948179)
        ·
          refine ⟨12097021931457488024922269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8064681287638325349948179 12097021931457488024922269)
          ·
            refine ⟨4536383224296558009345851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12097021931457488024922269 4536383224296558009345851)
            ·
              refine ⟨6804574836444837014018777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4536383224296558009345851 6804574836444837014018777)
              ·
                refine ⟨5103431127333627760514083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6804574836444837014018777 5103431127333627760514083)
                ·
                  refine ⟨7655146691000441640771125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5103431127333627760514083 7655146691000441640771125)
                  ·
                    refine ⟨717670002281291403822293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7655146691000441640771125 717670002281291403822293)
                    ·
                      rfl

theorem cell23_4192972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 3, 1, 2, 1, 5].length) (baseStart_4192972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192972 prefixEnd_4192972 := by exact prefixLift 4192972
  have htrace : WordTrace (prefixWord ++ tailWord_4192972) baseStart_4192972 baseEnd_4192972 := by
    simpa [prefixWord, tailWord_4192972, baseEnd_4192972] using wordTrace_append hprefix tailTrace_4192972
  have hstable : (prefixWord ++ tailWord_4192972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192972).length < 2 ^ (prefixWord ++ tailWord_4192972).sum := by decide
  have hdescent : baseEnd_4192972 < baseStart_4192972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4192995 : List Nat := [1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 5]
def baseStart_4192995 : Nat := 118140960795 + 4192995 * 2 ^ 59
def prefixEnd_4192995 : Nat := 4983230072969 + 3 ^ 40 * 4192995 * 2
def baseEnd_4192995 : Nat := 2153021816898927621479273

theorem tailTrace_4192995 : CollatzResearch.WordTrace tailWord_4192995 prefixEnd_4192995 2153021816898927621479273 := by
  unfold tailWord_4192995
  simp only [CollatzResearch.WordTrace]
  refine ⟨152931091444502696378956439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101954060963001797585970959 152931091444502696378956439)
  ·
    refine ⟨229396637166754044568434659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152931091444502696378956439 229396637166754044568434659)
    ·
      refine ⟨344094955750131066852651989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229396637166754044568434659 344094955750131066852651989)
      ·
        refine ⟨8064725525393696879359031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 344094955750131066852651989 8064725525393696879359031)
        ·
          refine ⟨12097088288090545319038547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8064725525393696879359031 12097088288090545319038547)
          ·
            refine ⟨18145632432135817978557821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12097088288090545319038547 18145632432135817978557821)
            ·
              refine ⟨6804612162050931741959183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18145632432135817978557821 6804612162050931741959183)
              ·
                refine ⟨10206918243076397612938775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6804612162050931741959183 10206918243076397612938775)
                ·
                  refine ⟨15310377364614596419408163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10206918243076397612938775 15310377364614596419408163)
                  ·
                    refine ⟨22965566046921894629112245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15310377364614596419408163 22965566046921894629112245)
                    ·
                      refine ⟨2153021816898927621479273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22965566046921894629112245 2153021816898927621479273)
                      ·
                        rfl

theorem cell23_4192995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_4192995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4192995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4192995 prefixEnd_4192995 := by exact prefixLift 4192995
  have htrace : WordTrace (prefixWord ++ tailWord_4192995) baseStart_4192995 baseEnd_4192995 := by
    simpa [prefixWord, tailWord_4192995, baseEnd_4192995] using wordTrace_append hprefix tailTrace_4192995
  have hstable : (prefixWord ++ tailWord_4192995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4192995).length < 2 ^ (prefixWord ++ tailWord_4192995).sum := by decide
  have hdescent : baseEnd_4192995 < baseStart_4192995 := by decide
  rcases family_descends (prefixWord ++ tailWord_4192995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193008 : List Nat := [2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 3]
def baseStart_4193008 : Nat := 118140960795 + 4193008 * 2 ^ 59
def prefixEnd_4193008 : Nat := 4983230072969 + 3 ^ 40 * 4193008 * 2
def baseEnd_4193008 : Nat := 2153028492147436070616713

theorem tailTrace_4193008 : CollatzResearch.WordTrace tailWord_4193008 prefixEnd_4193008 2153028492147436070616713 := by
  unfold tailWord_4193008
  simp only [CollatzResearch.WordTrace]
  refine ⟨76465782796727799799589839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101954377062303733066119785 76465782796727799799589839)
  ·
    refine ⟨114698674195091699699384759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76465782796727799799589839 114698674195091699699384759)
    ·
      refine ⟨172048011292637549549077139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114698674195091699699384759 172048011292637549549077139)
      ·
        refine ⟨258072016938956324323615709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172048011292637549549077139 258072016938956324323615709)
        ·
          refine ⟨96777006352108621621355891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 258072016938956324323615709 96777006352108621621355891)
          ·
            refine ⟨145165509528162932432033837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96777006352108621621355891 145165509528162932432033837)
            ·
              refine ⟨54437066073061099662012689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145165509528162932432033837 54437066073061099662012689)
              ·
                refine ⟨40827799554795824746509517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54437066073061099662012689 40827799554795824746509517)
                ·
                  refine ⟨15310424833048434279941069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40827799554795824746509517 15310424833048434279941069)
                  ·
                    refine ⟨5741409312393162854977901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15310424833048434279941069 5741409312393162854977901)
                    ·
                      refine ⟨2153028492147436070616713, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5741409312393162854977901 2153028492147436070616713)
                      ·
                        rfl

theorem cell23_4193008_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 3, 2, 3, 3, 3].length) (baseStart_4193008 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193008 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193008 prefixEnd_4193008 := by exact prefixLift 4193008
  have htrace : WordTrace (prefixWord ++ tailWord_4193008) baseStart_4193008 baseEnd_4193008 := by
    simpa [prefixWord, tailWord_4193008, baseEnd_4193008] using wordTrace_append hprefix tailTrace_4193008
  have hstable : (prefixWord ++ tailWord_4193008).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193008).length < 2 ^ (prefixWord ++ tailWord_4193008).sum := by decide
  have hdescent : baseEnd_4193008 < baseStart_4193008 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193008) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193009 : List Nat := [1, 2, 2, 2, 2, 2, 3, 4, 1, 2, 2]
def baseStart_4193009 : Nat := 118140960795 + 4193009 * 2 ^ 59
def prefixEnd_4193009 : Nat := 4983230072969 + 3 ^ 40 * 4193009 * 2
def baseEnd_4193009 : Nat := 2153029005628090566704209

theorem tailTrace_4193009 : CollatzResearch.WordTrace tailWord_4193009 prefixEnd_4193009 2153029005628090566704209 := by
  unfold tailWord_4193009
  simp only [CollatzResearch.WordTrace]
  refine ⟨152931602066451976769966081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101954401377634651179977387 152931602066451976769966081)
  ·
    refine ⟨114698701549838982577474561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152931602066451976769966081 114698701549838982577474561)
    ·
      refine ⟨86024026162379236933105921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114698701549838982577474561 86024026162379236933105921)
      ·
        refine ⟨64518019621784427699829441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86024026162379236933105921 64518019621784427699829441)
        ·
          refine ⟨48388514716338320774872081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64518019621784427699829441 48388514716338320774872081)
          ·
            refine ⟨36291386037253740581154061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48388514716338320774872081 36291386037253740581154061)
            ·
              refine ⟨13609269763970152717932773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36291386037253740581154061 13609269763970152717932773)
              ·
                refine ⟨2551738080744403634612395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13609269763970152717932773 2551738080744403634612395)
                ·
                  refine ⟨3827607121116605451918593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2551738080744403634612395 3827607121116605451918593)
                  ·
                    refine ⟨2870705340837454088938945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3827607121116605451918593 2870705340837454088938945)
                    ·
                      refine ⟨2153029005628090566704209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2870705340837454088938945 2153029005628090566704209)
                      ·
                        rfl

theorem cell23_4193009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 3, 4, 1, 2, 2].length) (baseStart_4193009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193009 prefixEnd_4193009 := by exact prefixLift 4193009
  have htrace : WordTrace (prefixWord ++ tailWord_4193009) baseStart_4193009 baseEnd_4193009 := by
    simpa [prefixWord, tailWord_4193009, baseEnd_4193009] using wordTrace_append hprefix tailTrace_4193009
  have hstable : (prefixWord ++ tailWord_4193009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193009).length < 2 ^ (prefixWord ++ tailWord_4193009).sum := by decide
  have hdescent : baseEnd_4193009 < baseStart_4193009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193022 : List Nat := [4, 2, 2, 1, 2, 2, 2, 1, 1, 2, 4]
def baseStart_4193022 : Nat := 118140960795 + 4193022 * 2 ^ 59
def prefixEnd_4193022 : Nat := 4983230072969 + 3 ^ 40 * 4193022 * 2
def baseEnd_4193022 : Nat := 2153035680876599015841649

theorem tailTrace_4193022 : CollatzResearch.WordTrace tailWord_4193022 prefixEnd_4193022 2153035680876599015841649 := by
  unfold tailWord_4193022
  simp only [CollatzResearch.WordTrace]
  refine ⟨19116509526925609998773665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101954717476936586660126213 19116509526925609998773665)
  ·
    refine ⟨14337382145194207499080249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19116509526925609998773665 14337382145194207499080249)
    ·
      refine ⟨10753036608895655624310187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14337382145194207499080249 10753036608895655624310187)
      ·
        refine ⟨16129554913343483436465281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10753036608895655624310187 16129554913343483436465281)
        ·
          refine ⟨12097166185007612577348961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16129554913343483436465281 12097166185007612577348961)
          ·
            refine ⟨9072874638755709433011721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12097166185007612577348961 9072874638755709433011721)
            ·
              refine ⟨6804655979066782074758791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9072874638755709433011721 6804655979066782074758791)
              ·
                refine ⟨10206983968600173112138187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6804655979066782074758791 10206983968600173112138187)
                ·
                  refine ⟨15310475952900259668207281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10206983968600173112138187 15310475952900259668207281)
                  ·
                    refine ⟨11482856964675194751155461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15310475952900259668207281 11482856964675194751155461)
                    ·
                      refine ⟨2153035680876599015841649, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11482856964675194751155461 2153035680876599015841649)
                      ·
                        rfl

theorem cell23_4193022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 2, 1, 1, 2, 4].length) (baseStart_4193022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193022 prefixEnd_4193022 := by exact prefixLift 4193022
  have htrace : WordTrace (prefixWord ++ tailWord_4193022) baseStart_4193022 baseEnd_4193022 := by
    simpa [prefixWord, tailWord_4193022, baseEnd_4193022] using wordTrace_append hprefix tailTrace_4193022
  have hstable : (prefixWord ++ tailWord_4193022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193022).length < 2 ^ (prefixWord ++ tailWord_4193022).sum := by decide
  have hdescent : baseEnd_4193022 < baseStart_4193022 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193025 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 6, 1, 3]
def baseStart_4193025 : Nat := 118140960795 + 4193025 * 2 ^ 59
def prefixEnd_4193025 : Nat := 4983230072969 + 3 ^ 40 * 4193025 * 2
def baseEnd_4193025 : Nat := 2153037221318562504104135

theorem tailTrace_4193025 : CollatzResearch.WordTrace tailWord_4193025 prefixEnd_4193025 2153037221318562504104135 := by
  unfold tailWord_4193025
  simp only [CollatzResearch.WordTrace]
  refine ⟨152932185634394011502548529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101954790422929341001699019 152932185634394011502548529)
  ·
    refine ⟨114699139225795508626911397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152932185634394011502548529 114699139225795508626911397)
    ·
      refine ⟨21506088604836657867545887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114699139225795508626911397 21506088604836657867545887)
      ·
        refine ⟨32259132907254986801318831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21506088604836657867545887 32259132907254986801318831)
        ·
          refine ⟨48388699360882480201978247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32259132907254986801318831 48388699360882480201978247)
          ·
            refine ⟨72583049041323720302967371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48388699360882480201978247 72583049041323720302967371)
            ·
              refine ⟨108874573561985580454451057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72583049041323720302967371 108874573561985580454451057)
              ·
                refine ⟨81655930171489185340838293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108874573561985580454451057 81655930171489185340838293)
                ·
                  refine ⟨3827621726788555562851795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81655930171489185340838293 3827621726788555562851795)
                  ·
                    refine ⟨5741432590182833344277693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3827621726788555562851795 5741432590182833344277693)
                    ·
                      refine ⟨2153037221318562504104135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5741432590182833344277693 2153037221318562504104135)
                      ·
                        rfl

theorem cell23_4193025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 6, 1, 3].length) (baseStart_4193025 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193025 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193025 prefixEnd_4193025 := by exact prefixLift 4193025
  have htrace : WordTrace (prefixWord ++ tailWord_4193025) baseStart_4193025 baseEnd_4193025 := by
    simpa [prefixWord, tailWord_4193025, baseEnd_4193025] using wordTrace_append hprefix tailTrace_4193025
  have hstable : (prefixWord ++ tailWord_4193025).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193025).length < 2 ^ (prefixWord ++ tailWord_4193025).sum := by decide
  have hdescent : baseEnd_4193025 < baseStart_4193025 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193028 : List Nat := [2, 3, 2, 2, 1, 1, 1, 2, 2, 7]
def baseStart_4193028 : Nat := 118140960795 + 4193028 * 2 ^ 59
def prefixEnd_4193028 : Nat := 4983230072969 + 3 ^ 40 * 4193028 * 2
def baseEnd_4193028 : Nat := 717679587253508664122207

theorem tailTrace_4193028 : CollatzResearch.WordTrace tailWord_4193028 prefixEnd_4193028 717679587253508664122207 := by
  unfold tailWord_4193028
  simp only [CollatzResearch.WordTrace]
  refine ⟨76466147526691571507453869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101954863368922095343271825 76466147526691571507453869)
  ·
    refine ⟨28674805322509339315295201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76466147526691571507453869 28674805322509339315295201)
    ·
      refine ⟨21506103991882004486471401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28674805322509339315295201 21506103991882004486471401)
      ·
        refine ⟨16129577993911503364853551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21506103991882004486471401 16129577993911503364853551)
        ·
          refine ⟨24194366990867255047280327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16129577993911503364853551 24194366990867255047280327)
          ·
            refine ⟨36291550486300882570920491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24194366990867255047280327 36291550486300882570920491)
            ·
              refine ⟨54437325729451323856380737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36291550486300882570920491 54437325729451323856380737)
              ·
                refine ⟨40827994297088492892285553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54437325729451323856380737 40827994297088492892285553)
                ·
                  refine ⟨30620995722816369669214165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40827994297088492892285553 30620995722816369669214165)
                  ·
                    refine ⟨717679587253508664122207, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30620995722816369669214165 717679587253508664122207)
                    ·
                      rfl

theorem cell23_4193028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_4193028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193028 prefixEnd_4193028 := by exact prefixLift 4193028
  have htrace : WordTrace (prefixWord ++ tailWord_4193028) baseStart_4193028 baseEnd_4193028 := by
    simpa [prefixWord, tailWord_4193028, baseEnd_4193028] using wordTrace_append hprefix tailTrace_4193028
  have hstable : (prefixWord ++ tailWord_4193028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193028).length < 2 ^ (prefixWord ++ tailWord_4193028).sum := by decide
  have hdescent : baseEnd_4193028 < baseStart_4193028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193038 : List Nat := [4, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5]
def baseStart_4193038 : Nat := 118140960795 + 4193038 * 2 ^ 59
def prefixEnd_4193038 : Nat := 4983230072969 + 3 ^ 40 * 4193038 * 2
def baseEnd_4193038 : Nat := 2153043896567070953241575

theorem tailTrace_4193038 : CollatzResearch.WordTrace tailWord_4193038 prefixEnd_4193038 2153043896567070953241575 := by
  unfold tailWord_4193038
  simp only [CollatzResearch.WordTrace]
  refine ⟨19116582472918364340346471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101955106522231276481847845 19116582472918364340346471)
  ·
    refine ⟨28674873709377546510519707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19116582472918364340346471 28674873709377546510519707)
    ·
      refine ⟨43012310564066319765779561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28674873709377546510519707 43012310564066319765779561)
      ·
        refine ⟨32259232923049739824334671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43012310564066319765779561 32259232923049739824334671)
        ·
          refine ⟨48388849384574609736502007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32259232923049739824334671 48388849384574609736502007)
          ·
            refine ⟨72583274076861914604753011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48388849384574609736502007 72583274076861914604753011)
            ·
              refine ⟨108874911115292871907129517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72583274076861914604753011 108874911115292871907129517)
              ·
                refine ⟨40828091668234826965173569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108874911115292871907129517 40828091668234826965173569)
                ·
                  refine ⟨30621068751176120223880177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40828091668234826965173569 30621068751176120223880177)
                  ·
                    refine ⟨22965801563382090167910133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30621068751176120223880177 22965801563382090167910133)
                    ·
                      refine ⟨2153043896567070953241575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22965801563382090167910133 2153043896567070953241575)
                      ·
                        rfl

theorem cell23_4193038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 3, 2, 2, 5].length) (baseStart_4193038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193038 prefixEnd_4193038 := by exact prefixLift 4193038
  have htrace : WordTrace (prefixWord ++ tailWord_4193038) baseStart_4193038 baseEnd_4193038 := by
    simpa [prefixWord, tailWord_4193038, baseEnd_4193038] using wordTrace_append hprefix tailTrace_4193038
  have hstable : (prefixWord ++ tailWord_4193038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193038).length < 2 ^ (prefixWord ++ tailWord_4193038).sum := by decide
  have hdescent : baseEnd_4193038 < baseStart_4193038 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193076 : List Nat := [2, 5, 1, 1, 4, 1, 1, 1, 1, 3, 3]
def baseStart_4193076 : Nat := 118140960795 + 4193076 * 2 ^ 59
def prefixEnd_4193076 : Nat := 4983230072969 + 3 ^ 40 * 4193076 * 2
def baseEnd_4193076 : Nat := 2153063408831941804566401

theorem tailTrace_4193076 : CollatzResearch.WordTrace tailWord_4193076 prefixEnd_4193076 2153063408831941804566401 := by
  unfold tailWord_4193076
  simp only [CollatzResearch.WordTrace]
  refine ⟨76467022878604623606327541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101956030504806164808436721 76467022878604623606327541)
  ·
    refine ⟨7168783394869183463093207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 76467022878604623606327541 7168783394869183463093207)
    ·
      refine ⟨10753175092303775194639811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7168783394869183463093207 10753175092303775194639811)
      ·
        refine ⟨16129762638455662791959717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10753175092303775194639811 16129762638455662791959717)
        ·
          refine ⟨3024330494710436773492447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16129762638455662791959717 3024330494710436773492447)
          ·
            refine ⟨4536495742065655160238671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3024330494710436773492447 4536495742065655160238671)
            ·
              refine ⟨6804743613098482740358007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4536495742065655160238671 6804743613098482740358007)
              ·
                refine ⟨10207115419647724110537011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6804743613098482740358007 10207115419647724110537011)
                ·
                  refine ⟨15310673129471586165805517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10207115419647724110537011 15310673129471586165805517)
                  ·
                    refine ⟨5741502423551844812177069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15310673129471586165805517 5741502423551844812177069)
                    ·
                      refine ⟨2153063408831941804566401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5741502423551844812177069 2153063408831941804566401)
                      ·
                        rfl

theorem cell23_4193076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 4, 1, 1, 1, 1, 3, 3].length) (baseStart_4193076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193076 prefixEnd_4193076 := by exact prefixLift 4193076
  have htrace : WordTrace (prefixWord ++ tailWord_4193076) baseStart_4193076 baseEnd_4193076 := by
    simpa [prefixWord, tailWord_4193076, baseEnd_4193076] using wordTrace_append hprefix tailTrace_4193076
  have hstable : (prefixWord ++ tailWord_4193076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193076).length < 2 ^ (prefixWord ++ tailWord_4193076).sum := by decide
  have hdescent : baseEnd_4193076 < baseStart_4193076 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193086 : List Nat := [4, 2, 1, 2, 3, 1, 2, 2, 1, 3, 2]
def baseStart_4193086 : Nat := 118140960795 + 4193086 * 2 ^ 59
def prefixEnd_4193086 : Nat := 4983230072969 + 3 ^ 40 * 4193086 * 2
def baseEnd_4193086 : Nat := 2153068543638486765441355

theorem tailTrace_4193086 : CollatzResearch.WordTrace tailWord_4193086 prefixEnd_4193086 2153068543638486765441355 := by
  unfold tailWord_4193086
  simp only [CollatzResearch.WordTrace]
  refine ⟨19116801310896627365064889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101956273658115345947012741 19116801310896627365064889)
  ·
    refine ⟨14337600983172470523798667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19116801310896627365064889 14337600983172470523798667)
    ·
      refine ⟨21506401474758705785698001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14337600983172470523798667 21506401474758705785698001)
      ·
        refine ⟨16129801106069029339273501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21506401474758705785698001 16129801106069029339273501)
        ·
          refine ⟨6048675414775886002227563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16129801106069029339273501 6048675414775886002227563)
          ·
            refine ⟨9073013122163829003341345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6048675414775886002227563 9073013122163829003341345)
            ·
              refine ⟨6804759841622871752506009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9073013122163829003341345 6804759841622871752506009)
              ·
                refine ⟨5103569881217153814379507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6804759841622871752506009 5103569881217153814379507)
                ·
                  refine ⟨7655354821825730721569261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5103569881217153814379507 7655354821825730721569261)
                  ·
                    refine ⟨2870758058184649020588473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7655354821825730721569261 2870758058184649020588473)
                    ·
                      refine ⟨2153068543638486765441355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2870758058184649020588473 2153068543638486765441355)
                      ·
                        rfl

theorem cell23_4193086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 2, 1, 3, 2].length) (baseStart_4193086 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193086 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193086 prefixEnd_4193086 := by exact prefixLift 4193086
  have htrace : WordTrace (prefixWord ++ tailWord_4193086) baseStart_4193086 baseEnd_4193086 := by
    simpa [prefixWord, tailWord_4193086, baseEnd_4193086] using wordTrace_append hprefix tailTrace_4193086
  have hstable : (prefixWord ++ tailWord_4193086).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193086).length < 2 ^ (prefixWord ++ tailWord_4193086).sum := by decide
  have hdescent : baseEnd_4193086 < baseStart_4193086 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193148 : List Nat := [2, 2, 2, 1, 1, 1, 1, 3, 2, 8]
def baseStart_4193148 : Nat := 118140960795 + 4193148 * 2 ^ 59
def prefixEnd_4193148 : Nat := 4983230072969 + 3 ^ 40 * 4193148 * 2
def baseEnd_4193148 : Nat := 717700126479688507622023

theorem tailTrace_4193148 : CollatzResearch.WordTrace tailWord_4193148 prefixEnd_4193148 717700126479688507622023 := by
  unfold tailWord_4193148
  simp only [CollatzResearch.WordTrace]
  refine ⟨76468335906474201754638049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101957781208632269006184065 76468335906474201754638049)
  ·
    refine ⟨57351251929855651315978537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76468335906474201754638049 57351251929855651315978537)
    ·
      refine ⟨43013438947391738486983903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57351251929855651315978537 43013438947391738486983903)
      ·
        refine ⟨64520158421087607730475855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43013438947391738486983903 64520158421087607730475855)
        ·
          refine ⟨96780237631631411595713783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64520158421087607730475855 96780237631631411595713783)
          ·
            refine ⟨145170356447447117393570675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96780237631631411595713783 145170356447447117393570675)
            ·
              refine ⟨217755534671170676090356013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145170356447447117393570675 217755534671170676090356013)
              ·
                refine ⟨81658325501689003533883505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217755534671170676090356013 81658325501689003533883505)
                ·
                  refine ⟨61243744126266752650412629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 81658325501689003533883505 61243744126266752650412629)
                  ·
                    refine ⟨717700126479688507622023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61243744126266752650412629 717700126479688507622023)
                    ·
                      rfl

theorem cell23_4193148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_4193148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193148 prefixEnd_4193148 := by exact prefixLift 4193148
  have htrace : WordTrace (prefixWord ++ tailWord_4193148) baseStart_4193148 baseEnd_4193148 := by
    simpa [prefixWord, tailWord_4193148, baseEnd_4193148] using wordTrace_append hprefix tailTrace_4193148
  have hstable : (prefixWord ++ tailWord_4193148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193148).length < 2 ^ (prefixWord ++ tailWord_4193148).sum := by decide
  have hdescent : baseEnd_4193148 < baseStart_4193148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193172 : List Nat := [2, 4, 2, 1, 1, 1, 1, 4, 2, 1, 4]
def baseStart_4193172 : Nat := 118140960795 + 4193172 * 2 ^ 59
def prefixEnd_4193172 : Nat := 4983230072969 + 3 ^ 40 * 4193172 * 2
def baseEnd_4193172 : Nat := 2153112702974773428965959

theorem tailTrace_4193172 : CollatzResearch.WordTrace tailWord_4193172 prefixEnd_4193172 2153112702974773428965959 := by
  unfold tailWord_4193172
  simp only [CollatzResearch.WordTrace]
  refine ⟨76468773582430727804074885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101958364776574303738766513 76468773582430727804074885)
  ·
    refine ⟨14337895046705761463264041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76468773582430727804074885 14337895046705761463264041)
    ·
      refine ⟨10753421285029321097448031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14337895046705761463264041 10753421285029321097448031)
      ·
        refine ⟨16130131927543981646172047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10753421285029321097448031 16130131927543981646172047)
        ·
          refine ⟨24195197891315972469258071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16130131927543981646172047 24195197891315972469258071)
          ·
            refine ⟨36292796836973958703887107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24195197891315972469258071 36292796836973958703887107)
            ·
              refine ⟨54439195255460938055830661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36292796836973958703887107 54439195255460938055830661)
              ·
                refine ⟨10207349110398925885468249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54439195255460938055830661 10207349110398925885468249)
                ·
                  refine ⟨7655511832799194414101187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10207349110398925885468249 7655511832799194414101187)
                  ·
                    refine ⟨11483267749198791621151781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7655511832799194414101187 11483267749198791621151781)
                    ·
                      refine ⟨2153112702974773428965959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11483267749198791621151781 2153112702974773428965959)
                      ·
                        rfl

theorem cell23_4193172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 1, 4, 2, 1, 4].length) (baseStart_4193172 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193172 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193172 prefixEnd_4193172 := by exact prefixLift 4193172
  have htrace : WordTrace (prefixWord ++ tailWord_4193172) baseStart_4193172 baseEnd_4193172 := by
    simpa [prefixWord, tailWord_4193172, baseEnd_4193172] using wordTrace_append hprefix tailTrace_4193172
  have hstable : (prefixWord ++ tailWord_4193172).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193172).length < 2 ^ (prefixWord ++ tailWord_4193172).sum := by decide
  have hdescent : baseEnd_4193172 < baseStart_4193172 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193209 : List Nat := [1, 2, 1, 4, 2, 4, 1, 1, 2, 2, 3]
def baseStart_4193209 : Nat := 118140960795 + 4193209 * 2 ^ 59
def prefixEnd_4193209 : Nat := 4983230072969 + 3 ^ 40 * 4193209 * 2
def baseEnd_4193209 : Nat := 2153131701758989784203289

theorem tailTrace_4193209 : CollatzResearch.WordTrace tailWord_4193209 prefixEnd_4193209 2153131701758989784203289 := by
  unfold tailWord_4193209
  simp only [CollatzResearch.WordTrace]
  refine ⟨152938896665727410927246681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101959264443818273951497787 152938896665727410927246681)
  ·
    refine ⟨114704172499295558195435011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152938896665727410927246681 114704172499295558195435011)
    ·
      refine ⟨172056258748943337293152517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114704172499295558195435011 172056258748943337293152517)
      ·
        refine ⟨32260548515426875742466097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172056258748943337293152517 32260548515426875742466097)
        ·
          refine ⟨24195411386570156806849573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32260548515426875742466097 24195411386570156806849573)
          ·
            refine ⟨4536639634981904401284295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24195411386570156806849573 4536639634981904401284295)
            ·
              refine ⟨6804959452472856601926443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4536639634981904401284295 6804959452472856601926443)
              ·
                refine ⟨10207439178709284902889665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6804959452472856601926443 10207439178709284902889665)
                ·
                  refine ⟨7655579384031963677167249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10207439178709284902889665 7655579384031963677167249)
                  ·
                    refine ⟨5741684538023972757875437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7655579384031963677167249 5741684538023972757875437)
                    ·
                      refine ⟨2153131701758989784203289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5741684538023972757875437 2153131701758989784203289)
                      ·
                        rfl

theorem cell23_4193209_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_4193209 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193209 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193209 prefixEnd_4193209 := by exact prefixLift 4193209
  have htrace : WordTrace (prefixWord ++ tailWord_4193209) baseStart_4193209 baseEnd_4193209 := by
    simpa [prefixWord, tailWord_4193209, baseEnd_4193209] using wordTrace_append hprefix tailTrace_4193209
  have hstable : (prefixWord ++ tailWord_4193209).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193209).length < 2 ^ (prefixWord ++ tailWord_4193209).sum := by decide
  have hdescent : baseEnd_4193209 < baseStart_4193209 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193209) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193232 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 4, 3, 2]
def baseStart_4193232 : Nat := 118140960795 + 4193232 * 2 ^ 59
def prefixEnd_4193232 : Nat := 4983230072969 + 3 ^ 40 * 4193232 * 2
def baseEnd_4193232 : Nat := 2153143511814043194215683

theorem tailTrace_4193232 : CollatzResearch.WordTrace tailWord_4193232 prefixEnd_4193232 2153143511814043194215683 := by
  unfold tailWord_4193232
  simp only [CollatzResearch.WordTrace]
  refine ⟨76469867772322042927666975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101959823696429390570222633 76469867772322042927666975)
  ·
    refine ⟨114704801658483064391500463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76469867772322042927666975 114704801658483064391500463)
    ·
      refine ⟨172057202487724596587250695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114704801658483064391500463 172057202487724596587250695)
      ·
        refine ⟨258085803731586894880876043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172057202487724596587250695 258085803731586894880876043)
        ·
          refine ⟨387128705597380342321314065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258085803731586894880876043 387128705597380342321314065)
          ·
            refine ⟨290346529198035256740985549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387128705597380342321314065 290346529198035256740985549)
            ·
              refine ⟨108879948449263221277869581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290346529198035256740985549 108879948449263221277869581)
              ·
                refine ⟨40829980668473707979201093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108879948449263221277869581 40829980668473707979201093)
                ·
                  refine ⟨7655621375338820246100205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40829980668473707979201093 7655621375338820246100205)
                  ·
                    refine ⟨2870858015752057592287577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7655621375338820246100205 2870858015752057592287577)
                    ·
                      refine ⟨2153143511814043194215683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2870858015752057592287577 2153143511814043194215683)
                      ·
                        rfl

theorem cell23_4193232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 4, 3, 2].length) (baseStart_4193232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193232 prefixEnd_4193232 := by exact prefixLift 4193232
  have htrace : WordTrace (prefixWord ++ tailWord_4193232) baseStart_4193232 baseEnd_4193232 := by
    simpa [prefixWord, tailWord_4193232, baseEnd_4193232] using wordTrace_append hprefix tailTrace_4193232
  have hstable : (prefixWord ++ tailWord_4193232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193232).length < 2 ^ (prefixWord ++ tailWord_4193232).sum := by decide
  have hdescent : baseEnd_4193232 < baseStart_4193232 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193275 : List Nat := [1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 4]
def baseStart_4193275 : Nat := 118140960795 + 4193275 * 2 ^ 59
def prefixEnd_4193275 : Nat := 4983230072969 + 3 ^ 40 * 4193275 * 2
def baseEnd_4193275 : Nat := 2153165591482186525977985

theorem tailTrace_4193275 : CollatzResearch.WordTrace tailWord_4193275 prefixEnd_4193275 2153165591482186525977985 := by
  unfold tailWord_4193275
  simp only [CollatzResearch.WordTrace]
  refine ⟨152941303883488304199149279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101960869255658869466099519 152941303883488304199149279)
  ·
    refine ⟨229411955825232456298723919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152941303883488304199149279 229411955825232456298723919)
    ·
      refine ⟨344117933737848684448085879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229411955825232456298723919 344117933737848684448085879)
      ·
        refine ⟨516176900606773026672128819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344117933737848684448085879 516176900606773026672128819)
        ·
          refine ⟨774265350910159540008193229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516176900606773026672128819 774265350910159540008193229)
          ·
            refine ⟨290349506591309827503072461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 774265350910159540008193229 290349506591309827503072461)
            ·
              refine ⟨108881064971741185313652173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 290349506591309827503072461 108881064971741185313652173)
              ·
                refine ⟨40830399364402944492619565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108881064971741185313652173 40830399364402944492619565)
                ·
                  refine ⟨15311399761651104184732337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40830399364402944492619565 15311399761651104184732337)
                  ·
                    refine ⟨11483549821238328138549253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15311399761651104184732337 11483549821238328138549253)
                    ·
                      refine ⟨2153165591482186525977985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11483549821238328138549253 2153165591482186525977985)
                      ·
                        rfl

theorem cell23_4193275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 3, 3, 2, 4].length) (baseStart_4193275 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193275 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193275 prefixEnd_4193275 := by exact prefixLift 4193275
  have htrace : WordTrace (prefixWord ++ tailWord_4193275) baseStart_4193275 baseEnd_4193275 := by
    simpa [prefixWord, tailWord_4193275, baseEnd_4193275] using wordTrace_append hprefix tailTrace_4193275
  have hstable : (prefixWord ++ tailWord_4193275).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193275).length < 2 ^ (prefixWord ++ tailWord_4193275).sum := by decide
  have hdescent : baseEnd_4193275 < baseStart_4193275 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193316 : List Nat := [2, 3, 1, 4, 1, 1, 3, 2, 1, 2, 3]
def baseStart_4193316 : Nat := 118140960795 + 4193316 * 2 ^ 59
def prefixEnd_4193316 : Nat := 4983230072969 + 3 ^ 40 * 4193316 * 2
def baseEnd_4193316 : Nat := 2153186644189020865565297

theorem tailTrace_4193316 : CollatzResearch.WordTrace tailWord_4193316 prefixEnd_4193316 2153186644189020865565297 := by
  unfold tailWord_4193316
  simp only [CollatzResearch.WordTrace]
  refine ⟨76471399638169884100695901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101961866184226512134261201 76471399638169884100695901)
  ·
    refine ⟨28676774864313706537760963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76471399638169884100695901 28676774864313706537760963)
    ·
      refine ⟨43015162296470559806641445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28676774864313706537760963 43015162296470559806641445)
      ·
        refine ⟨8065342930588229963745271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43015162296470559806641445 8065342930588229963745271)
        ·
          refine ⟨12098014395882344945617907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8065342930588229963745271 12098014395882344945617907)
          ·
            refine ⟨18147021593823517418426861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12098014395882344945617907 18147021593823517418426861)
            ·
              refine ⟨6805133097683819031910073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18147021593823517418426861 6805133097683819031910073)
              ·
                refine ⟨5103849823262864273932555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6805133097683819031910073 5103849823262864273932555)
                ·
                  refine ⟨7655774734894296410898833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5103849823262864273932555 7655774734894296410898833)
                  ·
                    refine ⟨5741831051170722308174125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7655774734894296410898833 5741831051170722308174125)
                    ·
                      refine ⟨2153186644189020865565297, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5741831051170722308174125 2153186644189020865565297)
                      ·
                        rfl

theorem cell23_4193316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_4193316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193316 prefixEnd_4193316 := by exact prefixLift 4193316
  have htrace : WordTrace (prefixWord ++ tailWord_4193316) baseStart_4193316 baseEnd_4193316 := by
    simpa [prefixWord, tailWord_4193316, baseEnd_4193316] using wordTrace_append hprefix tailTrace_4193316
  have hstable : (prefixWord ++ tailWord_4193316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193316).length < 2 ^ (prefixWord ++ tailWord_4193316).sum := by decide
  have hdescent : baseEnd_4193316 < baseStart_4193316 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193362 : List Nat := [3, 2, 2, 1, 3, 1, 1, 1, 1, 8]
def baseStart_4193362 : Nat := 118140960795 + 4193362 * 2 ^ 59
def prefixEnd_4193362 : Nat := 4983230072969 + 3 ^ 40 * 4193362 * 2
def baseEnd_4193362 : Nat := 717736754766375895196695

theorem tailTrace_4193362 : CollatzResearch.WordTrace tailWord_4193362 prefixEnd_4193362 717736754766375895196695 := by
  unfold tailWord_4193362
  simp only [CollatzResearch.WordTrace]
  refine ⟨38236119258543279514391585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101962984689448745371710893 38236119258543279514391585)
  ·
    refine ⟨28677089443907459635793689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38236119258543279514391585 28677089443907459635793689)
    ·
      refine ⟨21507817082930594726845267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28677089443907459635793689 21507817082930594726845267)
      ·
        refine ⟨32261725624395892090267901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21507817082930594726845267 32261725624395892090267901)
        ·
          refine ⟨12098147109148459533850463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32261725624395892090267901 12098147109148459533850463)
          ·
            refine ⟨18147220663722689300775695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12098147109148459533850463 18147220663722689300775695)
            ·
              refine ⟨27220830995584033951163543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18147220663722689300775695 27220830995584033951163543)
              ·
                refine ⟨40831246493376050926745315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27220830995584033951163543 40831246493376050926745315)
                ·
                  refine ⟨61246869740064076390117973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40831246493376050926745315 61246869740064076390117973)
                  ·
                    refine ⟨717736754766375895196695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61246869740064076390117973 717736754766375895196695)
                    ·
                      rfl

theorem cell23_4193362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_4193362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193362 prefixEnd_4193362 := by exact prefixLift 4193362
  have htrace : WordTrace (prefixWord ++ tailWord_4193362) baseStart_4193362 baseEnd_4193362 := by
    simpa [prefixWord, tailWord_4193362, baseEnd_4193362] using wordTrace_append hprefix tailTrace_4193362
  have hstable : (prefixWord ++ tailWord_4193362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193362).length < 2 ^ (prefixWord ++ tailWord_4193362).sum := by decide
  have hdescent : baseEnd_4193362 < baseStart_4193362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193386 : List Nat := [3, 1, 3, 2, 2, 1, 2, 2, 1, 4, 2]
def baseStart_4193386 : Nat := 118140960795 + 4193386 * 2 ^ 59
def prefixEnd_4193386 : Nat := 4983230072969 + 3 ^ 40 * 4193386 * 2
def baseEnd_4193386 : Nat := 2153222587834835591689975

theorem tailTrace_4193386 : CollatzResearch.WordTrace tailWord_4193386 prefixEnd_4193386 2153222587834835591689975 := by
  unfold tailWord_4193386
  simp only [CollatzResearch.WordTrace]
  refine ⟨38236338096521542539110003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101963568257390780104293341 38236338096521542539110003)
  ·
    refine ⟨57354507144782313808665005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38236338096521542539110003 57354507144782313808665005)
    ·
      refine ⟨21507940179293367678249377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57354507144782313808665005 21507940179293367678249377)
      ·
        refine ⟨16130955134470025758687033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21507940179293367678249377 16130955134470025758687033)
        ·
          refine ⟨12098216350852519319015275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16130955134470025758687033 12098216350852519319015275)
          ·
            refine ⟨18147324526278778978522913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12098216350852519319015275 18147324526278778978522913)
            ·
              refine ⟨13610493394709084233892185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18147324526278778978522913 13610493394709084233892185)
              ·
                refine ⟨10207870046031813175419139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13610493394709084233892185 10207870046031813175419139)
                ·
                  refine ⟨15311805069047719763128709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10207870046031813175419139 15311805069047719763128709)
                  ·
                    refine ⟨2870963450446447455586633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15311805069047719763128709 2870963450446447455586633)
                    ·
                      refine ⟨2153222587834835591689975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2870963450446447455586633 2153222587834835591689975)
                      ·
                        rfl

theorem cell23_4193386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_4193386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193386 prefixEnd_4193386 := by exact prefixLift 4193386
  have htrace : WordTrace (prefixWord ++ tailWord_4193386) baseStart_4193386 baseEnd_4193386 := by
    simpa [prefixWord, tailWord_4193386, baseEnd_4193386] using wordTrace_append hprefix tailTrace_4193386
  have hstable : (prefixWord ++ tailWord_4193386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193386).length < 2 ^ (prefixWord ++ tailWord_4193386).sum := by decide
  have hdescent : baseEnd_4193386 < baseStart_4193386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193390 : List Nat := [4, 1, 2, 2, 1, 4, 2, 1, 1, 3, 2]
def baseStart_4193390 : Nat := 118140960795 + 4193390 * 2 ^ 59
def prefixEnd_4193390 : Nat := 4983230072969 + 3 ^ 40 * 4193390 * 2
def baseEnd_4193390 : Nat := 2153224641757453576039957

theorem tailTrace_4193390 : CollatzResearch.WordTrace tailWord_4193390 prefixEnd_4193390 2153224641757453576039957 := by
  unfold tailWord_4193390
  simp only [CollatzResearch.WordTrace]
  refine ⟨19118187284758959854948203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101963665518714452559723749 19118187284758959854948203)
  ·
    refine ⟨28677280927138439782422305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19118187284758959854948203 28677280927138439782422305)
    ·
      refine ⟨21507960695353829836816729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28677280927138439782422305 21507960695353829836816729)
      ·
        refine ⟨16130970521515372377612547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21507960695353829836816729 16130970521515372377612547)
        ·
          refine ⟨24196455782273058566418821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16130970521515372377612547 24196455782273058566418821)
          ·
            refine ⟨4536835459176198481203529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 24196455782273058566418821 4536835459176198481203529)
            ·
              refine ⟨3402626594382148860902647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4536835459176198481203529 3402626594382148860902647)
              ·
                refine ⟨5103939891573223291353971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3402626594382148860902647 5103939891573223291353971)
                ·
                  refine ⟨7655909837359834937030957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5103939891573223291353971 7655909837359834937030957)
                  ·
                    refine ⟨2870966189009938101386609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7655909837359834937030957 2870966189009938101386609)
                    ·
                      refine ⟨2153224641757453576039957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2870966189009938101386609 2153224641757453576039957)
                      ·
                        rfl

theorem cell23_4193390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 2, 1, 1, 3, 2].length) (baseStart_4193390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193390 prefixEnd_4193390 := by exact prefixLift 4193390
  have htrace : WordTrace (prefixWord ++ tailWord_4193390) baseStart_4193390 baseEnd_4193390 := by
    simpa [prefixWord, tailWord_4193390, baseEnd_4193390] using wordTrace_append hprefix tailTrace_4193390
  have hstable : (prefixWord ++ tailWord_4193390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193390).length < 2 ^ (prefixWord ++ tailWord_4193390).sum := by decide
  have hdescent : baseEnd_4193390 < baseStart_4193390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193397 : List Nat := [1, 3, 4, 3, 2, 1, 1, 2, 2, 1, 3]
def baseStart_4193397 : Nat := 118140960795 + 4193397 * 2 ^ 59
def prefixEnd_4193397 : Nat := 4983230072969 + 3 ^ 40 * 4193397 * 2
def baseEnd_4193397 : Nat := 2153228236122035048652425

theorem tailTrace_4193397 : CollatzResearch.WordTrace tailWord_4193397 prefixEnd_4193397 2153228236122035048652425 := by
  unfold tailWord_4193397
  simp only [CollatzResearch.WordTrace]
  refine ⟨152945753589046319035090445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101963835726030879356726963 152945753589046319035090445)
  ·
    refine ⟨57354657595892369638158917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152945753589046319035090445 57354657595892369638158917)
    ·
      refine ⟨10753998299229819307154797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57354657595892369638158917 10753998299229819307154797)
      ·
        refine ⟨4032749362211182240183049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 10753998299229819307154797 4032749362211182240183049)
        ·
          refine ⟨3024562021658386680137287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4032749362211182240183049 3024562021658386680137287)
          ·
            refine ⟨4536843032487580020205931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3024562021658386680137287 4536843032487580020205931)
            ·
              refine ⟨6805264548731370030308897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4536843032487580020205931 6805264548731370030308897)
              ·
                refine ⟨5103948411548527522731673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6805264548731370030308897 5103948411548527522731673)
                ·
                  refine ⟨3827961308661395642048755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5103948411548527522731673 3827961308661395642048755)
                  ·
                    refine ⟨5741941962992093463073133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3827961308661395642048755 5741941962992093463073133)
                    ·
                      refine ⟨2153228236122035048652425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5741941962992093463073133 2153228236122035048652425)
                      ·
                        rfl

theorem cell23_4193397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_4193397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193397 prefixEnd_4193397 := by exact prefixLift 4193397
  have htrace : WordTrace (prefixWord ++ tailWord_4193397) baseStart_4193397 baseEnd_4193397 := by
    simpa [prefixWord, tailWord_4193397, baseEnd_4193397] using wordTrace_append hprefix tailTrace_4193397
  have hstable : (prefixWord ++ tailWord_4193397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193397).length < 2 ^ (prefixWord ++ tailWord_4193397).sum := by decide
  have hdescent : baseEnd_4193397 < baseStart_4193397 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193409 : List Nat := [1, 2, 4, 2, 2, 2, 2, 1, 7]
def baseStart_4193409 : Nat := 118140960795 + 4193409 * 2 ^ 59
def prefixEnd_4193409 : Nat := 4983230072969 + 3 ^ 40 * 4193409 * 2
def baseEnd_4193409 : Nat := 239248266432209889078041

theorem tailTrace_4193409 : CollatzResearch.WordTrace tailWord_4193409 prefixEnd_4193409 239248266432209889078041 := by
  unfold tailWord_4193409
  simp only [CollatzResearch.WordTrace]
  refine ⟨152946191265002845084527281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101964127510001896723018187 152946191265002845084527281)
  ·
    refine ⟨114709643448752133813395461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152946191265002845084527281 114709643448752133813395461)
    ·
      refine ⟨21508058146641025090011649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114709643448752133813395461 21508058146641025090011649)
      ·
        refine ⟨16131043609980768817508737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21508058146641025090011649 16131043609980768817508737)
        ·
          refine ⟨12098282707485576613131553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16131043609980768817508737 12098282707485576613131553)
          ·
            refine ⟨9073712030614182459848665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12098282707485576613131553 9073712030614182459848665)
            ·
              refine ⟨6805284022960636844886499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9073712030614182459848665 6805284022960636844886499)
              ·
                refine ⟨10207926034440955267329749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6805284022960636844886499 10207926034440955267329749)
                ·
                  refine ⟨239248266432209889078041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10207926034440955267329749 239248266432209889078041)
                  ·
                    rfl

theorem cell23_4193409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 2, 1, 7].length) (baseStart_4193409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193409 prefixEnd_4193409 := by exact prefixLift 4193409
  have htrace : WordTrace (prefixWord ++ tailWord_4193409) baseStart_4193409 baseEnd_4193409 := by
    simpa [prefixWord, tailWord_4193409, baseEnd_4193409] using wordTrace_append hprefix tailTrace_4193409
  have hstable : (prefixWord ++ tailWord_4193409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193409).length < 2 ^ (prefixWord ++ tailWord_4193409).sum := by decide
  have hdescent : baseEnd_4193409 < baseStart_4193409 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193459 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 4, 4, 2]
def baseStart_4193459 : Nat := 118140960795 + 4193459 * 2 ^ 59
def prefixEnd_4193459 : Nat := 4983230072969 + 3 ^ 40 * 4193459 * 2
def baseEnd_4193459 : Nat := 2153260071922613806077139

theorem tailTrace_4193459 : CollatzResearch.WordTrace tailWord_4193459 prefixEnd_4193459 2153260071922613806077139 := by
  unfold tailWord_4193459
  simp only [CollatzResearch.WordTrace]
  refine ⟨152948014914821703623847431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101965343276547802415898287 152948014914821703623847431)
  ·
    refine ⟨229422022372232555435771147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152948014914821703623847431 229422022372232555435771147)
    ·
      refine ⟨344133033558348833153656721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229422022372232555435771147 344133033558348833153656721)
      ·
        refine ⟨258099775168761624865242541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344133033558348833153656721 258099775168761624865242541)
        ·
          refine ⟨96787415688285609324465953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 258099775168761624865242541 96787415688285609324465953)
          ·
            refine ⟨72590561766214206993349465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96787415688285609324465953 72590561766214206993349465)
            ·
              refine ⟨54442921324660655245012099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72590561766214206993349465 54442921324660655245012099)
              ·
                refine ⟨81664381986990982867518149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54442921324660655245012099 81664381986990982867518149)
                ·
                  refine ⟨15312071622560809287659653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81664381986990982867518149 15312071622560809287659653)
                  ·
                    refine ⟨2871013429230151741436185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15312071622560809287659653 2871013429230151741436185)
                    ·
                      refine ⟨2153260071922613806077139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2871013429230151741436185 2153260071922613806077139)
                      ·
                        rfl

theorem cell23_4193459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 4, 4, 2].length) (baseStart_4193459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193459 prefixEnd_4193459 := by exact prefixLift 4193459
  have htrace : WordTrace (prefixWord ++ tailWord_4193459) baseStart_4193459 baseEnd_4193459 := by
    simpa [prefixWord, tailWord_4193459, baseEnd_4193459] using wordTrace_append hprefix tailTrace_4193459
  have hstable : (prefixWord ++ tailWord_4193459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193459).length < 2 ^ (prefixWord ++ tailWord_4193459).sum := by decide
  have hdescent : baseEnd_4193459 < baseStart_4193459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193559 : List Nat := [1, 1, 3, 4, 1, 1, 1, 4, 1, 6]
def baseStart_4193559 : Nat := 118140960795 + 4193559 * 2 ^ 59
def prefixEnd_4193559 : Nat := 4983230072969 + 3 ^ 40 * 4193559 * 2
def baseEnd_4193559 : Nat := 717770473329354471608893

theorem tailTrace_4193559 : CollatzResearch.WordTrace tailWord_4193559 prefixEnd_4193559 717770473329354471608893 := by
  unfold tailWord_4193559
  simp only [CollatzResearch.WordTrace]
  refine ⟨152951662214459420702487731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101967774809639613801658487 152951662214459420702487731)
  ·
    refine ⟨229427493321689131053731597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152951662214459420702487731 229427493321689131053731597)
    ·
      refine ⟨86035309995633424145149349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229427493321689131053731597 86035309995633424145149349)
      ·
        refine ⟨16131620624181267027215503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86035309995633424145149349 16131620624181267027215503)
        ·
          refine ⟨24197430936271900540823255, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16131620624181267027215503 24197430936271900540823255)
          ·
            refine ⟨36296146404407850811234883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24197430936271900540823255 36296146404407850811234883)
            ·
              refine ⟨54444219606611776216852325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36296146404407850811234883 54444219606611776216852325)
              ·
                refine ⟨10208291176239708040659811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54444219606611776216852325 10208291176239708040659811)
                ·
                  refine ⟨15312436764359562060989717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10208291176239708040659811 15312436764359562060989717)
                  ·
                    refine ⟨717770473329354471608893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15312436764359562060989717 717770473329354471608893)
                    ·
                      rfl

theorem cell23_4193559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 1, 4, 1, 6].length) (baseStart_4193559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193559 prefixEnd_4193559 := by exact prefixLift 4193559
  have htrace : WordTrace (prefixWord ++ tailWord_4193559) baseStart_4193559 baseEnd_4193559 := by
    simpa [prefixWord, tailWord_4193559, baseEnd_4193559] using wordTrace_append hprefix tailTrace_4193559
  have hstable : (prefixWord ++ tailWord_4193559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193559).length < 2 ^ (prefixWord ++ tailWord_4193559).sum := by decide
  have hdescent : baseEnd_4193559 < baseStart_4193559 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193560 : List Nat := [2, 1, 2, 3, 1, 4, 2, 3, 1, 1, 3]
def baseStart_4193560 : Nat := 118140960795 + 4193560 * 2 ^ 59
def prefixEnd_4193560 : Nat := 4983230072969 + 3 ^ 40 * 4193560 * 2
def baseEnd_4193560 : Nat := 2153311933468717910914175

theorem tailTrace_4193560 : CollatzResearch.WordTrace tailWord_4193560 prefixEnd_4193560 2153311933468717910914175 := by
  unfold tailWord_4193560
  simp only [CollatzResearch.WordTrace]
  refine ⟨76475849343727898936637067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101967799124970531915516089 76475849343727898936637067)
  ·
    refine ⟨114713774015591848404955601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76475849343727898936637067 114713774015591848404955601)
    ·
      refine ⟨86035330511693886303716701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114713774015591848404955601 86035330511693886303716701)
      ·
        refine ⟨32263248941885207363893763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86035330511693886303716701 32263248941885207363893763)
        ·
          refine ⟨48394873412827811045840645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32263248941885207363893763 48394873412827811045840645)
          ·
            refine ⟨9074038764905214571095121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48394873412827811045840645 9074038764905214571095121)
            ·
              refine ⟨6805529073678910928321341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9074038764905214571095121 6805529073678910928321341)
              ·
                refine ⟨2552073402629591598120503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6805529073678910928321341 2552073402629591598120503)
                ·
                  refine ⟨3828110103944387397180755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2552073402629591598120503 3828110103944387397180755)
                  ·
                    refine ⟨5742165155916581095771133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3828110103944387397180755 5742165155916581095771133)
                    ·
                      refine ⟨2153311933468717910914175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5742165155916581095771133 2153311933468717910914175)
                      ·
                        rfl

theorem cell23_4193560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 2, 3, 1, 1, 3].length) (baseStart_4193560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193560 prefixEnd_4193560 := by exact prefixLift 4193560
  have htrace : WordTrace (prefixWord ++ tailWord_4193560) baseStart_4193560 baseEnd_4193560 := by
    simpa [prefixWord, tailWord_4193560, baseEnd_4193560] using wordTrace_append hprefix tailTrace_4193560
  have hstable : (prefixWord ++ tailWord_4193560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193560).length < 2 ^ (prefixWord ++ tailWord_4193560).sum := by decide
  have hdescent : baseEnd_4193560 < baseStart_4193560 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193569 : List Nat := [1, 2, 3, 2, 1, 1, 1, 5, 1, 1, 5]
def baseStart_4193569 : Nat := 118140960795 + 4193569 * 2 ^ 59
def prefixEnd_4193569 : Nat := 4983230072969 + 3 ^ 40 * 4193569 * 2
def baseEnd_4193569 : Nat := 2153316554794608375701633

theorem tailTrace_4193569 : CollatzResearch.WordTrace tailWord_4193569 prefixEnd_4193569 2153316554794608375701633 := by
  unfold tailWord_4193569
  simp only [CollatzResearch.WordTrace]
  refine ⟨152952026944423192410351761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101968017962948794940234507 152952026944423192410351761)
  ·
    refine ⟨114714020208317394307763821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152952026944423192410351761 114714020208317394307763821)
    ·
      refine ⟨43017757578119022865411433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114714020208317394307763821 43017757578119022865411433)
      ·
        refine ⟨32263318183589267149058575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43017757578119022865411433 32263318183589267149058575)
        ·
          refine ⟨48394977275383900723587863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32263318183589267149058575 48394977275383900723587863)
          ·
            refine ⟨72592465913075851085381795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48394977275383900723587863 72592465913075851085381795)
            ·
              refine ⟨108888698869613776628072693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72592465913075851085381795 108888698869613776628072693)
              ·
                refine ⟨10208315519026291558881815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 108888698869613776628072693 10208315519026291558881815)
                ·
                  refine ⟨15312473278539437338322723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10208315519026291558881815 15312473278539437338322723)
                  ·
                    refine ⟨22968709917809156007484085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15312473278539437338322723 22968709917809156007484085)
                    ·
                      refine ⟨2153316554794608375701633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22968709917809156007484085 2153316554794608375701633)
                      ·
                        rfl

theorem cell23_4193569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_4193569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193569 prefixEnd_4193569 := by exact prefixLift 4193569
  have htrace : WordTrace (prefixWord ++ tailWord_4193569) baseStart_4193569 baseEnd_4193569 := by
    simpa [prefixWord, tailWord_4193569, baseEnd_4193569] using wordTrace_append hprefix tailTrace_4193569
  have hstable : (prefixWord ++ tailWord_4193569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193569).length < 2 ^ (prefixWord ++ tailWord_4193569).sum := by decide
  have hdescent : baseEnd_4193569 < baseStart_4193569 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193586 : List Nat := [3, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5]
def baseStart_4193586 : Nat := 118140960795 + 4193586 * 2 ^ 59
def prefixEnd_4193586 : Nat := 4983230072969 + 3 ^ 40 * 4193586 * 2
def baseEnd_4193586 : Nat := 2153325283965734809189055

theorem tailTrace_4193586 : CollatzResearch.WordTrace tailWord_4193586 prefixEnd_4193586 2153325283965734809189055 := by
  unfold tailWord_4193586
  simp only [CollatzResearch.WordTrace]
  refine ⟨38238161746340401078430153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101968431323574402875813741 38238161746340401078430153)
  ·
    refine ⟨28678621309755300808822615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38238161746340401078430153 28678621309755300808822615)
    ·
      refine ⟨43017931964632951213233923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28678621309755300808822615 43017931964632951213233923)
      ·
        refine ⟨64526897946949426819850885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43017931964632951213233923 64526897946949426819850885)
        ·
          refine ⟨12098793365053017528722041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64526897946949426819850885 12098793365053017528722041)
          ·
            refine ⟨9074095023789763146541531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12098793365053017528722041 9074095023789763146541531)
            ·
              refine ⟨13611142535684644719812297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9074095023789763146541531 13611142535684644719812297)
              ·
                refine ⟨10208356901763483539859223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13611142535684644719812297 10208356901763483539859223)
                ·
                  refine ⟨15312535352645225309788835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10208356901763483539859223 15312535352645225309788835)
                  ·
                    refine ⟨22968803028967837964683253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15312535352645225309788835 22968803028967837964683253)
                    ·
                      refine ⟨2153325283965734809189055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22968803028967837964683253 2153325283965734809189055)
                      ·
                        rfl

theorem cell23_4193586_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 1, 2, 1, 1, 5].length) (baseStart_4193586 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193586 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193586 prefixEnd_4193586 := by exact prefixLift 4193586
  have htrace : WordTrace (prefixWord ++ tailWord_4193586) baseStart_4193586 baseEnd_4193586 := by
    simpa [prefixWord, tailWord_4193586, baseEnd_4193586] using wordTrace_append hprefix tailTrace_4193586
  have hstable : (prefixWord ++ tailWord_4193586).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193586).length < 2 ^ (prefixWord ++ tailWord_4193586).sum := by decide
  have hdescent : baseEnd_4193586 < baseStart_4193586 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193586) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193593 : List Nat := [1, 2, 1, 6, 2, 2, 1, 1, 1, 6]
def baseStart_4193593 : Nat := 118140960795 + 4193593 * 2 ^ 59
def prefixEnd_4193593 : Nat := 4983230072969 + 3 ^ 40 * 4193593 * 2
def baseEnd_4193593 : Nat := 717776292776772093933841

theorem tailTrace_4193593 : CollatzResearch.WordTrace tailWord_4193593 prefixEnd_4193593 717776292776772093933841 := by
  unfold tailWord_4193593
  simp only [CollatzResearch.WordTrace]
  refine ⟨152952902296336244509225433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101968601530890829672816955 152952902296336244509225433)
  ·
    refine ⟨114714676722252183381919075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152952902296336244509225433 114714676722252183381919075)
    ·
      refine ⟨172072015083378275072878613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114714676722252183381919075 172072015083378275072878613)
      ·
        refine ⟨8065875707033356644041185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 172072015083378275072878613 8065875707033356644041185)
        ·
          refine ⟨6049406780275017483030889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8065875707033356644041185 6049406780275017483030889)
          ·
            refine ⟨4537055085206263112273167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6049406780275017483030889 4537055085206263112273167)
            ·
              refine ⟨6805582627809394668409751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4537055085206263112273167 6805582627809394668409751)
              ·
                refine ⟨10208373941714092002614627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6805582627809394668409751 10208373941714092002614627)
                ·
                  refine ⟨15312560912571138003921941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10208373941714092002614627 15312560912571138003921941)
                  ·
                    refine ⟨717776292776772093933841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15312560912571138003921941 717776292776772093933841)
                    ·
                      rfl

theorem cell23_4193593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 2, 2, 1, 1, 1, 6].length) (baseStart_4193593 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193593 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193593 prefixEnd_4193593 := by exact prefixLift 4193593
  have htrace : WordTrace (prefixWord ++ tailWord_4193593) baseStart_4193593 baseEnd_4193593 := by
    simpa [prefixWord, tailWord_4193593, baseEnd_4193593] using wordTrace_append hprefix tailTrace_4193593
  have hstable : (prefixWord ++ tailWord_4193593).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193593).length < 2 ^ (prefixWord ++ tailWord_4193593).sum := by decide
  have hdescent : baseEnd_4193593 < baseStart_4193593 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193596 : List Nat := [2, 2, 2, 2, 1, 3, 3, 1, 1, 2, 4]
def baseStart_4193596 : Nat := 118140960795 + 4193596 * 2 ^ 59
def prefixEnd_4193596 : Nat := 4983230072969 + 3 ^ 40 * 4193596 * 2
def baseEnd_4193596 : Nat := 2153330418772279770064009

theorem tailTrace_4193596 : CollatzResearch.WordTrace tailWord_4193596 prefixEnd_4193596 2153330418772279770064009 := by
  unfold tailWord_4193596
  simp only [CollatzResearch.WordTrace]
  refine ⟨76476505857662688010792321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101968674476883584014389761 76476505857662688010792321)
  ·
    refine ⟨57357379393247016008094241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76476505857662688010792321 57357379393247016008094241)
    ·
      refine ⟨43018034544935262006070681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57357379393247016008094241 43018034544935262006070681)
      ·
        refine ⟨32263525908701446504553011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43018034544935262006070681 32263525908701446504553011)
        ·
          refine ⟨48395288863052169756829517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32263525908701446504553011 48395288863052169756829517)
          ·
            refine ⟨18148233323644563658811069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48395288863052169756829517 18148233323644563658811069)
            ·
              refine ⟨6805587496366711372054151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18148233323644563658811069 6805587496366711372054151)
              ·
                refine ⟨10208381244550067058081227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6805587496366711372054151 10208381244550067058081227)
                ·
                  refine ⟨15312571866825100587121841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10208381244550067058081227 15312571866825100587121841)
                  ·
                    refine ⟨11484428900118825440341381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15312571866825100587121841 11484428900118825440341381)
                    ·
                      refine ⟨2153330418772279770064009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11484428900118825440341381 2153330418772279770064009)
                      ·
                        rfl

theorem cell23_4193596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 3, 1, 1, 2, 4].length) (baseStart_4193596 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193596 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193596 prefixEnd_4193596 := by exact prefixLift 4193596
  have htrace : WordTrace (prefixWord ++ tailWord_4193596) baseStart_4193596 baseEnd_4193596 := by
    simpa [prefixWord, tailWord_4193596, baseEnd_4193596] using wordTrace_append hprefix tailTrace_4193596
  have hstable : (prefixWord ++ tailWord_4193596).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193596).length < 2 ^ (prefixWord ++ tailWord_4193596).sum := by decide
  have hdescent : baseEnd_4193596 < baseStart_4193596 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193616 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 6, 1, 3]
def baseStart_4193616 : Nat := 118140960795 + 4193616 * 2 ^ 59
def prefixEnd_4193616 : Nat := 4983230072969 + 3 ^ 40 * 4193616 * 2
def baseEnd_4193616 : Nat := 2153340688385369691813917

theorem tailTrace_4193616 : CollatzResearch.WordTrace tailWord_4193616 prefixEnd_4193616 2153340688385369691813917 := by
  unfold tailWord_4193616
  simp only [CollatzResearch.WordTrace]
  refine ⟨76476870587626459718656351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101969160783501946291541801 76476870587626459718656351)
  ·
    refine ⟨114715305881439689577984527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76476870587626459718656351 114715305881439689577984527)
    ·
      refine ⟨172072958822159534366976791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114715305881439689577984527 172072958822159534366976791)
      ·
        refine ⟨258109438233239301550465187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172072958822159534366976791 258109438233239301550465187)
        ·
          refine ⟨387164157349858952325697781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258109438233239301550465187 387164157349858952325697781)
          ·
            refine ⟨36296639751549276780534167, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 387164157349858952325697781 36296639751549276780534167)
            ·
              refine ⟨54444959627323915170801251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36296639751549276780534167 54444959627323915170801251)
              ·
                refine ⟨81667439440985872756201877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54444959627323915170801251 81667439440985872756201877)
                ·
                  refine ⟨3828161223796212785446963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 81667439440985872756201877 3828161223796212785446963)
                  ·
                    refine ⟨5742241835694319178170445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3828161223796212785446963 5742241835694319178170445)
                    ·
                      refine ⟨2153340688385369691813917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5742241835694319178170445 2153340688385369691813917)
                      ·
                        rfl

theorem cell23_4193616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 6, 1, 3].length) (baseStart_4193616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193616 prefixEnd_4193616 := by exact prefixLift 4193616
  have htrace : WordTrace (prefixWord ++ tailWord_4193616) baseStart_4193616 baseEnd_4193616 := by
    simpa [prefixWord, tailWord_4193616, baseEnd_4193616] using wordTrace_append hprefix tailTrace_4193616
  have hstable : (prefixWord ++ tailWord_4193616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193616).length < 2 ^ (prefixWord ++ tailWord_4193616).sum := by decide
  have hdescent : baseEnd_4193616 < baseStart_4193616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193634 : List Nat := [3, 3, 2, 1, 1, 1, 5, 2, 1, 2, 2]
def baseStart_4193634 : Nat := 118140960795 + 4193634 * 2 ^ 59
def prefixEnd_4193634 : Nat := 4983230072969 + 3 ^ 40 * 4193634 * 2
def baseEnd_4193634 : Nat := 2153349931037150621388835

theorem tailTrace_4193634 : CollatzResearch.WordTrace tailWord_4193634 prefixEnd_4193634 2153349931037150621388835 := by
  unfold tailWord_4193634
  simp only [CollatzResearch.WordTrace]
  refine ⟨38238599422296927127866989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101969598459458472340978637 38238599422296927127866989)
  ·
    refine ⟨14339474783361347672950121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38238599422296927127866989 14339474783361347672950121)
    ·
      refine ⟨10754606087521010754712591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14339474783361347672950121 10754606087521010754712591)
      ·
        refine ⟨16131909131281516132068887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10754606087521010754712591 16131909131281516132068887)
        ·
          refine ⟨24197863696922274198103331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16131909131281516132068887 24197863696922274198103331)
          ·
            refine ⟨36296795545383411297154997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24197863696922274198103331 36296795545383411297154997)
            ·
              refine ⟨3402824582379694809108281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36296795545383411297154997 3402824582379694809108281)
              ·
                refine ⟨2552118436784771106831211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3402824582379694809108281 2552118436784771106831211)
                ·
                  refine ⟨3828177655177156660246817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2552118436784771106831211 3828177655177156660246817)
                  ·
                    refine ⟨2871133241382867495185113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3828177655177156660246817 2871133241382867495185113)
                    ·
                      refine ⟨2153349931037150621388835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2871133241382867495185113 2153349931037150621388835)
                      ·
                        rfl

theorem cell23_4193634_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 5, 2, 1, 2, 2].length) (baseStart_4193634 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193634 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193634 prefixEnd_4193634 := by exact prefixLift 4193634
  have htrace : WordTrace (prefixWord ++ tailWord_4193634) baseStart_4193634 baseEnd_4193634 := by
    simpa [prefixWord, tailWord_4193634, baseEnd_4193634] using wordTrace_append hprefix tailTrace_4193634
  have hstable : (prefixWord ++ tailWord_4193634).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193634).length < 2 ^ (prefixWord ++ tailWord_4193634).sum := by decide
  have hdescent : baseEnd_4193634 < baseStart_4193634 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193634) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193649 : List Nat := [1, 2, 2, 2, 1, 2, 2, 3, 2, 6]
def baseStart_4193649 : Nat := 118140960795 + 4193649 * 2 ^ 59
def prefixEnd_4193649 : Nat := 4983230072969 + 3 ^ 40 * 4193649 * 2
def baseEnd_4193649 : Nat := 717785877748989354233755

theorem tailTrace_4193649 : CollatzResearch.WordTrace tailWord_4193649 prefixEnd_4193649 717785877748989354233755 := by
  unfold tailWord_4193649
  simp only [CollatzResearch.WordTrace]
  refine ⟨152954944784133366073264001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101969963189422244048842667 152954944784133366073264001)
  ·
    refine ⟨114716208588100024554948001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152954944784133366073264001 114716208588100024554948001)
    ·
      refine ⟨86037156441075018416211001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114716208588100024554948001 86037156441075018416211001)
      ·
        refine ⟨64527867330806263812158251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86037156441075018416211001 64527867330806263812158251)
        ·
          refine ⟨96791800996209395718237377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64527867330806263812158251 96791800996209395718237377)
          ·
            refine ⟨72593850747157046788678033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96791800996209395718237377 72593850747157046788678033)
            ·
              refine ⟨54445388060367785091508525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72593850747157046788678033 54445388060367785091508525)
              ·
                refine ⟨20417020522637919409315697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54445388060367785091508525 20417020522637919409315697)
                ·
                  refine ⟨15312765391978439556986773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20417020522637919409315697 15312765391978439556986773)
                  ·
                    refine ⟨717785877748989354233755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15312765391978439556986773 717785877748989354233755)
                    ·
                      rfl

theorem cell23_4193649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 3, 2, 6].length) (baseStart_4193649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193649 prefixEnd_4193649 := by exact prefixLift 4193649
  have htrace : WordTrace (prefixWord ++ tailWord_4193649) baseStart_4193649 baseEnd_4193649 := by
    simpa [prefixWord, tailWord_4193649, baseEnd_4193649] using wordTrace_append hprefix tailTrace_4193649
  have hstable : (prefixWord ++ tailWord_4193649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193649).length < 2 ^ (prefixWord ++ tailWord_4193649).sum := by decide
  have hdescent : baseEnd_4193649 < baseStart_4193649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193656 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 7, 4, 2]
def baseStart_4193656 : Nat := 118140960795 + 4193656 * 2 ^ 59
def prefixEnd_4193656 : Nat := 4983230072969 + 3 ^ 40 * 4193656 * 2
def baseEnd_4193656 : Nat := 2153361227611549535313733

theorem tailTrace_4193656 : CollatzResearch.WordTrace tailWord_4193656 prefixEnd_4193656 2153361227611549535313733 := by
  unfold tailWord_4193656
  simp only [CollatzResearch.WordTrace]
  refine ⟨76477600047554003134384411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101970133396738670845845881 76477600047554003134384411)
  ·
    refine ⟨114716400071331004701576617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76477600047554003134384411 114716400071331004701576617)
    ·
      refine ⟨86037300053498253526182463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114716400071331004701576617 86037300053498253526182463)
      ·
        refine ⟨129055950080247380289273695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86037300053498253526182463 129055950080247380289273695)
        ·
          refine ⟨193583925120371070433910543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129055950080247380289273695 193583925120371070433910543)
          ·
            refine ⟨290375887680556605650865815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193583925120371070433910543 290375887680556605650865815)
            ·
              refine ⟨435563831520834908476298723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290375887680556605650865815 435563831520834908476298723)
              ·
                refine ⟨653345747281252362714448085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 435563831520834908476298723 653345747281252362714448085)
                ·
                  refine ⟨15312790951904352251119877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 653345747281252362714448085 15312790951904352251119877)
                  ·
                    refine ⟨2871148303482066047084977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15312790951904352251119877 2871148303482066047084977)
                    ·
                      refine ⟨2153361227611549535313733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2871148303482066047084977 2153361227611549535313733)
                      ·
                        rfl

theorem cell23_4193656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 7, 4, 2].length) (baseStart_4193656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193656 prefixEnd_4193656 := by exact prefixLift 4193656
  have htrace : WordTrace (prefixWord ++ tailWord_4193656) baseStart_4193656 baseEnd_4193656 := by
    simpa [prefixWord, tailWord_4193656, baseEnd_4193656] using wordTrace_append hprefix tailTrace_4193656
  have hstable : (prefixWord ++ tailWord_4193656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193656).length < 2 ^ (prefixWord ++ tailWord_4193656).sum := by decide
  have hdescent : baseEnd_4193656 < baseStart_4193656 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193659 : List Nat := [1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 5]
def baseStart_4193659 : Nat := 118140960795 + 4193659 * 2 ^ 59
def prefixEnd_4193659 : Nat := 4983230072969 + 3 ^ 40 * 4193659 * 2
def baseEnd_4193659 : Nat := 2153362768053513023576219

theorem tailTrace_4193659 : CollatzResearch.WordTrace tailWord_4193659 prefixEnd_4193659 2153362768053513023576219 := by
  unfold tailWord_4193659
  simp only [CollatzResearch.WordTrace]
  refine ⟨152955309514097137781128031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101970206342731425187418687 152955309514097137781128031)
  ·
    refine ⟨229432964271145706671692047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152955309514097137781128031 229432964271145706671692047)
    ·
      refine ⟨344149446406718560007538071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229432964271145706671692047 344149446406718560007538071)
      ·
        refine ⟨516224169610077840011307107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344149446406718560007538071 516224169610077840011307107)
        ·
          refine ⟨774336254415116760016960661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516224169610077840011307107 774336254415116760016960661)
          ·
            refine ⟨36297011925708598125795031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 774336254415116760016960661 36297011925708598125795031)
            ·
              refine ⟨54445517888562897188692547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36297011925708598125795031 54445517888562897188692547)
              ·
                refine ⟨81668276832844345783038821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54445517888562897188692547 81668276832844345783038821)
                ·
                  refine ⟨15312801906158314834319779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81668276832844345783038821 15312801906158314834319779)
                  ·
                    refine ⟨22969202859237472251479669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15312801906158314834319779 22969202859237472251479669)
                    ·
                      refine ⟨2153362768053513023576219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22969202859237472251479669 2153362768053513023576219)
                      ·
                        rfl

theorem cell23_4193659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 1, 1, 4, 1, 5].length) (baseStart_4193659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193659 prefixEnd_4193659 := by exact prefixLift 4193659
  have htrace : WordTrace (prefixWord ++ tailWord_4193659) baseStart_4193659 baseEnd_4193659 := by
    simpa [prefixWord, tailWord_4193659, baseEnd_4193659] using wordTrace_append hprefix tailTrace_4193659
  have hstable : (prefixWord ++ tailWord_4193659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193659).length < 2 ^ (prefixWord ++ tailWord_4193659).sum := by decide
  have hdescent : baseEnd_4193659 < baseStart_4193659 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193823 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 3, 5, 2]
def baseStart_4193823 : Nat := 118140960795 + 4193823 * 2 ^ 59
def prefixEnd_4193823 : Nat := 4983230072969 + 3 ^ 40 * 4193823 * 2
def baseEnd_4193823 : Nat := 2153446978880850381925465

theorem tailTrace_4193823 : CollatzResearch.WordTrace tailWord_4193823 prefixEnd_4193823 2153446978880850381925465 := by
  unfold tailWord_4193823
  simp only [CollatzResearch.WordTrace]
  refine ⟨152961291085502993790098123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101974194057001995860065415 152961291085502993790098123)
  ·
    refine ⟨229441936628254490685147185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152961291085502993790098123 229441936628254490685147185)
    ·
      refine ⟨172081452471190868013860389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229441936628254490685147185 172081452471190868013860389)
      ·
        refine ⟨32265272338348287752598823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172081452471190868013860389 32265272338348287752598823)
        ·
          refine ⟨48397908507522431628898235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32265272338348287752598823 48397908507522431628898235)
          ·
            refine ⟨72596862761283647443347353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48397908507522431628898235 72596862761283647443347353)
            ·
              refine ⟨54447647070962735582510515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72596862761283647443347353 54447647070962735582510515)
              ·
                refine ⟨81671470606444103373765773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54447647070962735582510515 81671470606444103373765773)
                ·
                  refine ⟨30626801477416538765162165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81671470606444103373765773 30626801477416538765162165)
                  ·
                    refine ⟨2871262638507800509233953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30626801477416538765162165 2871262638507800509233953)
                    ·
                      refine ⟨2153446978880850381925465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2871262638507800509233953 2153446978880850381925465)
                      ·
                        rfl

theorem cell23_4193823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 3, 5, 2].length) (baseStart_4193823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193823 prefixEnd_4193823 := by exact prefixLift 4193823
  have htrace : WordTrace (prefixWord ++ tailWord_4193823) baseStart_4193823 baseEnd_4193823 := by
    simpa [prefixWord, tailWord_4193823, baseEnd_4193823] using wordTrace_append hprefix tailTrace_4193823
  have hstable : (prefixWord ++ tailWord_4193823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193823).length < 2 ^ (prefixWord ++ tailWord_4193823).sum := by decide
  have hdescent : baseEnd_4193823 < baseStart_4193823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193850 : List Nat := [3, 1, 1, 1, 3, 2, 5, 1, 1, 5]
def baseStart_4193850 : Nat := 118140960795 + 4193850 * 2 ^ 59
def prefixEnd_4193850 : Nat := 4983230072969 + 3 ^ 40 * 4193850 * 2
def baseEnd_4193850 : Nat := 717820280952840592095947

theorem tailTrace_4193850 : CollatzResearch.WordTrace tailWord_4193850 prefixEnd_4193850 717820280952840592095947 := by
  unfold tailWord_4193850
  simp only [CollatzResearch.WordTrace]
  refine ⟨38240568964101294350332751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101974850570936784934220669 38240568964101294350332751)
  ·
    refine ⟨57360853446151941525499127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38240568964101294350332751 57360853446151941525499127)
    ·
      refine ⟨86041280169227912288248691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57360853446151941525499127 86041280169227912288248691)
      ·
        refine ⟨129061920253841868432373037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86041280169227912288248691 129061920253841868432373037)
        ·
          refine ⟨48398220095190700662139889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129061920253841868432373037 48398220095190700662139889)
          ·
            refine ⟨36298665071393025496604917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48398220095190700662139889 36298665071393025496604917)
            ·
              refine ⟨3402999850443096140306711, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36298665071393025496604917 3402999850443096140306711)
              ·
                refine ⟨5104499775664644210460067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3402999850443096140306711 5104499775664644210460067)
                ·
                  refine ⟨7656749663496966315690101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5104499775664644210460067 7656749663496966315690101)
                  ·
                    refine ⟨717820280952840592095947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7656749663496966315690101 717820280952840592095947)
                    ·
                      rfl

theorem cell23_4193850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 1, 5].length) (baseStart_4193850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193850 prefixEnd_4193850 := by exact prefixLift 4193850
  have htrace : WordTrace (prefixWord ++ tailWord_4193850) baseStart_4193850 baseEnd_4193850 := by
    simpa [prefixWord, tailWord_4193850, baseEnd_4193850] using wordTrace_append hprefix tailTrace_4193850
  have hstable : (prefixWord ++ tailWord_4193850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193850).length < 2 ^ (prefixWord ++ tailWord_4193850).sum := by decide
  have hdescent : baseEnd_4193850 < baseStart_4193850 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193873 : List Nat := [1, 2, 2, 1, 3, 2, 1, 1, 5, 2, 3]
def baseStart_4193873 : Nat := 118140960795 + 4193873 * 2 ^ 59
def prefixEnd_4193873 : Nat := 4983230072969 + 3 ^ 40 * 4193873 * 2
def baseEnd_4193873 : Nat := 2153472652913575186300235

theorem tailTrace_4193873 : CollatzResearch.WordTrace tailWord_4193873 prefixEnd_4193873 2153472652913575186300235 := by
  unfold tailWord_4193873
  simp only [CollatzResearch.WordTrace]
  refine ⟨152963114735321852329418273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101975409823547901552945515 152963114735321852329418273)
  ·
    refine ⟨114722336051491389247063705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152963114735321852329418273 114722336051491389247063705)
    ·
      refine ⟨86041752038618541935297779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114722336051491389247063705 86041752038618541935297779)
      ·
        refine ⟨129062628057927812902946669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86041752038618541935297779 129062628057927812902946669)
        ·
          refine ⟨48398485521722929838605001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129062628057927812902946669 48398485521722929838605001)
          ·
            refine ⟨36298864141292197378953751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48398485521722929838605001 36298864141292197378953751)
            ·
              refine ⟨54448296211938296068430627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36298864141292197378953751 54448296211938296068430627)
              ·
                refine ⟨81672444317907444102645941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54448296211938296068430627 81672444317907444102645941)
                ·
                  refine ⟨7656791654803822884623057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81672444317907444102645941 7656791654803822884623057)
                  ·
                    refine ⟨5742593741102867163467293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7656791654803822884623057 5742593741102867163467293)
                    ·
                      refine ⟨2153472652913575186300235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5742593741102867163467293 2153472652913575186300235)
                      ·
                        rfl

theorem cell23_4193873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 1, 1, 5, 2, 3].length) (baseStart_4193873 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193873 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193873 prefixEnd_4193873 := by exact prefixLift 4193873
  have htrace : WordTrace (prefixWord ++ tailWord_4193873) baseStart_4193873 baseEnd_4193873 := by
    simpa [prefixWord, tailWord_4193873, baseEnd_4193873] using wordTrace_append hprefix tailTrace_4193873
  have hstable : (prefixWord ++ tailWord_4193873).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193873).length < 2 ^ (prefixWord ++ tailWord_4193873).sum := by decide
  have hdescent : baseEnd_4193873 < baseStart_4193873 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193904 : List Nat := [2, 1, 1, 1, 6, 1, 1, 5, 1, 2, 2]
def baseStart_4193904 : Nat := 118140960795 + 4193904 * 2 ^ 59
def prefixEnd_4193904 : Nat := 4983230072969 + 3 ^ 40 * 4193904 * 2
def baseEnd_4193904 : Nat := 2153488570813864565012593

theorem tailTrace_4193904 : CollatzResearch.WordTrace tailWord_4193904 prefixEnd_4193904 2153488570813864565012593 := by
  unfold tailWord_4193904
  simp only [CollatzResearch.WordTrace]
  refine ⟨76482122699104772311898383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101976163598806363082531177 76482122699104772311898383)
  ·
    refine ⟨114723184048657158467847575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76482122699104772311898383 114723184048657158467847575)
    ·
      refine ⟨172084776072985737701771363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114723184048657158467847575 172084776072985737701771363)
      ·
        refine ⟨258127164109478606552657045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172084776072985737701771363 258127164109478606552657045)
        ·
          refine ⟨12099710817631809682155799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 258127164109478606552657045 12099710817631809682155799)
          ·
            refine ⟨18149566226447714523233699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12099710817631809682155799 18149566226447714523233699)
            ·
              refine ⟨27224349339671571784850549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18149566226447714523233699 27224349339671571784850549)
              ·
                refine ⟨2552282750594209854829739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27224349339671571784850549 2552282750594209854829739)
                ·
                  refine ⟨3828424125891314782244609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2552282750594209854829739 3828424125891314782244609)
                  ·
                    refine ⟨2871318094418486086683457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3828424125891314782244609 2871318094418486086683457)
                    ·
                      refine ⟨2153488570813864565012593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2871318094418486086683457 2153488570813864565012593)
                      ·
                        rfl

theorem cell23_4193904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 1, 5, 1, 2, 2].length) (baseStart_4193904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193904 prefixEnd_4193904 := by exact prefixLift 4193904
  have htrace : WordTrace (prefixWord ++ tailWord_4193904) baseStart_4193904 baseEnd_4193904 := by
    simpa [prefixWord, tailWord_4193904, baseEnd_4193904] using wordTrace_append hprefix tailTrace_4193904
  have hstable : (prefixWord ++ tailWord_4193904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193904).length < 2 ^ (prefixWord ++ tailWord_4193904).sum := by decide
  have hdescent : baseEnd_4193904 < baseStart_4193904 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193920 : List Nat := [2, 1, 1, 2, 1, 4, 3, 1, 4, 1, 3]
def baseStart_4193920 : Nat := 118140960795 + 4193920 * 2 ^ 59
def prefixEnd_4193920 : Nat := 4983230072969 + 3 ^ 40 * 4193920 * 2
def baseEnd_4193920 : Nat := 2153496786504336502412519

theorem tailTrace_4193920 : CollatzResearch.WordTrace tailWord_4193920 prefixEnd_4193920 2153496786504336502412519 := by
  unfold tailWord_4193920
  simp only [CollatzResearch.WordTrace]
  refine ⟨76482414483075789678189607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101976552644101052904252809 76482414483075789678189607)
  ·
    refine ⟨114723621724613684517284411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76482414483075789678189607 114723621724613684517284411)
    ·
      refine ⟨172085432586920526775926617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114723621724613684517284411 172085432586920526775926617)
      ·
        refine ⟨129064074440190395081944963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172085432586920526775926617 129064074440190395081944963)
        ·
          refine ⟨193596111660285592622917445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129064074440190395081944963 193596111660285592622917445)
          ·
            refine ⟨36299270936303548616797021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 193596111660285592622917445 36299270936303548616797021)
            ·
              refine ⟨13612226601113830731298883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36299270936303548616797021 13612226601113830731298883)
              ·
                refine ⟨20418339901670746096948325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13612226601113830731298883 20418339901670746096948325)
                ·
                  refine ⟨3828438731563264893177811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20418339901670746096948325 3828438731563264893177811)
                  ·
                    refine ⟨5742658097344897339766717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3828438731563264893177811 5742658097344897339766717)
                    ·
                      refine ⟨2153496786504336502412519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5742658097344897339766717 2153496786504336502412519)
                      ·
                        rfl

theorem cell23_4193920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 4, 1, 3].length) (baseStart_4193920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193920 prefixEnd_4193920 := by exact prefixLift 4193920
  have htrace : WordTrace (prefixWord ++ tailWord_4193920) baseStart_4193920 baseEnd_4193920 := by
    simpa [prefixWord, tailWord_4193920, baseEnd_4193920] using wordTrace_append hprefix tailTrace_4193920
  have hstable : (prefixWord ++ tailWord_4193920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193920).length < 2 ^ (prefixWord ++ tailWord_4193920).sum := by decide
  have hdescent : baseEnd_4193920 < baseStart_4193920 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193950 : List Nat := [4, 3, 1, 1, 1, 2, 1, 1, 2, 2, 5]
def baseStart_4193950 : Nat := 118140960795 + 4193950 * 2 ^ 59
def prefixEnd_4193950 : Nat := 4983230072969 + 3 ^ 40 * 4193950 * 2
def baseEnd_4193950 : Nat := 2153512190923971385037381

theorem tailTrace_4193950 : CollatzResearch.WordTrace tailWord_4193950 prefixEnd_4193950 2153512190923971385037381 := by
  unfold tailWord_4193950
  simp only [CollatzResearch.WordTrace]
  refine ⟨19120740394505361809996413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101977282104028596319980869 19120740394505361809996413)
  ·
    refine ⟨7170277647939510678748655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 19120740394505361809996413 7170277647939510678748655)
    ·
      refine ⟨10755416471909266018122983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7170277647939510678748655 10755416471909266018122983)
      ·
        refine ⟨16133124707863899027184475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10755416471909266018122983 16133124707863899027184475)
        ·
          refine ⟨24199687061795848540776713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16133124707863899027184475 24199687061795848540776713)
          ·
            refine ⟨18149765296346886405582535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24199687061795848540776713 18149765296346886405582535)
            ·
              refine ⟨27224647944520329608373803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18149765296346886405582535 27224647944520329608373803)
              ·
                refine ⟨40836971916780494412560705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27224647944520329608373803 40836971916780494412560705)
                ·
                  refine ⟨30627728937585370809420529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40836971916780494412560705 30627728937585370809420529)
                  ·
                    refine ⟨22970796703189028107065397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30627728937585370809420529 22970796703189028107065397)
                    ·
                      refine ⟨2153512190923971385037381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22970796703189028107065397 2153512190923971385037381)
                      ·
                        rfl

theorem cell23_4193950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 1, 2, 2, 5].length) (baseStart_4193950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193950 prefixEnd_4193950 := by exact prefixLift 4193950
  have htrace : WordTrace (prefixWord ++ tailWord_4193950) baseStart_4193950 baseEnd_4193950 := by
    simpa [prefixWord, tailWord_4193950, baseEnd_4193950] using wordTrace_append hprefix tailTrace_4193950
  have hstable : (prefixWord ++ tailWord_4193950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193950).length < 2 ^ (prefixWord ++ tailWord_4193950).sum := by decide
  have hdescent : baseEnd_4193950 < baseStart_4193950 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193977 : List Nat := [1, 2, 1, 4, 1, 1, 4, 1, 4, 2, 2]
def baseStart_4193977 : Nat := 118140960795 + 4193977 * 2 ^ 59
def prefixEnd_4193977 : Nat := 4983230072969 + 3 ^ 40 * 4193977 * 2
def baseEnd_4193977 : Nat := 2153526054901642779399757

theorem tailTrace_4193977 : CollatzResearch.WordTrace tailWord_4193977 prefixEnd_4193977 2153526054901642779399757 := by
  unfold tailWord_4193977
  simp only [CollatzResearch.WordTrace]
  refine ⟨152966907926945078091204185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101977938617963385394136123 152966907926945078091204185)
  ·
    refine ⟨114725180945208808568403139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152966907926945078091204185 114725180945208808568403139)
    ·
      refine ⟨172087771417813212852604709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114725180945208808568403139 172087771417813212852604709)
      ·
        refine ⟨32266457140839977409863383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172087771417813212852604709 32266457140839977409863383)
        ·
          refine ⟨48399685711259966114795075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32266457140839977409863383 48399685711259966114795075)
          ·
            refine ⟨72599528566889949172192613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48399685711259966114795075 72599528566889949172192613)
            ·
              refine ⟨13612411606291865469786115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72599528566889949172192613 13612411606291865469786115)
              ·
                refine ⟨20418617409437798204679173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13612411606291865469786115 20418617409437798204679173)
                ·
                  refine ⟨3828490764269587163377345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20418617409437798204679173 3828490764269587163377345)
                  ·
                    refine ⟨2871368073202190372533009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3828490764269587163377345 2871368073202190372533009)
                    ·
                      refine ⟨2153526054901642779399757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2871368073202190372533009 2153526054901642779399757)
                      ·
                        rfl

theorem cell23_4193977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 1, 4, 2, 2].length) (baseStart_4193977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193977 prefixEnd_4193977 := by exact prefixLift 4193977
  have htrace : WordTrace (prefixWord ++ tailWord_4193977) baseStart_4193977 baseEnd_4193977 := by
    simpa [prefixWord, tailWord_4193977, baseEnd_4193977] using wordTrace_append hprefix tailTrace_4193977
  have hstable : (prefixWord ++ tailWord_4193977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193977).length < 2 ^ (prefixWord ++ tailWord_4193977).sum := by decide
  have hdescent : baseEnd_4193977 < baseStart_4193977 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4193997 : List Nat := [1, 6, 2, 1, 1, 1, 1, 2, 2, 1, 5]
def baseStart_4193997 : Nat := 118140960795 + 4193997 * 2 ^ 59
def prefixEnd_4193997 : Nat := 4983230072969 + 3 ^ 40 * 4193997 * 2
def baseEnd_4193997 : Nat := 2153536324514732701149665

theorem tailTrace_4193997 : CollatzResearch.WordTrace tailWord_4193997 prefixEnd_4193997 2153536324514732701149665 := by
  unfold tailWord_4193997
  simp only [CollatzResearch.WordTrace]
  refine ⟨152967637386872621506932245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101978424924581747671288163 152967637386872621506932245)
  ·
    refine ⟨7170358002509654133137449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152967637386872621506932245 7170358002509654133137449)
    ·
      refine ⟨5377768501882240599853087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7170358002509654133137449 5377768501882240599853087)
      ·
        refine ⟨8066652752823360899779631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5377768501882240599853087 8066652752823360899779631)
        ·
          refine ⟨12099979129235041349669447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8066652752823360899779631 12099979129235041349669447)
          ·
            refine ⟨18149968693852562024504171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12099979129235041349669447 18149968693852562024504171)
            ·
              refine ⟨27224953040778843036756257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18149968693852562024504171 27224953040778843036756257)
              ·
                refine ⟨20418714780584132277567193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27224953040778843036756257 20418714780584132277567193)
                ·
                  refine ⟨15314036085438099208175395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20418714780584132277567193 15314036085438099208175395)
                  ·
                    refine ⟨22971054128157148812263093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15314036085438099208175395 22971054128157148812263093)
                    ·
                      refine ⟨2153536324514732701149665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22971054128157148812263093 2153536324514732701149665)
                      ·
                        rfl

theorem cell23_4193997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 1, 1, 2, 2, 1, 5].length) (baseStart_4193997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4193997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4193997 prefixEnd_4193997 := by exact prefixLift 4193997
  have htrace : WordTrace (prefixWord ++ tailWord_4193997) baseStart_4193997 baseEnd_4193997 := by
    simpa [prefixWord, tailWord_4193997, baseEnd_4193997] using wordTrace_append hprefix tailTrace_4193997
  have hstable : (prefixWord ++ tailWord_4193997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4193997).length < 2 ^ (prefixWord ++ tailWord_4193997).sum := by decide
  have hdescent : baseEnd_4193997 < baseStart_4193997 := by decide
  rcases family_descends (prefixWord ++ tailWord_4193997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194030 : List Nat := [4, 1, 2, 1, 1, 2, 1, 4, 2, 5]
def baseStart_4194030 : Nat := 118140960795 + 4194030 * 2 ^ 59
def prefixEnd_4194030 : Nat := 4983230072969 + 3 ^ 40 * 4194030 * 2
def baseEnd_4194030 : Nat := 717851089792110357345671

theorem tailTrace_4194030 : CollatzResearch.WordTrace tailWord_4194030 prefixEnd_4194030 717851089792110357345671 := by
  unfold tailWord_4194030
  simp only [CollatzResearch.WordTrace]
  refine ⟨19121105124469133517860443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 101979227330502045428589029 19121105124469133517860443)
  ·
    refine ⟨28681657686703700276790665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19121105124469133517860443 28681657686703700276790665)
    ·
      refine ⟨21511243265027775207592999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28681657686703700276790665 21511243265027775207592999)
      ·
        refine ⟨32266864897541662811389499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21511243265027775207592999 32266864897541662811389499)
        ·
          refine ⟨48400297346312494217084249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32266864897541662811389499 48400297346312494217084249)
          ·
            refine ⟨36300223009734370662813187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48400297346312494217084249 36300223009734370662813187)
            ·
              refine ⟨54450334514601555994219781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36300223009734370662813187 54450334514601555994219781)
              ·
                refine ⟨10209437721487791748916209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54450334514601555994219781 10209437721487791748916209)
                ·
                  refine ⟨7657078291115843811687157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10209437721487791748916209 7657078291115843811687157)
                  ·
                    refine ⟨717851089792110357345671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7657078291115843811687157 717851089792110357345671)
                    ·
                      rfl

theorem cell23_4194030_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_4194030 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194030 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194030 prefixEnd_4194030 := by exact prefixLift 4194030
  have htrace : WordTrace (prefixWord ++ tailWord_4194030) baseStart_4194030 baseEnd_4194030 := by
    simpa [prefixWord, tailWord_4194030, baseEnd_4194030] using wordTrace_append hprefix tailTrace_4194030
  have hstable : (prefixWord ++ tailWord_4194030).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194030).length < 2 ^ (prefixWord ++ tailWord_4194030).sum := by decide
  have hdescent : baseEnd_4194030 < baseStart_4194030 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194030) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194060 : List Nat := [2, 2, 1, 2, 2, 1, 3, 1, 5, 4]
def baseStart_4194060 : Nat := 118140960795 + 4194060 * 2 ^ 59
def prefixEnd_4194060 : Nat := 4983230072969 + 3 ^ 40 * 4194060 * 2
def baseEnd_4194060 : Nat := 717856224598655318220625

theorem tailTrace_4194060 : CollatzResearch.WordTrace tailWord_4194060 prefixEnd_4194060 717856224598655318220625 := by
  unfold tailWord_4194060
  simp only [CollatzResearch.WordTrace]
  refine ⟨76484967592822191633237817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101979956790429588844317089 76484967592822191633237817)
  ·
    refine ⟨57363725694616643724928363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76484967592822191633237817 57363725694616643724928363)
    ·
      refine ⟨86045588541924965587392545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57363725694616643724928363 86045588541924965587392545)
      ·
        refine ⟨64534191406443724190544409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86045588541924965587392545 64534191406443724190544409)
        ·
          refine ⟨48400643554832793142908307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64534191406443724190544409 48400643554832793142908307)
          ·
            refine ⟨72600965332249189714362461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48400643554832793142908307 72600965332249189714362461)
            ·
              refine ⟨27225361999593446142885923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72600965332249189714362461 27225361999593446142885923)
              ·
                refine ⟨40838042999390169214328885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27225361999593446142885923 40838042999390169214328885)
                ·
                  refine ⟨3828566531192828363843333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40838042999390169214328885 3828566531192828363843333)
                  ·
                    refine ⟨717856224598655318220625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3828566531192828363843333 717856224598655318220625)
                    ·
                      rfl

theorem cell23_4194060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 5, 4].length) (baseStart_4194060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194060 prefixEnd_4194060 := by exact prefixLift 4194060
  have htrace : WordTrace (prefixWord ++ tailWord_4194060) baseStart_4194060 baseEnd_4194060 := by
    simpa [prefixWord, tailWord_4194060, baseEnd_4194060] using wordTrace_append hprefix tailTrace_4194060
  have hstable : (prefixWord ++ tailWord_4194060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194060).length < 2 ^ (prefixWord ++ tailWord_4194060).sum := by decide
  have hdescent : baseEnd_4194060 < baseStart_4194060 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194063 : List Nat := [1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 4]
def baseStart_4194063 : Nat := 118140960795 + 4194063 * 2 ^ 59
def prefixEnd_4194063 : Nat := 4983230072969 + 3 ^ 40 * 4194063 * 2
def baseEnd_4194063 : Nat := 2153570214237929442924361

theorem tailTrace_4194063 : CollatzResearch.WordTrace tailWord_4194063 prefixEnd_4194063 2153570214237929442924361 := by
  unfold tailWord_4194063
  simp only [CollatzResearch.WordTrace]
  refine ⟨152970044604633514778834843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101980029736422343185889895 152970044604633514778834843)
  ·
    refine ⟨229455066906950272168252265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152970044604633514778834843 229455066906950272168252265)
    ·
      refine ⟨172091300180212704126189199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229455066906950272168252265 172091300180212704126189199)
      ·
        refine ⟨258136950270319056189283799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172091300180212704126189199 258136950270319056189283799)
        ·
          refine ⟨387205425405478584283925699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258136950270319056189283799 387205425405478584283925699)
          ·
            refine ⟨580808138108217876425888549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387205425405478584283925699 580808138108217876425888549)
            ·
              refine ⟨108901525895290851829854103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 580808138108217876425888549 108901525895290851829854103)
              ·
                refine ⟨163352288842936277744781155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108901525895290851829854103 163352288842936277744781155)
                ·
                  refine ⟨245028433264404416617171733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 163352288842936277744781155 245028433264404416617171733)
                  ·
                    refine ⟨11485707809268957028929925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 245028433264404416617171733 11485707809268957028929925)
                    ·
                      refine ⟨2153570214237929442924361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11485707809268957028929925 2153570214237929442924361)
                      ·
                        rfl

theorem cell23_4194063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 4].length) (baseStart_4194063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194063 prefixEnd_4194063 := by exact prefixLift 4194063
  have htrace : WordTrace (prefixWord ++ tailWord_4194063) baseStart_4194063 baseEnd_4194063 := by
    simpa [prefixWord, tailWord_4194063, baseEnd_4194063] using wordTrace_append hprefix tailTrace_4194063
  have hstable : (prefixWord ++ tailWord_4194063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194063).length < 2 ^ (prefixWord ++ tailWord_4194063).sum := by decide
  have hdescent : baseEnd_4194063 < baseStart_4194063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194068 : List Nat := [2, 4, 4, 1, 1, 1, 2, 3, 5]
def baseStart_4194068 : Nat := 118140960795 + 4194068 * 2 ^ 59
def prefixEnd_4194068 : Nat := 4983230072969 + 3 ^ 40 * 4194068 * 2
def baseEnd_4194068 : Nat := 239285864626800213706871

theorem tailTrace_4194068 : CollatzResearch.WordTrace tailWord_4194068 prefixEnd_4194068 239285864626800213706871 := by
  unfold tailWord_4194068
  simp only [CollatzResearch.WordTrace]
  refine ⟨76485113484807700316383429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101980151313076933755177905 76485113484807700316383429)
  ·
    refine ⟨14340958778401443809321893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76485113484807700316383429 14340958778401443809321893)
    ·
      refine ⟨2688929770950270714247855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 14340958778401443809321893 2688929770950270714247855)
      ·
        refine ⟨4033394656425406071371783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2688929770950270714247855 4033394656425406071371783)
        ·
          refine ⟨6050091984638109107057675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4033394656425406071371783 6050091984638109107057675)
          ·
            refine ⟨9075137976957163660586513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6050091984638109107057675 9075137976957163660586513)
            ·
              refine ⟨6806353482717872745439885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9075137976957163660586513 6806353482717872745439885)
              ·
                refine ⟨2552382556019202279539957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6806353482717872745439885 2552382556019202279539957)
                ·
                  refine ⟨239285864626800213706871, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2552382556019202279539957 239285864626800213706871)
                  ·
                    rfl

theorem cell23_4194068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_4194068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194068 prefixEnd_4194068 := by exact prefixLift 4194068
  have htrace : WordTrace (prefixWord ++ tailWord_4194068) baseStart_4194068 baseEnd_4194068 := by
    simpa [prefixWord, tailWord_4194068, baseEnd_4194068] using wordTrace_append hprefix tailTrace_4194068
  have hstable : (prefixWord ++ tailWord_4194068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194068).length < 2 ^ (prefixWord ++ tailWord_4194068).sum := by decide
  have hdescent : baseEnd_4194068 < baseStart_4194068 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194103 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 2, 9]
def baseStart_4194103 : Nat := 118140960795 + 4194103 * 2 ^ 59
def prefixEnd_4194103 : Nat := 4983230072969 + 3 ^ 40 * 4194103 * 2
def baseEnd_4194103 : Nat := 717863584488036428808059

theorem tailTrace_4194103 : CollatzResearch.WordTrace tailWord_4194103 prefixEnd_4194103 717863584488036428808059 := by
  unfold tailWord_4194103
  simp only [CollatzResearch.WordTrace]
  refine ⟨152971503524488601610290963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101981002349659067740193975 152971503524488601610290963)
  ·
    refine ⟨229457255286732902415436445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 152971503524488601610290963 229457255286732902415436445)
    ·
      refine ⟨86046470732524838405788667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229457255286732902415436445 86046470732524838405788667)
      ·
        refine ⟨129069706098787257608683001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86046470732524838405788667 129069706098787257608683001)
        ·
          refine ⟨96802279574090443206512251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129069706098787257608683001 96802279574090443206512251)
          ·
            refine ⟨145203419361135664809768377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96802279574090443206512251 145203419361135664809768377)
            ·
              refine ⟨108902564520851748607326283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 145203419361135664809768377 108902564520851748607326283)
              ·
                refine ⟨163353846781277622910989425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108902564520851748607326283 163353846781277622910989425)
                ·
                  refine ⟨122515385085958217183242069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163353846781277622910989425 122515385085958217183242069)
                  ·
                    refine ⟨717863584488036428808059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 122515385085958217183242069 717863584488036428808059)
                    ·
                      rfl

theorem cell23_4194103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 2, 9].length) (baseStart_4194103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194103 prefixEnd_4194103 := by exact prefixLift 4194103
  have htrace : WordTrace (prefixWord ++ tailWord_4194103) baseStart_4194103 baseEnd_4194103 := by
    simpa [prefixWord, tailWord_4194103, baseEnd_4194103] using wordTrace_append hprefix tailTrace_4194103
  have hstable : (prefixWord ++ tailWord_4194103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194103).length < 2 ^ (prefixWord ++ tailWord_4194103).sum := by decide
  have hdescent : baseEnd_4194103 < baseStart_4194103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194117 : List Nat := [1, 3, 1, 1, 1, 2, 3, 4, 3, 1, 3]
def baseStart_4194117 : Nat := 118140960795 + 4194117 * 2 ^ 59
def prefixEnd_4194117 : Nat := 4983230072969 + 3 ^ 40 * 4194117 * 2
def baseEnd_4194117 : Nat := 2153597942193272231649113

theorem tailTrace_4194117 : CollatzResearch.WordTrace tailWord_4194117 prefixEnd_4194117 2153597942193272231649113 := by
  unfold tailWord_4194117
  simp only [CollatzResearch.WordTrace]
  refine ⟨152972014146437882001300605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101981342764291921334200403 152972014146437882001300605)
  ·
    refine ⟨57364505304914205750487727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152972014146437882001300605 57364505304914205750487727)
    ·
      refine ⟨86046757957371308625731591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57364505304914205750487727 86046757957371308625731591)
      ·
        refine ⟨129070136936056962938597387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86046757957371308625731591 129070136936056962938597387)
        ·
          refine ⟨193605205404085444407896081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129070136936056962938597387 193605205404085444407896081)
          ·
            refine ⟨145203904053064083305922061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193605205404085444407896081 145203904053064083305922061)
            ·
              refine ⟨54451464019899031239720773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145203904053064083305922061 54451464019899031239720773)
              ·
                refine ⟨10209649503731068357447645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 54451464019899031239720773 10209649503731068357447645)
                ·
                  refine ⟨3828618563899150634042867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10209649503731068357447645 3828618563899150634042867)
                  ·
                    refine ⟨5742927845848725951064301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3828618563899150634042867 5742927845848725951064301)
                    ·
                      refine ⟨2153597942193272231649113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5742927845848725951064301 2153597942193272231649113)
                      ·
                        rfl

theorem cell23_4194117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 3, 4, 3, 1, 3].length) (baseStart_4194117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194117 prefixEnd_4194117 := by exact prefixLift 4194117
  have htrace : WordTrace (prefixWord ++ tailWord_4194117) baseStart_4194117 baseEnd_4194117 := by
    simpa [prefixWord, tailWord_4194117, baseEnd_4194117] using wordTrace_append hprefix tailTrace_4194117
  have hstable : (prefixWord ++ tailWord_4194117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194117).length < 2 ^ (prefixWord ++ tailWord_4194117).sum := by decide
  have hdescent : baseEnd_4194117 < baseStart_4194117 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194144 : List Nat := [2, 1, 1, 3, 3, 3, 1, 2, 2, 3, 2]
def baseStart_4194144 : Nat := 118140960795 + 4194144 * 2 ^ 59
def prefixEnd_4194144 : Nat := 4983230072969 + 3 ^ 40 * 4194144 * 2
def baseEnd_4194144 : Nat := 2153611806170943626011489

theorem tailTrace_4194144 : CollatzResearch.WordTrace tailWord_4194144 prefixEnd_4194144 2153611806170943626011489 := by
  unfold tailWord_4194144
  simp only [CollatzResearch.WordTrace]
  refine ⟨76486499458670032806266743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101981999278226710408355657 76486499458670032806266743)
  ·
    refine ⟨114729749188005049209400115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76486499458670032806266743 114729749188005049209400115)
    ·
      refine ⟨172094623782007573814100173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114729749188005049209400115 172094623782007573814100173)
      ·
        refine ⟨64535483918252840180287565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172094623782007573814100173 64535483918252840180287565)
        ·
          refine ⟨24200806469344815067607837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64535483918252840180287565 24200806469344815067607837)
          ·
            refine ⟨9075302426004305650352939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24200806469344815067607837 9075302426004305650352939)
            ·
              refine ⟨13612953639006458475529409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9075302426004305650352939 13612953639006458475529409)
              ·
                refine ⟨10209715229254843856647057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13612953639006458475529409 10209715229254843856647057)
                ·
                  refine ⟨7657286421941132892485293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10209715229254843856647057 7657286421941132892485293)
                  ·
                    refine ⟨2871482408227924834681985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7657286421941132892485293 2871482408227924834681985)
                    ·
                      refine ⟨2153611806170943626011489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2871482408227924834681985 2153611806170943626011489)
                      ·
                        rfl

theorem cell23_4194144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 2, 2, 3, 2].length) (baseStart_4194144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194144 prefixEnd_4194144 := by exact prefixLift 4194144
  have htrace : WordTrace (prefixWord ++ tailWord_4194144) baseStart_4194144 baseEnd_4194144 := by
    simpa [prefixWord, tailWord_4194144, baseEnd_4194144] using wordTrace_append hprefix tailTrace_4194144
  have hstable : (prefixWord ++ tailWord_4194144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194144).length < 2 ^ (prefixWord ++ tailWord_4194144).sum := by decide
  have hdescent : baseEnd_4194144 < baseStart_4194144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194160 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 3]
def baseStart_4194160 : Nat := 118140960795 + 4194160 * 2 ^ 59
def prefixEnd_4194160 : Nat := 4983230072969 + 3 ^ 40 * 4194160 * 2
def baseEnd_4194160 : Nat := 2153620021861415563411415

theorem tailTrace_4194160 : CollatzResearch.WordTrace tailWord_4194160 prefixEnd_4194160 2153620021861415563411415 := by
  unfold tailWord_4194160
  simp only [CollatzResearch.WordTrace]
  refine ⟨76486791242641050172557967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101982388323521400230077289 76486791242641050172557967)
  ·
    refine ⟨114730186863961575258836951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76486791242641050172557967 114730186863961575258836951)
    ·
      refine ⟨172095280295942362888255427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114730186863961575258836951 172095280295942362888255427)
      ·
        refine ⟨258142920443913544332383141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172095280295942362888255427 258142920443913544332383141)
        ·
          refine ⟨48401797583233789562321839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 258142920443913544332383141 48401797583233789562321839)
          ·
            refine ⟨72602696374850684343482759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48401797583233789562321839 72602696374850684343482759)
            ·
              refine ⟨108904044562276026515224139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72602696374850684343482759 108904044562276026515224139)
              ·
                refine ⟨163356066843414039772836209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108904044562276026515224139 163356066843414039772836209)
                ·
                  refine ⟨122517050132560529829627157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163356066843414039772836209 122517050132560529829627157)
                  ·
                    refine ⟨5742986724963774835763773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 122517050132560529829627157 5742986724963774835763773)
                    ·
                      refine ⟨2153620021861415563411415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5742986724963774835763773 2153620021861415563411415)
                      ·
                        rfl

theorem cell23_4194160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 2, 6, 3].length) (baseStart_4194160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194160 prefixEnd_4194160 := by exact prefixLift 4194160
  have htrace : WordTrace (prefixWord ++ tailWord_4194160) baseStart_4194160 baseEnd_4194160 := by
    simpa [prefixWord, tailWord_4194160, baseEnd_4194160] using wordTrace_append hprefix tailTrace_4194160
  have hstable : (prefixWord ++ tailWord_4194160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194160).length < 2 ^ (prefixWord ++ tailWord_4194160).sum := by decide
  have hdescent : baseEnd_4194160 < baseStart_4194160 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194170 : List Nat := [3, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6]
def baseStart_4194170 : Nat := 118140960795 + 4194170 * 2 ^ 59
def prefixEnd_4194170 : Nat := 4983230072969 + 3 ^ 40 * 4194170 * 2
def baseEnd_4194170 : Nat := 2153625156667960524286369

theorem tailTrace_4194170 : CollatzResearch.WordTrace tailWord_4194170 prefixEnd_4194170 2153625156667960524286369 := by
  unfold tailWord_4194170
  simp only [CollatzResearch.WordTrace]
  refine ⟨38243486803811468013244991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101982631476830581368653309 38243486803811468013244991)
  ·
    refine ⟨57365230205717202019867487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38243486803811468013244991 57365230205717202019867487)
    ·
      refine ⟨86047845308575803029801231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57365230205717202019867487 86047845308575803029801231)
      ·
        refine ⟨129071767962863704544701847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86047845308575803029801231 129071767962863704544701847)
        ·
          refine ⟨193607651944295556817052771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129071767962863704544701847 193607651944295556817052771)
          ·
            refine ⟨290411477916443335225579157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193607651944295556817052771 290411477916443335225579157)
            ·
              refine ⟨13613038027333281338699023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 290411477916443335225579157 13613038027333281338699023)
              ·
                refine ⟨20419557040999922008048535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13613038027333281338699023 20419557040999922008048535)
                ·
                  refine ⟨30629335561499883012072803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20419557040999922008048535 30629335561499883012072803)
                  ·
                    refine ⟨45944003342249824518109205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 30629335561499883012072803 45944003342249824518109205)
                    ·
                      refine ⟨2153625156667960524286369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45944003342249824518109205 2153625156667960524286369)
                      ·
                        rfl

theorem cell23_4194170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6].length) (baseStart_4194170 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194170 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194170 prefixEnd_4194170 := by exact prefixLift 4194170
  have htrace : WordTrace (prefixWord ++ tailWord_4194170) baseStart_4194170 baseEnd_4194170 := by
    simpa [prefixWord, tailWord_4194170, baseEnd_4194170] using wordTrace_append hprefix tailTrace_4194170
  have hstable : (prefixWord ++ tailWord_4194170).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194170).length < 2 ^ (prefixWord ++ tailWord_4194170).sum := by decide
  have hdescent : baseEnd_4194170 < baseStart_4194170 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194180 : List Nat := [2, 3, 2, 1, 1, 1, 4, 9]
def baseStart_4194180 : Nat := 118140960795 + 4194180 * 2 ^ 59
def prefixEnd_4194180 : Nat := 4983230072969 + 3 ^ 40 * 4194180 * 2
def baseEnd_4194180 : Nat := 79764084869426129080049

theorem tailTrace_4194180 : CollatzResearch.WordTrace tailWord_4194180 prefixEnd_4194180 79764084869426129080049 := by
  unfold tailWord_4194180
  simp only [CollatzResearch.WordTrace]
  refine ⟨76487155972604821880421997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101982874630139762507229329 76487155972604821880421997)
  ·
    refine ⟨28682683489726808205158249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76487155972604821880421997 28682683489726808205158249)
    ·
      refine ⟨21512012617295106153868687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28682683489726808205158249 21512012617295106153868687)
      ·
        refine ⟨32268018925942659230803031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21512012617295106153868687 32268018925942659230803031)
        ·
          refine ⟨48402028388913988846204547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32268018925942659230803031 48402028388913988846204547)
          ·
            refine ⟨72603042583370983269306821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48402028388913988846204547 72603042583370983269306821)
            ·
              refine ⟨13613070484382059362995029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72603042583370983269306821 13613070484382059362995029)
              ·
                refine ⟨79764084869426129080049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13613070484382059362995029 79764084869426129080049)
                ·
                  rfl

theorem cell23_4194180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 4, 9].length) (baseStart_4194180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194180 prefixEnd_4194180 := by exact prefixLift 4194180
  have htrace : WordTrace (prefixWord ++ tailWord_4194180) baseStart_4194180 baseEnd_4194180 := by
    simpa [prefixWord, tailWord_4194180, baseEnd_4194180] using wordTrace_append hprefix tailTrace_4194180
  have hstable : (prefixWord ++ tailWord_4194180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194180).length < 2 ^ (prefixWord ++ tailWord_4194180).sum := by decide
  have hdescent : baseEnd_4194180 < baseStart_4194180 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194194 : List Nat := [3, 2, 3, 2, 1, 1, 3, 1, 1, 1, 5]
def baseStart_4194194 : Nat := 118140960795 + 4194194 * 2 ^ 59
def prefixEnd_4194194 : Nat := 4983230072969 + 3 ^ 40 * 4194194 * 2
def baseEnd_4194194 : Nat := 2153637480203668430386259

theorem tailTrace_4194194 : CollatzResearch.WordTrace tailWord_4194194 prefixEnd_4194194 2153637480203668430386259 := by
  unfold tailWord_4194194
  simp only [CollatzResearch.WordTrace]
  refine ⟨38243705641789731037963409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101983215044772616101235757 38243705641789731037963409)
  ·
    refine ⟨28682779231342298278472557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38243705641789731037963409 28682779231342298278472557)
    ·
      refine ⟨10756042211753361854427209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28682779231342298278472557 10756042211753361854427209)
      ·
        refine ⟨8067031658815021390820407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10756042211753361854427209 8067031658815021390820407)
        ·
          refine ⟨12100547488222532086230611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8067031658815021390820407 12100547488222532086230611)
          ·
            refine ⟨18150821232333798129345917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12100547488222532086230611 18150821232333798129345917)
            ·
              refine ⟨6806557962125174298504719, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18150821232333798129345917 6806557962125174298504719)
              ·
                refine ⟨10209836943187761447757079, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6806557962125174298504719 10209836943187761447757079)
                ·
                  refine ⟨15314755414781642171635619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10209836943187761447757079 15314755414781642171635619)
                  ·
                    refine ⟨22972133122172463257453429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15314755414781642171635619 22972133122172463257453429)
                    ·
                      refine ⟨2153637480203668430386259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22972133122172463257453429 2153637480203668430386259)
                      ·
                        rfl

theorem cell23_4194194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 3, 1, 1, 1, 5].length) (baseStart_4194194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194194 prefixEnd_4194194 := by exact prefixLift 4194194
  have htrace : WordTrace (prefixWord ++ tailWord_4194194) baseStart_4194194 baseEnd_4194194 := by
    simpa [prefixWord, tailWord_4194194, baseEnd_4194194] using wordTrace_append hprefix tailTrace_4194194
  have hstable : (prefixWord ++ tailWord_4194194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194194).length < 2 ^ (prefixWord ++ tailWord_4194194).sum := by decide
  have hdescent : baseEnd_4194194 < baseStart_4194194 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194240 : List Nat := [2, 1, 1, 2, 3, 2, 1, 2, 1, 8]
def baseStart_4194240 : Nat := 118140960795 + 4194240 * 2 ^ 59
def prefixEnd_4194240 : Nat := 4983230072969 + 3 ^ 40 * 4194240 * 2
def baseEnd_4194240 : Nat := 717887033437925083470349

theorem tailTrace_4194240 : CollatzResearch.WordTrace tailWord_4194240 prefixEnd_4194240 717887033437925083470349 := by
  unfold tailWord_4194240
  simp only [CollatzResearch.WordTrace]
  refine ⟨76488250162496137004014087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101984333549994849338685449 76488250162496137004014087)
  ·
    refine ⟨114732375243744205506021131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76488250162496137004014087 114732375243744205506021131)
    ·
      refine ⟨172098562865616308259031697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114732375243744205506021131 172098562865616308259031697)
      ·
        refine ⟨129073922149212231194273773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172098562865616308259031697 129073922149212231194273773)
        ·
          refine ⟨48402720805954586697852665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129073922149212231194273773 48402720805954586697852665)
          ·
            refine ⟨36302040604465940023389499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48402720805954586697852665 36302040604465940023389499)
            ·
              refine ⟨54453060906698910035084249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36302040604465940023389499 54453060906698910035084249)
              ·
                refine ⟨40839795680024182526313187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54453060906698910035084249 40839795680024182526313187)
                ·
                  refine ⟨61259693520036273789469781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40839795680024182526313187 61259693520036273789469781)
                  ·
                    refine ⟨717887033437925083470349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 61259693520036273789469781 717887033437925083470349)
                    ·
                      rfl

theorem cell23_4194240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 1, 2, 1, 8].length) (baseStart_4194240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194240 prefixEnd_4194240 := by exact prefixLift 4194240
  have htrace : WordTrace (prefixWord ++ tailWord_4194240) baseStart_4194240 baseEnd_4194240 := by
    simpa [prefixWord, tailWord_4194240, baseEnd_4194240] using wordTrace_append hprefix tailTrace_4194240
  have hstable : (prefixWord ++ tailWord_4194240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194240).length < 2 ^ (prefixWord ++ tailWord_4194240).sum := by decide
  have hdescent : baseEnd_4194240 < baseStart_4194240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194285 : List Nat := [1, 5, 1, 4, 1, 1, 2, 2, 1, 3, 2]
def baseStart_4194285 : Nat := 118140960795 + 4194285 * 2 ^ 59
def prefixEnd_4194285 : Nat := 4983230072969 + 3 ^ 40 * 4194285 * 2
def baseEnd_4194285 : Nat := 2153684206943227574348341

theorem tailTrace_4194285 : CollatzResearch.WordTrace tailWord_4194285 prefixEnd_4194285 2153684206943227574348341 := by
  unfold tailWord_4194285
  simp only [CollatzResearch.WordTrace]
  refine ⟨152978141609829246693416309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101985427739886164462277539 152978141609829246693416309)
  ·
    refine ⟨14341700775921491877507779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 152978141609829246693416309 14341700775921491877507779)
    ·
      refine ⟨21512551163882237816261669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14341700775921491877507779 21512551163882237816261669)
      ·
        refine ⟨4033603343227919590549063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 21512551163882237816261669 4033603343227919590549063)
        ·
          refine ⟨6050405014841879385823595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4033603343227919590549063 6050405014841879385823595)
          ·
            refine ⟨9075607522262819078735393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6050405014841879385823595 9075607522262819078735393)
            ·
              refine ⟨6806705641697114309051545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9075607522262819078735393 6806705641697114309051545)
              ·
                refine ⟨5105029231272835731788659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6806705641697114309051545 5105029231272835731788659)
                ·
                  refine ⟨7657543846909253597682989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5105029231272835731788659 7657543846909253597682989)
                  ·
                    refine ⟨2871578942590970099131121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7657543846909253597682989 2871578942590970099131121)
                    ·
                      refine ⟨2153684206943227574348341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2871578942590970099131121 2153684206943227574348341)
                      ·
                        rfl

theorem cell23_4194285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 2, 1, 3, 2].length) (baseStart_4194285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194285 prefixEnd_4194285 := by exact prefixLift 4194285
  have htrace : WordTrace (prefixWord ++ tailWord_4194285) baseStart_4194285 baseEnd_4194285 := by
    simpa [prefixWord, tailWord_4194285, baseEnd_4194285] using wordTrace_append hprefix tailTrace_4194285
  have hstable : (prefixWord ++ tailWord_4194285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194285).length < 2 ^ (prefixWord ++ tailWord_4194285).sum := by decide
  have hdescent : baseEnd_4194285 < baseStart_4194285 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194354 : List Nat := [3, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4]
def baseStart_4194354 : Nat := 118140960795 + 4194354 * 2 ^ 59
def prefixEnd_4194354 : Nat := 4983230072969 + 3 ^ 40 * 4194354 * 2
def baseEnd_4194354 : Nat := 2153719637108387804385523

theorem tailTrace_4194354 : CollatzResearch.WordTrace tailWord_4194354 prefixEnd_4194354 2153719637108387804385523 := by
  unfold tailWord_4194354
  simp only [CollatzResearch.WordTrace]
  refine ⟨38245164561644817869419529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101987105497719514318452077 38245164561644817869419529)
  ·
    refine ⟨28683873421233613402064647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38245164561644817869419529 28683873421233613402064647)
    ·
      refine ⟨43025810131850420103096971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28683873421233613402064647 43025810131850420103096971)
      ·
        refine ⟨64538715197775630154645457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43025810131850420103096971 64538715197775630154645457)
        ·
          refine ⟨48404036398331722615984093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64538715197775630154645457 48404036398331722615984093)
          ·
            refine ⟨18151513649374395980994035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48404036398331722615984093 18151513649374395980994035)
            ·
              refine ⟨27227270474061593971491053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18151513649374395980994035 27227270474061593971491053)
              ·
                refine ⟨10210226427773097739309145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27227270474061593971491053 10210226427773097739309145)
                ·
                  refine ⟨7657669820829823304481859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10210226427773097739309145 7657669820829823304481859)
                  ·
                    refine ⟨11486504731244734956722789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7657669820829823304481859 11486504731244734956722789)
                    ·
                      refine ⟨2153719637108387804385523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11486504731244734956722789 2153719637108387804385523)
                      ·
                        rfl

theorem cell23_4194354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 3, 1, 3, 2, 1, 4].length) (baseStart_4194354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194354 prefixEnd_4194354 := by exact prefixLift 4194354
  have htrace : WordTrace (prefixWord ++ tailWord_4194354) baseStart_4194354 baseEnd_4194354 := by
    simpa [prefixWord, tailWord_4194354, baseEnd_4194354] using wordTrace_append hprefix tailTrace_4194354
  have hstable : (prefixWord ++ tailWord_4194354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194354).length < 2 ^ (prefixWord ++ tailWord_4194354).sum := by decide
  have hdescent : baseEnd_4194354 < baseStart_4194354 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194381 : List Nat := [1, 6, 1, 1, 1, 1, 2, 3, 3, 4]
def baseStart_4194381 : Nat := 118140960795 + 4194381 * 2 ^ 59
def prefixEnd_4194381 : Nat := 4983230072969 + 3 ^ 40 * 4194381 * 2
def baseEnd_4194381 : Nat := 717911167028686399582633

theorem tailTrace_4194381 : CollatzResearch.WordTrace tailWord_4194381 prefixEnd_4194381 717911167028686399582633 := by
  unfold tailWord_4194381
  simp only [CollatzResearch.WordTrace]
  refine ⟨152981643017481455088910997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101987762011654303392607331 152981643017481455088910997)
  ·
    refine ⟨7171014516444443207292703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 152981643017481455088910997 7171014516444443207292703)
    ·
      refine ⟨10756521774666664810939055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7171014516444443207292703 10756521774666664810939055)
      ·
        refine ⟨16134782661999997216408583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10756521774666664810939055 16134782661999997216408583)
        ·
          refine ⟨24202173992999995824612875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16134782661999997216408583 24202173992999995824612875)
          ·
            refine ⟨36303260989499993736919313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24202173992999995824612875 36303260989499993736919313)
            ·
              refine ⟨27227445742124995302689485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36303260989499993736919313 27227445742124995302689485)
              ·
                refine ⟨10210292153296873238508557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27227445742124995302689485 10210292153296873238508557)
                ·
                  refine ⟨3828859557486327464440709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10210292153296873238508557 3828859557486327464440709)
                  ·
                    refine ⟨717911167028686399582633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3828859557486327464440709 717911167028686399582633)
                    ·
                      rfl

theorem cell23_4194381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 3, 3, 4].length) (baseStart_4194381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194381 prefixEnd_4194381 := by exact prefixLift 4194381
  have htrace : WordTrace (prefixWord ++ tailWord_4194381) baseStart_4194381 baseEnd_4194381 := by
    simpa [prefixWord, tailWord_4194381, baseEnd_4194381] using wordTrace_append hprefix tailTrace_4194381
  have hstable : (prefixWord ++ tailWord_4194381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194381).length < 2 ^ (prefixWord ++ tailWord_4194381).sum := by decide
  have hdescent : baseEnd_4194381 < baseStart_4194381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194458 : List Nat := [3, 1, 1, 5, 2, 1, 2, 2, 1, 5]
def baseStart_4194458 : Nat := 118140960795 + 4194458 * 2 ^ 59
def prefixEnd_4194458 : Nat := 4983230072969 + 3 ^ 40 * 4194458 * 2
def baseEnd_4194458 : Nat := 717924346365485132495015

theorem tailTrace_4194458 : CollatzResearch.WordTrace tailWord_4194458 prefixEnd_4194458 717924346365485132495015 := by
  unfold tailWord_4194458
  simp only [CollatzResearch.WordTrace]
  refine ⟨38246112859550624309866007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101989634292134998159642685 38246112859550624309866007)
  ·
    refine ⟨57369169289325936464799011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38246112859550624309866007 57369169289325936464799011)
    ·
      refine ⟨86053753933988904697198517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57369169289325936464799011 86053753933988904697198517)
      ·
        refine ⟨8067539431311459815362361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 86053753933988904697198517 8067539431311459815362361)
        ·
          refine ⟨6050654573483594861521771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8067539431311459815362361 6050654573483594861521771)
          ·
            refine ⟨9075981860225392292282657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6050654573483594861521771 9075981860225392292282657)
            ·
              refine ⟨6806986395169044219211993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9075981860225392292282657 6806986395169044219211993)
              ·
                refine ⟨5105239796376783164408995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6806986395169044219211993 5105239796376783164408995)
                ·
                  refine ⟨7657859694565174746613493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5105239796376783164408995 7657859694565174746613493)
                  ·
                    refine ⟨717924346365485132495015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7657859694565174746613493 717924346365485132495015)
                    ·
                      rfl

theorem cell23_4194458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 2, 2, 1, 5].length) (baseStart_4194458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194458 prefixEnd_4194458 := by exact prefixLift 4194458
  have htrace : WordTrace (prefixWord ++ tailWord_4194458) baseStart_4194458 baseEnd_4194458 := by
    simpa [prefixWord, tailWord_4194458, baseEnd_4194458] using wordTrace_append hprefix tailTrace_4194458
  have hstable : (prefixWord ++ tailWord_4194458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194458).length < 2 ^ (prefixWord ++ tailWord_4194458).sum := by decide
  have hdescent : baseEnd_4194458 < baseStart_4194458 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194461 : List Nat := [1, 4, 2, 1, 1, 3, 1, 4, 1, 1, 4]
def baseStart_4194461 : Nat := 118140960795 + 4194461 * 2 ^ 59
def prefixEnd_4194461 : Nat := 4983230072969 + 3 ^ 40 * 4194461 * 2
def baseEnd_4194461 : Nat := 2153774579538418885747531

theorem tailTrace_4194461 : CollatzResearch.WordTrace tailWord_4194461 prefixEnd_4194461 2153774579538418885747531 := by
  unfold tailWord_4194461
  simp only [CollatzResearch.WordTrace]
  refine ⟨152984560857191628751823237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101989707238127752501215491 152984560857191628751823237)
  ·
    refine ⟨28684605160723430390966857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152984560857191628751823237 28684605160723430390966857)
    ·
      refine ⟨21513453870542572793225143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28684605160723430390966857 21513453870542572793225143)
      ·
        refine ⟨32270180805813859189837715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21513453870542572793225143 32270180805813859189837715)
        ·
          refine ⟨48405271208720788784756573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32270180805813859189837715 48405271208720788784756573)
          ·
            refine ⟨18151976703270295794283715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48405271208720788784756573 18151976703270295794283715)
            ·
              refine ⟨27227965054905443691425573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18151976703270295794283715 27227965054905443691425573)
              ·
                refine ⟨5105243447794770692142295, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 27227965054905443691425573 5105243447794770692142295)
                ·
                  refine ⟨7657865171692156038213443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5105243447794770692142295 7657865171692156038213443)
                  ·
                    refine ⟨11486797757538234057320165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7657865171692156038213443 11486797757538234057320165)
                    ·
                      refine ⟨2153774579538418885747531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11486797757538234057320165 2153774579538418885747531)
                      ·
                        rfl

theorem cell23_4194461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 3, 1, 4, 1, 1, 4].length) (baseStart_4194461 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194461 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194461 prefixEnd_4194461 := by exact prefixLift 4194461
  have htrace : WordTrace (prefixWord ++ tailWord_4194461) baseStart_4194461 baseEnd_4194461 := by
    simpa [prefixWord, tailWord_4194461, baseEnd_4194461] using wordTrace_append hprefix tailTrace_4194461
  have hstable : (prefixWord ++ tailWord_4194461).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194461).length < 2 ^ (prefixWord ++ tailWord_4194461).sum := by decide
  have hdescent : baseEnd_4194461 < baseStart_4194461 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194568 : List Nat := [2, 1, 3, 2, 3, 1, 1, 3, 1, 4, 2]
def baseStart_4194568 : Nat := 118140960795 + 4194568 * 2 ^ 59
def prefixEnd_4194568 : Nat := 4983230072969 + 3 ^ 40 * 4194568 * 2
def baseEnd_4194568 : Nat := 2153829521968449967109539

theorem tailTrace_4194568 : CollatzResearch.WordTrace tailWord_4194568 prefixEnd_4194568 2153829521968449967109539 := by
  unfold tailWord_4194568
  simp only [CollatzResearch.WordTrace]
  refine ⟨76494231733901993012984179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101992308978535990683978905 76494231733901993012984179)
  ·
    refine ⟨114741347600852989519476269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76494231733901993012984179 114741347600852989519476269)
    ·
      refine ⟨43028005350319871069803601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114741347600852989519476269 43028005350319871069803601)
      ·
        refine ⟨32271004012739903302352701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43028005350319871069803601 32271004012739903302352701)
        ·
          refine ⟨12101626504777463738382263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32271004012739903302352701 12101626504777463738382263)
          ·
            refine ⟨18152439757166195607573395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12101626504777463738382263 18152439757166195607573395)
            ·
              refine ⟨27228659635749293411360093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18152439757166195607573395 27228659635749293411360093)
              ·
                refine ⟨10210747363405985029260035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27228659635749293411360093 10210747363405985029260035)
                ·
                  refine ⟨15316121045108977543890053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10210747363405985029260035 15316121045108977543890053)
                  ·
                    refine ⟨2871772695957933289479385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15316121045108977543890053 2871772695957933289479385)
                    ·
                      refine ⟨2153829521968449967109539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2871772695957933289479385 2153829521968449967109539)
                      ·
                        rfl

theorem cell23_4194568_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_4194568 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194568 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194568 prefixEnd_4194568 := by exact prefixLift 4194568
  have htrace : WordTrace (prefixWord ++ tailWord_4194568) baseStart_4194568 baseEnd_4194568 := by
    simpa [prefixWord, tailWord_4194568, baseEnd_4194568] using wordTrace_append hprefix tailTrace_4194568
  have hstable : (prefixWord ++ tailWord_4194568).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194568).length < 2 ^ (prefixWord ++ tailWord_4194568).sum := by decide
  have hdescent : baseEnd_4194568 < baseStart_4194568 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194568) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194589 : List Nat := [1, 4, 2, 3, 2, 2, 2, 1, 1, 3, 2]
def baseStart_4194589 : Nat := 118140960795 + 4194589 * 2 ^ 59
def prefixEnd_4194589 : Nat := 4983230072969 + 3 ^ 40 * 4194589 * 2
def baseEnd_4194589 : Nat := 2153840305062194384946943

theorem tailTrace_4194589 : CollatzResearch.WordTrace tailWord_4194589 prefixEnd_4194589 2153840305062194384946943 := by
  unfold tailWord_4194589
  simp only [CollatzResearch.WordTrace]
  refine ⟨152989229400727906612482821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101992819600485271074988547 152989229400727906612482821)
  ·
    refine ⟨28685480512636482489840529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 152989229400727906612482821 28685480512636482489840529)
    ·
      refine ⟨21514110384477361867380397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28685480512636482489840529 21514110384477361867380397)
      ·
        refine ⟨8067791394179010700267649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21514110384477361867380397 8067791394179010700267649)
        ·
          refine ⟨6050843545634258025200737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8067791394179010700267649 6050843545634258025200737)
          ·
            refine ⟨4538132659225693518900553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6050843545634258025200737 4538132659225693518900553)
            ·
              refine ⟨3403599494419270139175415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4538132659225693518900553 3403599494419270139175415)
              ·
                refine ⟨5105399241628905208763123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3403599494419270139175415 5105399241628905208763123)
                ·
                  refine ⟨7658098862443357813144685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5105399241628905208763123 7658098862443357813144685)
                  ·
                    refine ⟨2871787073416259179929257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7658098862443357813144685 2871787073416259179929257)
                    ·
                      refine ⟨2153840305062194384946943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2871787073416259179929257 2153840305062194384946943)
                      ·
                        rfl

theorem cell23_4194589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_4194589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194589 prefixEnd_4194589 := by exact prefixLift 4194589
  have htrace : WordTrace (prefixWord ++ tailWord_4194589) baseStart_4194589 baseEnd_4194589 := by
    simpa [prefixWord, tailWord_4194589, baseEnd_4194589] using wordTrace_append hprefix tailTrace_4194589
  have hstable : (prefixWord ++ tailWord_4194589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194589).length < 2 ^ (prefixWord ++ tailWord_4194589).sum := by decide
  have hdescent : baseEnd_4194589 < baseStart_4194589 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194602 : List Nat := [3, 1, 4, 2, 2, 1, 1, 1, 4, 2, 2]
def baseStart_4194602 : Nat := 118140960795 + 4194602 * 2 ^ 59
def prefixEnd_4194602 : Nat := 4983230072969 + 3 ^ 40 * 4194602 * 2
def baseEnd_4194602 : Nat := 2153846980310702834084383

theorem tailTrace_4194602 : CollatzResearch.WordTrace tailWord_4194602 prefixEnd_4194602 2153846980310702834084383 := by
  unfold tailWord_4194602
  simp only [CollatzResearch.WordTrace]
  refine ⟨38247425887420202458176515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101993135699787206555137373 38247425887420202458176515)
  ·
    refine ⟨57371138831130303687264773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38247425887420202458176515 57371138831130303687264773)
    ·
      refine ⟨10757088530836931941362145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57371138831130303687264773 10757088530836931941362145)
      ·
        refine ⟨8067816398127698956021609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10757088530836931941362145 8067816398127698956021609)
        ·
          refine ⟨6050862298595774217016207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8067816398127698956021609 6050862298595774217016207)
          ·
            refine ⟨9076293447893661325524311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6050862298595774217016207 9076293447893661325524311)
            ·
              refine ⟨13614440171840491988286467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9076293447893661325524311 13614440171840491988286467)
              ·
                refine ⟨20421660257760737982429701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13614440171840491988286467 20421660257760737982429701)
                ·
                  refine ⟨3829061298330138371705569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20421660257760737982429701 3829061298330138371705569)
                  ·
                    refine ⟨2871795973747603778779177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3829061298330138371705569 2871795973747603778779177)
                    ·
                      refine ⟨2153846980310702834084383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2871795973747603778779177 2153846980310702834084383)
                      ·
                        rfl

theorem cell23_4194602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 1, 4, 2, 2].length) (baseStart_4194602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194602 prefixEnd_4194602 := by exact prefixLift 4194602
  have htrace : WordTrace (prefixWord ++ tailWord_4194602) baseStart_4194602 baseEnd_4194602 := by
    simpa [prefixWord, tailWord_4194602, baseEnd_4194602] using wordTrace_append hprefix tailTrace_4194602
  have hstable : (prefixWord ++ tailWord_4194602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194602).length < 2 ^ (prefixWord ++ tailWord_4194602).sum := by decide
  have hdescent : baseEnd_4194602 < baseStart_4194602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194641 : List Nat := [1, 2, 2, 1, 4, 2, 2, 1, 1, 3, 4]
def baseStart_4194641 : Nat := 118140960795 + 4194641 * 2 ^ 59
def prefixEnd_4194641 : Nat := 4983230072969 + 3 ^ 40 * 4194641 * 2
def baseEnd_4194641 : Nat := 2153867006056228181496703

theorem tailTrace_4194641 : CollatzResearch.WordTrace tailWord_4194641 prefixEnd_4194641 2153867006056228181496703 := by
  unfold tailWord_4194641
  simp only [CollatzResearch.WordTrace]
  refine ⟨152991125996539519493375777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101994083997693012995583851 152991125996539519493375777)
  ·
    refine ⟨114743344497404639620031833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 152991125996539519493375777 114743344497404639620031833)
    ·
      refine ⟨86057508373053479715023875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114743344497404639620031833 86057508373053479715023875)
      ·
        refine ⟨129086262559580219572535813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86057508373053479715023875 129086262559580219572535813)
        ·
          refine ⟨24203674229921291169850465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 129086262559580219572535813 24203674229921291169850465)
          ·
            refine ⟨18152755672440968377387849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24203674229921291169850465 18152755672440968377387849)
            ·
              refine ⟨13614566754330726283040887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18152755672440968377387849 13614566754330726283040887)
              ·
                refine ⟨20421850131496089424561331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13614566754330726283040887 20421850131496089424561331)
                ·
                  refine ⟨30632775197244134136841997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20421850131496089424561331 30632775197244134136841997)
                  ·
                    refine ⟨11487290698966550301315749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30632775197244134136841997 11487290698966550301315749)
                    ·
                      refine ⟨2153867006056228181496703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11487290698966550301315749 2153867006056228181496703)
                      ·
                        rfl

theorem cell23_4194641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_4194641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194641 prefixEnd_4194641 := by exact prefixLift 4194641
  have htrace : WordTrace (prefixWord ++ tailWord_4194641) baseStart_4194641 baseEnd_4194641 := by
    simpa [prefixWord, tailWord_4194641, baseEnd_4194641] using wordTrace_append hprefix tailTrace_4194641
  have hstable : (prefixWord ++ tailWord_4194641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194641).length < 2 ^ (prefixWord ++ tailWord_4194641).sum := by decide
  have hdescent : baseEnd_4194641 < baseStart_4194641 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194658 : List Nat := [3, 3, 2, 1, 1, 2, 1, 1, 4, 1, 4]
def baseStart_4194658 : Nat := 118140960795 + 4194658 * 2 ^ 59
def prefixEnd_4194658 : Nat := 4983230072969 + 3 ^ 40 * 4194658 * 2
def baseEnd_4194658 : Nat := 2153875735227354614984125

theorem tailTrace_4194658 : CollatzResearch.WordTrace tailWord_4194658 prefixEnd_4194658 2153875735227354614984125 := by
  unfold tailWord_4194658
  simp only [CollatzResearch.WordTrace]
  refine ⟨38247936509369482849186157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 101994497358318620931163085 38247936509369482849186157)
  ·
    refine ⟨14342976191013556068444809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38247936509369482849186157 14342976191013556068444809)
    ·
      refine ⟨10757232143260167051333607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14342976191013556068444809 10757232143260167051333607)
      ·
        refine ⟨16135848214890250577000411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10757232143260167051333607 16135848214890250577000411)
        ·
          refine ⟨24203772322335375865500617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16135848214890250577000411 24203772322335375865500617)
          ·
            refine ⟨18152829241751531899125463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24203772322335375865500617 18152829241751531899125463)
            ·
              refine ⟨27229243862627297848688195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18152829241751531899125463 27229243862627297848688195)
              ·
                refine ⟨40843865793940946773032293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27229243862627297848688195 40843865793940946773032293)
                ·
                  refine ⟨7658224836363927519943555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40843865793940946773032293 7658224836363927519943555)
                  ·
                    refine ⟨11487337254545891279915333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7658224836363927519943555 11487337254545891279915333)
                    ·
                      refine ⟨2153875735227354614984125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11487337254545891279915333 2153875735227354614984125)
                      ·
                        rfl

theorem cell23_4194658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 4, 1, 4].length) (baseStart_4194658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194658 prefixEnd_4194658 := by exact prefixLift 4194658
  have htrace : WordTrace (prefixWord ++ tailWord_4194658) baseStart_4194658 baseEnd_4194658 := by
    simpa [prefixWord, tailWord_4194658, baseEnd_4194658] using wordTrace_append hprefix tailTrace_4194658
  have hstable : (prefixWord ++ tailWord_4194658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194658).length < 2 ^ (prefixWord ++ tailWord_4194658).sum := by decide
  have hdescent : baseEnd_4194658 < baseStart_4194658 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194792 : List Nat := [2, 1, 4, 1, 1, 4, 3, 1, 2, 4]
def baseStart_4194792 : Nat := 118140960795 + 4194792 * 2 ^ 59
def prefixEnd_4194792 : Nat := 4983230072969 + 3 ^ 40 * 4194792 * 2
def baseEnd_4194792 : Nat := 717981513878352363569503

theorem tailTrace_4194792 : CollatzResearch.WordTrace tailWord_4194792 prefixEnd_4194792 717981513878352363569503 := by
  unfold tailWord_4194792
  simp only [CollatzResearch.WordTrace]
  refine ⟨76498316709496236141061315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101997755612661648188081753 76498316709496236141061315)
  ·
    refine ⟨114747475064244354211591973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76498316709496236141061315 114747475064244354211591973)
    ·
      refine ⟨21515151574545816414673495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114747475064244354211591973 21515151574545816414673495)
      ·
        refine ⟨32272727361818724622010243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21515151574545816414673495 32272727361818724622010243)
        ·
          refine ⟨48409091042728086933015365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32272727361818724622010243 48409091042728086933015365)
          ·
            refine ⟨9076704570511516299940381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48409091042728086933015365 9076704570511516299940381)
            ·
              refine ⟨3403764213941818612477643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9076704570511516299940381 3403764213941818612477643)
              ·
                refine ⟨5105646320912727918716465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3403764213941818612477643 5105646320912727918716465)
                ·
                  refine ⟨3829234740684545939037349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5105646320912727918716465 3829234740684545939037349)
                  ·
                    refine ⟨717981513878352363569503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3829234740684545939037349 717981513878352363569503)
                    ·
                      rfl

theorem cell23_4194792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_4194792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194792 prefixEnd_4194792 := by exact prefixLift 4194792
  have htrace : WordTrace (prefixWord ++ tailWord_4194792) baseStart_4194792 baseEnd_4194792 := by
    simpa [prefixWord, tailWord_4194792, baseEnd_4194792] using wordTrace_append hprefix tailTrace_4194792
  have hstable : (prefixWord ++ tailWord_4194792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194792).length < 2 ^ (prefixWord ++ tailWord_4194792).sum := by decide
  have hdescent : baseEnd_4194792 < baseStart_4194792 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194805 : List Nat := [1, 3, 5, 1, 2, 1, 1, 9]
def baseStart_4194805 : Nat := 118140960795 + 4194805 * 2 ^ 59
def prefixEnd_4194805 : Nat := 4983230072969 + 3 ^ 40 * 4194805 * 2
def baseEnd_4194805 : Nat := 79775970995687612586887

theorem tailTrace_4194805 : CollatzResearch.WordTrace tailWord_4194805 prefixEnd_4194805 79775970995687612586887 := by
  unfold tailWord_4194805
  simp only [CollatzResearch.WordTrace]
  refine ⟨152997107567945375502345869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 101998071711963583668230579 152997107567945375502345869)
  ·
    refine ⟨57373915337979515813379701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 152997107567945375502345869 57373915337979515813379701)
    ·
      refine ⟨5378804562935579607504347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57373915337979515813379701 5378804562935579607504347)
      ·
        refine ⟨8068206844403369411256521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5378804562935579607504347 8068206844403369411256521)
        ·
          refine ⟨6051155133302527058442391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8068206844403369411256521 6051155133302527058442391)
          ·
            refine ⟨9076732699953790587663587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6051155133302527058442391 9076732699953790587663587)
            ·
              refine ⟨13615099049930685881495381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9076732699953790587663587 13615099049930685881495381)
              ·
                refine ⟨79775970995687612586887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 13615099049930685881495381 79775970995687612586887)
                ·
                  rfl

theorem cell23_4194805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 2, 1, 1, 9].length) (baseStart_4194805 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194805 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194805 prefixEnd_4194805 := by exact prefixLift 4194805
  have htrace : WordTrace (prefixWord ++ tailWord_4194805) baseStart_4194805 baseEnd_4194805 := by
    simpa [prefixWord, tailWord_4194805, baseEnd_4194805] using wordTrace_append hprefix tailTrace_4194805
  have hstable : (prefixWord ++ tailWord_4194805).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194805).length < 2 ^ (prefixWord ++ tailWord_4194805).sum := by decide
  have hdescent : baseEnd_4194805 < baseStart_4194805 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194822 : List Nat := [6, 2, 1, 1, 1, 1, 11]
def baseStart_4194822 : Nat := 118140960795 + 4194822 * 2 ^ 59
def prefixEnd_4194822 : Nat := 4983230072969 + 3 ^ 40 * 4194822 * 2
def baseEnd_4194822 : Nat := 26592098099440641646091

theorem tailTrace_4194822 : CollatzResearch.WordTrace tailWord_4194822 prefixEnd_4194822 26592098099440641646091 := by
  unfold tailWord_4194822
  simp only [CollatzResearch.WordTrace]
  refine ⟨4781178987777618356428585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 101998485072589191603809813 4781178987777618356428585)
  ·
    refine ⟨3585884240833213767321439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 4781178987777618356428585 3585884240833213767321439)
    ·
      refine ⟨5378826361249820650982159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3585884240833213767321439 5378826361249820650982159)
      ·
        refine ⟨8068239541874730976473239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5378826361249820650982159 8068239541874730976473239)
        ·
          refine ⟨12102359312812096464709859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8068239541874730976473239 12102359312812096464709859)
          ·
            refine ⟨18153538969218144697064789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12102359312812096464709859 18153538969218144697064789)
            ·
              refine ⟨26592098099440641646091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 18153538969218144697064789 26592098099440641646091)
              ·
                rfl

theorem cell23_4194822_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 11].length) (baseStart_4194822 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194822 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194822 prefixEnd_4194822 := by exact prefixLift 4194822
  have htrace : WordTrace (prefixWord ++ tailWord_4194822) baseStart_4194822 baseEnd_4194822 := by
    simpa [prefixWord, tailWord_4194822, baseEnd_4194822] using wordTrace_append hprefix tailTrace_4194822
  have hstable : (prefixWord ++ tailWord_4194822).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194822).length < 2 ^ (prefixWord ++ tailWord_4194822).sum := by decide
  have hdescent : baseEnd_4194822 < baseStart_4194822 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194822) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194884 : List Nat := [2, 3, 5, 1, 2, 1, 2, 2, 1, 2, 2]
def baseStart_4194884 : Nat := 118140960795 + 4194884 * 2 ^ 59
def prefixEnd_4194884 : Nat := 4983230072969 + 3 ^ 40 * 4194884 * 2
def baseEnd_4194884 : Nat := 2153991781855270730758087

theorem tailTrace_4194884 : CollatzResearch.WordTrace tailWord_4194884 prefixEnd_4194884 2153991781855270730758087 := by
  unfold tailWord_4194884
  simp only [CollatzResearch.WordTrace]
  refine ⟨76499994467329585997235853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 101999992623106114662981137 76499994467329585997235853)
  ·
    refine ⟨28687497925248594748963445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76499994467329585997235853 28687497925248594748963445)
    ·
      refine ⟨2689452930492055757715323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 28687497925248594748963445 2689452930492055757715323)
      ·
        refine ⟨4034179395738083636572985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2689452930492055757715323 4034179395738083636572985)
        ·
          refine ⟨3025634546803562727429739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4034179395738083636572985 3025634546803562727429739)
          ·
            refine ⟨4538451820205344091144609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3025634546803562727429739 4538451820205344091144609)
            ·
              refine ⟨3403838865154008068358457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4538451820205344091144609 3403838865154008068358457)
              ·
                refine ⟨2552879148865506051268843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3403838865154008068358457 2552879148865506051268843)
                ·
                  refine ⟨3829318723298259076903265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2552879148865506051268843 3829318723298259076903265)
                  ·
                    refine ⟨2871989042473694307677449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3829318723298259076903265 2871989042473694307677449)
                    ·
                      refine ⟨2153991781855270730758087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2871989042473694307677449 2153991781855270730758087)
                      ·
                        rfl

theorem cell23_4194884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 2, 2, 1, 2, 2].length) (baseStart_4194884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194884 prefixEnd_4194884 := by exact prefixLift 4194884
  have htrace : WordTrace (prefixWord ++ tailWord_4194884) baseStart_4194884 baseEnd_4194884 := by
    simpa [prefixWord, tailWord_4194884, baseEnd_4194884] using wordTrace_append hprefix tailTrace_4194884
  have hstable : (prefixWord ++ tailWord_4194884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194884).length < 2 ^ (prefixWord ++ tailWord_4194884).sum := by decide
  have hdescent : baseEnd_4194884 < baseStart_4194884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194888 : List Nat := [2, 1, 3, 1, 1, 1, 1, 2, 3, 5, 3]
def baseStart_4194888 : Nat := 118140960795 + 4194888 * 2 ^ 59
def prefixEnd_4194888 : Nat := 4983230072969 + 3 ^ 40 * 4194888 * 2
def baseEnd_4194888 : Nat := 2153993835777888715108067

theorem tailTrace_4194888 : CollatzResearch.WordTrace tailWord_4194888 prefixEnd_4194888 2153993835777888715108067 := by
  unfold tailWord_4194888
  simp only [CollatzResearch.WordTrace]
  refine ⟨76500067413322340338808659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102000089884429787118411545 76500067413322340338808659)
  ·
    refine ⟨114750101119983510508212989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76500067413322340338808659 114750101119983510508212989)
    ·
      refine ⟨43031287919993816440579871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114750101119983510508212989 43031287919993816440579871)
      ·
        refine ⟨64546931879990724660869807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43031287919993816440579871 64546931879990724660869807)
        ·
          refine ⟨96820397819986086991304711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64546931879990724660869807 96820397819986086991304711)
          ·
            refine ⟨145230596729979130486957067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96820397819986086991304711 145230596729979130486957067)
            ·
              refine ⟨217845895094968695730435601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145230596729979130486957067 217845895094968695730435601)
              ·
                refine ⟨163384421321226521797826701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217845895094968695730435601 163384421321226521797826701)
                ·
                  refine ⟨61269157995459945674185013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163384421321226521797826701 61269157995459945674185013)
                  ·
                    refine ⟨5743983562074369906954845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61269157995459945674185013 5743983562074369906954845)
                    ·
                      refine ⟨2153993835777888715108067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5743983562074369906954845 2153993835777888715108067)
                      ·
                        rfl

theorem cell23_4194888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_4194888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194888 prefixEnd_4194888 := by exact prefixLift 4194888
  have htrace : WordTrace (prefixWord ++ tailWord_4194888) baseStart_4194888 baseEnd_4194888 := by
    simpa [prefixWord, tailWord_4194888, baseEnd_4194888] using wordTrace_append hprefix tailTrace_4194888
  have hstable : (prefixWord ++ tailWord_4194888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194888).length < 2 ^ (prefixWord ++ tailWord_4194888).sum := by decide
  have hdescent : baseEnd_4194888 < baseStart_4194888 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194915 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 2, 5, 2]
def baseStart_4194915 : Nat := 118140960795 + 4194915 * 2 ^ 59
def prefixEnd_4194915 : Nat := 4983230072969 + 3 ^ 40 * 4194915 * 2
def baseEnd_4194915 : Nat := 2154007699755560109470443

theorem tailTrace_4194915 : CollatzResearch.WordTrace tailWord_4194915 prefixEnd_4194915 2154007699755560109470443 := by
  unfold tailWord_4194915
  simp only [CollatzResearch.WordTrace]
  refine ⟨153001119597546864288850199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102000746398364576192566799 153001119597546864288850199)
  ·
    refine ⟨229501679396320296433275299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153001119597546864288850199 229501679396320296433275299)
    ·
      refine ⟨344252519094480444649912949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229501679396320296433275299 344252519094480444649912949)
      ·
        refine ⟨32273673665107541685929339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 344252519094480444649912949 32273673665107541685929339)
        ·
          refine ⟨48410510497661312528894009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32273673665107541685929339 48410510497661312528894009)
          ·
            refine ⟨36307882873245984396670507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48410510497661312528894009 36307882873245984396670507)
            ·
              refine ⟨54461824309868976595005761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36307882873245984396670507 54461824309868976595005761)
              ·
                refine ⟨40846368232401732446254321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54461824309868976595005761 40846368232401732446254321)
                ·
                  refine ⟨30634776174301299334690741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40846368232401732446254321 30634776174301299334690741)
                  ·
                    refine ⟨2872010266340746812627257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30634776174301299334690741 2872010266340746812627257)
                    ·
                      refine ⟨2154007699755560109470443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2872010266340746812627257 2154007699755560109470443)
                      ·
                        rfl

theorem cell23_4194915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_4194915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194915 prefixEnd_4194915 := by exact prefixLift 4194915
  have htrace : WordTrace (prefixWord ++ tailWord_4194915) baseStart_4194915 baseEnd_4194915 := by
    simpa [prefixWord, tailWord_4194915, baseEnd_4194915] using wordTrace_append hprefix tailTrace_4194915
  have hstable : (prefixWord ++ tailWord_4194915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194915).length < 2 ^ (prefixWord ++ tailWord_4194915).sum := by decide
  have hdescent : baseEnd_4194915 < baseStart_4194915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194925 : List Nat := [1, 5, 1, 1, 3, 2, 1, 1, 1, 7]
def baseStart_4194925 : Nat := 118140960795 + 4194925 * 2 ^ 59
def prefixEnd_4194925 : Nat := 4983230072969 + 3 ^ 40 * 4194925 * 2
def baseEnd_4194925 : Nat := 718004278187368356781799

theorem tailTrace_4194925 : CollatzResearch.WordTrace tailWord_4194925 prefixEnd_4194925 718004278187368356781799 := by
  unfold tailWord_4194925
  simp only [CollatzResearch.WordTrace]
  refine ⟨153001484327510635996714229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102000989551673757331142819 153001484327510635996714229)
  ·
    refine ⟨14343889155704122124691959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 153001484327510635996714229 14343889155704122124691959)
    ·
      refine ⟨21515833733556183187037939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14343889155704122124691959 21515833733556183187037939)
      ·
        refine ⟨32273750600334274780556909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21515833733556183187037939 32273750600334274780556909)
        ·
          refine ⟨12102656475125353042708841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 32273750600334274780556909 12102656475125353042708841)
          ·
            refine ⟨9076992356344014782031631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12102656475125353042708841 9076992356344014782031631)
            ·
              refine ⟨13615488534516022173047447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9076992356344014782031631 13615488534516022173047447)
              ·
                refine ⟨20423232801774033259571171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13615488534516022173047447 20423232801774033259571171)
                ·
                  refine ⟨30634849202661049889356757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20423232801774033259571171 30634849202661049889356757)
                  ·
                    refine ⟨718004278187368356781799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30634849202661049889356757 718004278187368356781799)
                    ·
                      rfl

theorem cell23_4194925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_4194925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194925 prefixEnd_4194925 := by exact prefixLift 4194925
  have htrace : WordTrace (prefixWord ++ tailWord_4194925) baseStart_4194925 baseEnd_4194925 := by
    simpa [prefixWord, tailWord_4194925, baseEnd_4194925] using wordTrace_append hprefix tailTrace_4194925
  have hstable : (prefixWord ++ tailWord_4194925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194925).length < 2 ^ (prefixWord ++ tailWord_4194925).sum := by decide
  have hdescent : baseEnd_4194925 < baseStart_4194925 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194945 : List Nat := [1, 2, 4, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_4194945 : Nat := 118140960795 + 4194945 * 2 ^ 59
def prefixEnd_4194945 : Nat := 4983230072969 + 3 ^ 40 * 4194945 * 2
def baseEnd_4194945 : Nat := 2154023104175194992095305

theorem tailTrace_4194945 : CollatzResearch.WordTrace tailWord_4194945 prefixEnd_4194945 2154023104175194992095305 := by
  unfold tailWord_4194945
  simp only [CollatzResearch.WordTrace]
  refine ⟨153002213787438179412442289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102001475858292119608294859 153002213787438179412442289)
  ·
    refine ⟨114751660340578634559331717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153002213787438179412442289 114751660340578634559331717)
    ·
      refine ⟨21515936313858493979874697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114751660340578634559331717 21515936313858493979874697)
      ·
        refine ⟨16136952235393870484906023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21515936313858493979874697 16136952235393870484906023)
        ·
          refine ⟨24205428353090805727359035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16136952235393870484906023 24205428353090805727359035)
          ·
            refine ⟨36308142529636208591038553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24205428353090805727359035 36308142529636208591038553)
            ·
              refine ⟨27231106897227156443278915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36308142529636208591038553 27231106897227156443278915)
              ·
                refine ⟨40846660345840734664918373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27231106897227156443278915 40846660345840734664918373)
                ·
                  refine ⟨7658748814845137749672195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40846660345840734664918373 7658748814845137749672195)
                  ·
                    refine ⟨11488123222267706624508293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7658748814845137749672195 11488123222267706624508293)
                    ·
                      refine ⟨2154023104175194992095305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11488123222267706624508293 2154023104175194992095305)
                      ·
                        rfl

theorem cell23_4194945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_4194945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194945 prefixEnd_4194945 := by exact prefixLift 4194945
  have htrace : WordTrace (prefixWord ++ tailWord_4194945) baseStart_4194945 baseEnd_4194945 := by
    simpa [prefixWord, tailWord_4194945, baseEnd_4194945] using wordTrace_append hprefix tailTrace_4194945
  have hstable : (prefixWord ++ tailWord_4194945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194945).length < 2 ^ (prefixWord ++ tailWord_4194945).sum := by decide
  have hdescent : baseEnd_4194945 < baseStart_4194945 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194946 : List Nat := [3, 4, 3, 1, 1, 1, 2, 1, 7]
def baseStart_4194946 : Nat := 118140960795 + 4194946 * 2 ^ 59
def prefixEnd_4194946 : Nat := 4983230072969 + 3 ^ 40 * 4194946 * 2
def baseEnd_4194946 : Nat := 239335957517316609798089

theorem tailTrace_4194946 : CollatzResearch.WordTrace tailWord_4194946 prefixEnd_4194946 239335957517316609798089 := by
  unfold tailWord_4194946
  simp only [CollatzResearch.WordTrace]
  refine ⟨38250562565108639145807173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102001500173623037722152461 38250562565108639145807173)
  ·
    refine ⟨7171980480957869839838845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38250562565108639145807173 7171980480957869839838845)
    ·
      refine ⟨2689492680359201189939567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7171980480957869839838845 2689492680359201189939567)
      ·
        refine ⟨4034239020538801784909351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2689492680359201189939567 4034239020538801784909351)
        ·
          refine ⟨6051358530808202677364027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4034239020538801784909351 6051358530808202677364027)
          ·
            refine ⟨9077037796212304016046041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6051358530808202677364027 9077037796212304016046041)
            ·
              refine ⟨6807778347159228012034531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9077037796212304016046041 6807778347159228012034531)
              ·
                refine ⟨10211667520738842018051797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6807778347159228012034531 10211667520738842018051797)
                ·
                  refine ⟨239335957517316609798089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10211667520738842018051797 239335957517316609798089)
                  ·
                    rfl

theorem cell23_4194946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_4194946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194946 prefixEnd_4194946 := by exact prefixLift 4194946
  have htrace : WordTrace (prefixWord ++ tailWord_4194946) baseStart_4194946 baseEnd_4194946 := by
    simpa [prefixWord, tailWord_4194946, baseEnd_4194946] using wordTrace_append hprefix tailTrace_4194946
  have hstable : (prefixWord ++ tailWord_4194946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194946).length < 2 ^ (prefixWord ++ tailWord_4194946).sum := by decide
  have hdescent : baseEnd_4194946 < baseStart_4194946 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4194972 : List Nat := [2, 2, 3, 2, 2, 1, 2, 2, 3, 4]
def baseStart_4194972 : Nat := 118140960795 + 4194972 * 2 ^ 59
def prefixEnd_4194972 : Nat := 4983230072969 + 3 ^ 40 * 4194972 * 2
def baseEnd_4194972 : Nat := 718012322717622128819227

theorem tailTrace_4194972 : CollatzResearch.WordTrace tailWord_4194972 prefixEnd_4194972 718012322717622128819227 := by
  unfold tailWord_4194972
  simp only [CollatzResearch.WordTrace]
  refine ⟨76501599279170181511837585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102002132372226908682450113 76501599279170181511837585)
  ·
    refine ⟨57376199459377636133878189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76501599279170181511837585 57376199459377636133878189)
    ·
      refine ⟨21516074797266613550204321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57376199459377636133878189 21516074797266613550204321)
      ·
        refine ⟨16137056097949960162653241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21516074797266613550204321 16137056097949960162653241)
        ·
          refine ⟨12102792073462470121989931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16137056097949960162653241 12102792073462470121989931)
          ·
            refine ⟨18154188110193705182984897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12102792073462470121989931 18154188110193705182984897)
            ·
              refine ⟨13615641082645278887238673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18154188110193705182984897 13615641082645278887238673)
              ·
                refine ⟨10211730811983959165429005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13615641082645278887238673 10211730811983959165429005)
                ·
                  refine ⟨3829399054493984687035877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10211730811983959165429005 3829399054493984687035877)
                  ·
                    refine ⟨718012322717622128819227, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3829399054493984687035877 718012322717622128819227)
                    ·
                      rfl

theorem cell23_4194972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_4194972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4194972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4194972 prefixEnd_4194972 := by exact prefixLift 4194972
  have htrace : WordTrace (prefixWord ++ tailWord_4194972) baseStart_4194972 baseEnd_4194972 := by
    simpa [prefixWord, tailWord_4194972, baseEnd_4194972] using wordTrace_append hprefix tailTrace_4194972
  have hstable : (prefixWord ++ tailWord_4194972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4194972).length < 2 ^ (prefixWord ++ tailWord_4194972).sum := by decide
  have hdescent : baseEnd_4194972 < baseStart_4194972 := by decide
  rcases family_descends (prefixWord ++ tailWord_4194972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195006 : List Nat := [4, 2, 1, 1, 2, 1, 5, 2, 1, 4]
def baseStart_4195006 : Nat := 118140960795 + 4195006 * 2 ^ 59
def prefixEnd_4195006 : Nat := 4983230072969 + 3 ^ 40 * 4195006 * 2
def baseEnd_4195006 : Nat := 718018142165039751144175

theorem tailTrace_4195006 : CollatzResearch.WordTrace tailWord_4195006 prefixEnd_4195006 718018142165039751144175 := by
  unfold tailWord_4195006
  simp only [CollatzResearch.WordTrace]
  refine ⟨19125554830027148353801609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102002959093478124553608581 19125554830027148353801609)
  ·
    refine ⟨14344166122520361265351207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19125554830027148353801609 14344166122520361265351207)
    ·
      refine ⟨21516249183780541898026811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14344166122520361265351207 21516249183780541898026811)
      ·
        refine ⟨32274373775670812847040217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21516249183780541898026811 32274373775670812847040217)
        ·
          refine ⟨24205780331753109635280163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32274373775670812847040217 24205780331753109635280163)
          ·
            refine ⟨36308670497629664452920245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24205780331753109635280163 36308670497629664452920245)
            ·
              refine ⟨3403937859152781042461273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36308670497629664452920245 3403937859152781042461273)
              ·
                refine ⟨2552953394364585781845955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3403937859152781042461273 2552953394364585781845955)
                ·
                  refine ⟨3829430091546878672768933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2552953394364585781845955 3829430091546878672768933)
                  ·
                    refine ⟨718018142165039751144175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3829430091546878672768933 718018142165039751144175)
                    ·
                      rfl

theorem cell23_4195006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_4195006 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195006 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195006 prefixEnd_4195006 := by exact prefixLift 4195006
  have htrace : WordTrace (prefixWord ++ tailWord_4195006) baseStart_4195006 baseEnd_4195006 := by
    simpa [prefixWord, tailWord_4195006, baseEnd_4195006] using wordTrace_append hprefix tailTrace_4195006
  have hstable : (prefixWord ++ tailWord_4195006).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195006).length < 2 ^ (prefixWord ++ tailWord_4195006).sum := by decide
  have hdescent : baseEnd_4195006 < baseStart_4195006 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195032 : List Nat := [2, 1, 2, 2, 3, 2, 3, 2, 1, 5]
def baseStart_4195032 : Nat := 118140960795 + 4195032 * 2 ^ 59
def prefixEnd_4195032 : Nat := 4983230072969 + 3 ^ 40 * 4195032 * 2
def baseEnd_4195032 : Nat := 718022592330712050569135

theorem tailTrace_4195032 : CollatzResearch.WordTrace tailWord_4195032 prefixEnd_4195032 718022592330712050569135 := by
  unfold tailWord_4195032
  simp only [CollatzResearch.WordTrace]
  refine ⟨76502693469061496635429675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102003591292081995513906233 76502693469061496635429675)
  ·
    refine ⟨114754040203592244953144513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76502693469061496635429675 114754040203592244953144513)
    ·
      refine ⟨86065530152694183714858385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114754040203592244953144513 86065530152694183714858385)
      ·
        refine ⟨64549147614520637786143789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86065530152694183714858385 64549147614520637786143789)
        ·
          refine ⟨24205930355445239169803921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64549147614520637786143789 24205930355445239169803921)
          ·
            refine ⟨18154447766583929377352941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24205930355445239169803921 18154447766583929377352941)
            ·
              refine ⟨6807917912468973516507353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18154447766583929377352941 6807917912468973516507353)
              ·
                refine ⟨5105938434351730137380515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6807917912468973516507353 5105938434351730137380515)
                ·
                  refine ⟨7658907651527595206070773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5105938434351730137380515 7658907651527595206070773)
                  ·
                    refine ⟨718022592330712050569135, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7658907651527595206070773 718022592330712050569135)
                    ·
                      rfl

theorem cell23_4195032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 3, 2, 1, 5].length) (baseStart_4195032 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195032 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195032 prefixEnd_4195032 := by exact prefixLift 4195032
  have htrace : WordTrace (prefixWord ++ tailWord_4195032) baseStart_4195032 baseEnd_4195032 := by
    simpa [prefixWord, tailWord_4195032, baseEnd_4195032] using wordTrace_append hprefix tailTrace_4195032
  have hstable : (prefixWord ++ tailWord_4195032).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195032).length < 2 ^ (prefixWord ++ tailWord_4195032).sum := by decide
  have hdescent : baseEnd_4195032 < baseStart_4195032 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195039 : List Nat := [1, 1, 2, 3, 2, 4, 2, 1, 2, 3, 2]
def baseStart_4195039 : Nat := 118140960795 + 4195039 * 2 ^ 59
def prefixEnd_4195039 : Nat := 4983230072969 + 3 ^ 40 * 4195039 * 2
def baseEnd_4195039 : Nat := 2154071371356717624319873

theorem tailTrace_4195039 : CollatzResearch.WordTrace tailWord_4195039 prefixEnd_4195039 2154071371356717624319873 := by
  unfold tailWord_4195039
  simp only [CollatzResearch.WordTrace]
  refine ⟨153005642249097633466364171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102003761499398422310909447 153005642249097633466364171)
  ·
    refine ⟨229508463373646450199546257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153005642249097633466364171 229508463373646450199546257)
    ·
      refine ⟨172131347530234837649659693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229508463373646450199546257 172131347530234837649659693)
      ·
        refine ⟨64549255323838064118622385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172131347530234837649659693 64549255323838064118622385)
        ·
          refine ⟨48411941492878548088966789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64549255323838064118622385 48411941492878548088966789)
          ·
            refine ⟨9077239029914727766681273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48411941492878548088966789 9077239029914727766681273)
            ·
              refine ⟨6807929272436045825010955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9077239029914727766681273 6807929272436045825010955)
              ·
                refine ⟨10211893908654068737516433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6807929272436045825010955 10211893908654068737516433)
                ·
                  refine ⟨7658920431490551553137325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10211893908654068737516433 7658920431490551553137325)
                  ·
                    refine ⟨2872095161808956832426497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7658920431490551553137325 2872095161808956832426497)
                    ·
                      refine ⟨2154071371356717624319873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2872095161808956832426497 2154071371356717624319873)
                      ·
                        rfl

theorem cell23_4195039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 4, 2, 1, 2, 3, 2].length) (baseStart_4195039 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195039 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195039 prefixEnd_4195039 := by exact prefixLift 4195039
  have htrace : WordTrace (prefixWord ++ tailWord_4195039) baseStart_4195039 baseEnd_4195039 := by
    simpa [prefixWord, tailWord_4195039, baseEnd_4195039] using wordTrace_append hprefix tailTrace_4195039
  have hstable : (prefixWord ++ tailWord_4195039).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195039).length < 2 ^ (prefixWord ++ tailWord_4195039).sum := by decide
  have hdescent : baseEnd_4195039 < baseStart_4195039 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195045 : List Nat := [1, 3, 1, 4, 1, 2, 1, 1, 3, 6]
def baseStart_4195045 : Nat := 118140960795 + 4195045 * 2 ^ 59
def prefixEnd_4195045 : Nat := 4983230072969 + 3 ^ 40 * 4195045 * 2
def baseEnd_4195045 : Nat := 718024817413548200281615

theorem tailTrace_4195045 : CollatzResearch.WordTrace tailWord_4195045 prefixEnd_4195045 718024817413548200281615 := by
  unfold tailWord_4195045
  simp only [CollatzResearch.WordTrace]
  refine ⟨153005861087075896491082589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102003907391383930994055059 153005861087075896491082589)
  ·
    refine ⟨57377197907653461184155971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153005861087075896491082589 57377197907653461184155971)
    ·
      refine ⟨86065796861480191776233957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57377197907653461184155971 86065796861480191776233957)
      ·
        refine ⟨16137336911527535958043867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86065796861480191776233957 16137336911527535958043867)
        ·
          refine ⟨24206005367291303937065801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16137336911527535958043867 24206005367291303937065801)
          ·
            refine ⟨18154504025468477952799351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24206005367291303937065801 18154504025468477952799351)
            ·
              refine ⟨27231756038202716929199027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18154504025468477952799351 27231756038202716929199027)
              ·
                refine ⟨40847634057304075393798541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27231756038202716929199027 40847634057304075393798541)
                ·
                  refine ⟨15317862771489028272674453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40847634057304075393798541 15317862771489028272674453)
                  ·
                    refine ⟨718024817413548200281615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15317862771489028272674453 718024817413548200281615)
                    ·
                      rfl

theorem cell23_4195045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 1, 3, 6].length) (baseStart_4195045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195045 prefixEnd_4195045 := by exact prefixLift 4195045
  have htrace : WordTrace (prefixWord ++ tailWord_4195045) baseStart_4195045 baseEnd_4195045 := by
    simpa [prefixWord, tailWord_4195045, baseEnd_4195045] using wordTrace_append hprefix tailTrace_4195045
  have hstable : (prefixWord ++ tailWord_4195045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195045).length < 2 ^ (prefixWord ++ tailWord_4195045).sum := by decide
  have hdescent : baseEnd_4195045 < baseStart_4195045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195069 : List Nat := [1, 4, 1, 1, 1, 1, 4, 3, 3, 2, 2]
def baseStart_4195069 : Nat := 118140960795 + 4195069 * 2 ^ 59
def prefixEnd_4195069 : Nat := 4983230072969 + 3 ^ 40 * 4195069 * 2
def baseEnd_4195069 : Nat := 2154086775776352506944735

theorem tailTrace_4195069 : CollatzResearch.WordTrace tailWord_4195069 prefixEnd_4195069 2154086775776352506944735 := by
  unfold tailWord_4195069
  simp only [CollatzResearch.WordTrace]
  refine ⟨153006736438988948589956261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102004490959325965726637507 153006736438988948589956261)
  ·
    refine ⟨28688763082310427860616799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153006736438988948589956261 28688763082310427860616799)
    ·
      refine ⟨43033144623465641790925199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28688763082310427860616799 43033144623465641790925199)
      ·
        refine ⟨64549716935198462686387799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43033144623465641790925199 64549716935198462686387799)
        ·
          refine ⟨96824575402797694029581699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64549716935198462686387799 96824575402797694029581699)
          ·
            refine ⟨145236863104196541044372549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96824575402797694029581699 145236863104196541044372549)
            ·
              refine ⟨27231911832036851445819853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145236863104196541044372549 27231911832036851445819853)
              ·
                refine ⟨10211966937013819292182445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27231911832036851445819853 10211966937013819292182445)
                ·
                  refine ⟨3829487601380182234568417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10211966937013819292182445 3829487601380182234568417)
                  ·
                    refine ⟨2872115701035136675926313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3829487601380182234568417 2872115701035136675926313)
                    ·
                      refine ⟨2154086775776352506944735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2872115701035136675926313 2154086775776352506944735)
                      ·
                        rfl

theorem cell23_4195069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 4, 3, 3, 2, 2].length) (baseStart_4195069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195069 prefixEnd_4195069 := by exact prefixLift 4195069
  have htrace : WordTrace (prefixWord ++ tailWord_4195069) baseStart_4195069 baseEnd_4195069 := by
    simpa [prefixWord, tailWord_4195069, baseEnd_4195069] using wordTrace_append hprefix tailTrace_4195069
  have hstable : (prefixWord ++ tailWord_4195069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195069).length < 2 ^ (prefixWord ++ tailWord_4195069).sum := by decide
  have hdescent : baseEnd_4195069 < baseStart_4195069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195079 : List Nat := [1, 1, 4, 4, 1, 1, 2, 3, 2, 4]
def baseStart_4195079 : Nat := 118140960795 + 4195079 * 2 ^ 59
def prefixEnd_4195079 : Nat := 4983230072969 + 3 ^ 40 * 4195079 * 2
def baseEnd_4195079 : Nat := 718030636860965822606563

theorem tailTrace_4195079 : CollatzResearch.WordTrace tailWord_4195079 prefixEnd_4195079 718030636860965822606563 := by
  unfold tailWord_4195079
  simp only [CollatzResearch.WordTrace]
  refine ⟨153007101168952720297820291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102004734112635146865213527 153007101168952720297820291)
  ·
    refine ⟨229510651753429080446730437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153007101168952720297820291 229510651753429080446730437)
    ·
      refine ⟨43033247203767952583761957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229510651753429080446730437 43033247203767952583761957)
      ·
        refine ⟨8068733850706491109455367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43033247203767952583761957 8068733850706491109455367)
        ·
          refine ⟨12103100776059736664183051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8068733850706491109455367 12103100776059736664183051)
          ·
            refine ⟨18154651164089604996274577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12103100776059736664183051 18154651164089604996274577)
            ·
              refine ⟨13615988373067203747205933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18154651164089604996274577 13615988373067203747205933)
              ·
                refine ⟨5105995639900201405202225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13615988373067203747205933 5105995639900201405202225)
                ·
                  refine ⟨3829496729925151053901669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5105995639900201405202225 3829496729925151053901669)
                  ·
                    refine ⟨718030636860965822606563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3829496729925151053901669 718030636860965822606563)
                    ·
                      rfl

theorem cell23_4195079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 3, 2, 4].length) (baseStart_4195079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195079 prefixEnd_4195079 := by exact prefixLift 4195079
  have htrace : WordTrace (prefixWord ++ tailWord_4195079) baseStart_4195079 baseEnd_4195079 := by
    simpa [prefixWord, tailWord_4195079, baseEnd_4195079] using wordTrace_append hprefix tailTrace_4195079
  have hstable : (prefixWord ++ tailWord_4195079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195079).length < 2 ^ (prefixWord ++ tailWord_4195079).sum := by decide
  have hdescent : baseEnd_4195079 < baseStart_4195079 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195082 : List Nat := [3, 1, 2, 2, 1, 2, 4, 1, 1, 2, 4]
def baseStart_4195082 : Nat := 118140960795 + 4195082 * 2 ^ 59
def prefixEnd_4195082 : Nat := 4983230072969 + 3 ^ 40 * 4195082 * 2
def baseEnd_4195082 : Nat := 2154093451024860956082175

theorem tailTrace_4195082 : CollatzResearch.WordTrace tailWord_4195082 prefixEnd_4195082 2154093451024860956082175 := by
  unfold tailWord_4195082
  simp only [CollatzResearch.WordTrace]
  refine ⟨38251802646985462952544875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102004807058627901206786333 38251802646985462952544875)
  ·
    refine ⟨57377703970478194428817313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38251802646985462952544875 57377703970478194428817313)
    ·
      refine ⟨43033277977858645821612985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57377703970478194428817313 43033277977858645821612985)
      ·
        refine ⟨32274958483393984366209739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43033277977858645821612985 32274958483393984366209739)
        ·
          refine ⟨48412437725090976549314609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32274958483393984366209739 48412437725090976549314609)
          ·
            refine ⟨36309328293818232411985957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48412437725090976549314609 36309328293818232411985957)
            ·
              refine ⟨6807999055090918577247367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36309328293818232411985957 6807999055090918577247367)
              ·
                refine ⟨10211998582636377865871051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6807999055090918577247367 10211998582636377865871051)
                ·
                  refine ⟨15317997873954566798806577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10211998582636377865871051 15317997873954566798806577)
                  ·
                    refine ⟨11488498405465925099104933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15317997873954566798806577 11488498405465925099104933)
                    ·
                      refine ⟨2154093451024860956082175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11488498405465925099104933 2154093451024860956082175)
                      ·
                        rfl

theorem cell23_4195082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 4, 1, 1, 2, 4].length) (baseStart_4195082 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195082 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195082 prefixEnd_4195082 := by exact prefixLift 4195082
  have htrace : WordTrace (prefixWord ++ tailWord_4195082) baseStart_4195082 baseEnd_4195082 := by
    simpa [prefixWord, tailWord_4195082, baseEnd_4195082] using wordTrace_append hprefix tailTrace_4195082
  have hstable : (prefixWord ++ tailWord_4195082).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195082).length < 2 ^ (prefixWord ++ tailWord_4195082).sum := by decide
  have hdescent : baseEnd_4195082 < baseStart_4195082 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195090 : List Nat := [3, 2, 4, 1, 3, 1, 1, 1, 2, 3, 2]
def baseStart_4195090 : Nat := 118140960795 + 4195090 * 2 ^ 59
def prefixEnd_4195090 : Nat := 4983230072969 + 3 ^ 40 * 4195090 * 2
def baseEnd_4195090 : Nat := 2154097558870096924782139

theorem tailTrace_4195090 : CollatzResearch.WordTrace tailWord_4195090 prefixEnd_4195090 2154097558870096924782139 := by
  unfold tailWord_4195090
  simp only [CollatzResearch.WordTrace]
  refine ⟨38251875592978217294117681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102005001581275246117647149 38251875592978217294117681)
  ·
    refine ⟨28688906694733662970588261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 38251875592978217294117681 28688906694733662970588261)
    ·
      refine ⟨5379170005262561806985299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28688906694733662970588261 5379170005262561806985299)
      ·
        refine ⟨8068755007893842710477949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5379170005262561806985299 8068755007893842710477949)
        ·
          refine ⟨3025783127960191016429231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8068755007893842710477949 3025783127960191016429231)
          ·
            refine ⟨4538674691940286524643847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3025783127960191016429231 4538674691940286524643847)
            ·
              refine ⟨6808012037910429786965771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4538674691940286524643847 6808012037910429786965771)
              ·
                refine ⟨10212018056865644680448657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6808012037910429786965771 10212018056865644680448657)
                ·
                  refine ⟨7659013542649233510336493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10212018056865644680448657 7659013542649233510336493)
                  ·
                    refine ⟨2872130078493462566376185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7659013542649233510336493 2872130078493462566376185)
                    ·
                      refine ⟨2154097558870096924782139, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2872130078493462566376185 2154097558870096924782139)
                      ·
                        rfl

theorem cell23_4195090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 3, 1, 1, 1, 2, 3, 2].length) (baseStart_4195090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195090 prefixEnd_4195090 := by exact prefixLift 4195090
  have htrace : WordTrace (prefixWord ++ tailWord_4195090) baseStart_4195090 baseEnd_4195090 := by
    simpa [prefixWord, tailWord_4195090, baseEnd_4195090] using wordTrace_append hprefix tailTrace_4195090
  have hstable : (prefixWord ++ tailWord_4195090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195090).length < 2 ^ (prefixWord ++ tailWord_4195090).sum := by decide
  have hdescent : baseEnd_4195090 < baseStart_4195090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195103 : List Nat := [1, 1, 2, 4, 2, 3, 2, 3, 1, 2, 2]
def baseStart_4195103 : Nat := 118140960795 + 4195103 * 2 ^ 59
def prefixEnd_4195103 : Nat := 4983230072969 + 3 ^ 40 * 4195103 * 2
def baseEnd_4195103 : Nat := 2154104234118605373919579

theorem tailTrace_4195103 : CollatzResearch.WordTrace tailWord_4195103 prefixEnd_4195103 2154104234118605373919579 := by
  unfold tailWord_4195103
  simp only [CollatzResearch.WordTrace]
  refine ⟨153007976520865772396693963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102005317680577181597795975 153007976520865772396693963)
  ·
    refine ⟨229511964781298658595040945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153007976520865772396693963 229511964781298658595040945)
    ·
      refine ⟨172133973585973993946280709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229511964781298658595040945 172133973585973993946280709)
      ·
        refine ⟨32275120047370123864927633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172133973585973993946280709 32275120047370123864927633)
        ·
          refine ⟨24206340035527592898695725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32275120047370123864927633 24206340035527592898695725)
          ·
            refine ⟨9077377513322847337010897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24206340035527592898695725 9077377513322847337010897)
            ·
              refine ⟨6808033134992135502758173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9077377513322847337010897 6808033134992135502758173)
              ·
                refine ⟨2553012425622050813534315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6808033134992135502758173 2553012425622050813534315)
                ·
                  refine ⟨3829518638433076220301473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2553012425622050813534315 3829518638433076220301473)
                  ·
                    refine ⟨2872138978824807165226105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3829518638433076220301473 2872138978824807165226105)
                    ·
                      refine ⟨2154104234118605373919579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2872138978824807165226105 2154104234118605373919579)
                      ·
                        rfl

theorem cell23_4195103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 3, 2, 3, 1, 2, 2].length) (baseStart_4195103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195103 prefixEnd_4195103 := by exact prefixLift 4195103
  have htrace : WordTrace (prefixWord ++ tailWord_4195103) baseStart_4195103 baseEnd_4195103 := by
    simpa [prefixWord, tailWord_4195103, baseEnd_4195103] using wordTrace_append hprefix tailTrace_4195103
  have hstable : (prefixWord ++ tailWord_4195103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195103).length < 2 ^ (prefixWord ++ tailWord_4195103).sum := by decide
  have hdescent : baseEnd_4195103 < baseStart_4195103 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195106 : List Nat := [3, 3, 1, 1, 2, 2, 4, 1, 1, 2, 3]
def baseStart_4195106 : Nat := 118140960795 + 4195106 * 2 ^ 59
def prefixEnd_4195106 : Nat := 4983230072969 + 3 ^ 40 * 4195106 * 2
def baseEnd_4195106 : Nat := 2154105774560568862182065

theorem tailTrace_4195106 : CollatzResearch.WordTrace tailWord_4195106 prefixEnd_4195106 2154105774560568862182065 := by
  unfold tailWord_4195106
  simp only [CollatzResearch.WordTrace]
  refine ⟨38252021484963725977263293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102005390626569935939368781 38252021484963725977263293)
  ·
    refine ⟨14344508056861397241473735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 38252021484963725977263293 14344508056861397241473735)
    ·
      refine ⟨21516762085292095862210603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14344508056861397241473735 21516762085292095862210603)
      ·
        refine ⟨32275143127938143793315905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21516762085292095862210603 32275143127938143793315905)
        ·
          refine ⟨24206357345953607844986929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32275143127938143793315905 24206357345953607844986929)
          ·
            refine ⟨18154768009465205883740197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24206357345953607844986929 18154768009465205883740197)
            ·
              refine ⟨3404019001774726103201287, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18154768009465205883740197 3404019001774726103201287)
              ·
                refine ⟨5106028502662089154801931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3404019001774726103201287 5106028502662089154801931)
                ·
                  refine ⟨7659042753993133732202897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5106028502662089154801931 7659042753993133732202897)
                  ·
                    refine ⟨5744282065494850299152173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7659042753993133732202897 5744282065494850299152173)
                    ·
                      refine ⟨2154105774560568862182065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5744282065494850299152173 2154105774560568862182065)
                      ·
                        rfl

theorem cell23_4195106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 4, 1, 1, 2, 3].length) (baseStart_4195106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195106 prefixEnd_4195106 := by exact prefixLift 4195106
  have htrace : WordTrace (prefixWord ++ tailWord_4195106) baseStart_4195106 baseEnd_4195106 := by
    simpa [prefixWord, tailWord_4195106, baseEnd_4195106] using wordTrace_append hprefix tailTrace_4195106
  have hstable : (prefixWord ++ tailWord_4195106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195106).length < 2 ^ (prefixWord ++ tailWord_4195106).sum := by decide
  have hdescent : baseEnd_4195106 < baseStart_4195106 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195155 : List Nat := [1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 4]
def baseStart_4195155 : Nat := 118140960795 + 4195155 * 2 ^ 59
def prefixEnd_4195155 : Nat := 4983230072969 + 3 ^ 40 * 4195155 * 2
def baseEnd_4195155 : Nat := 2154130935112639170469339

theorem tailTrace_4195155 : CollatzResearch.WordTrace tailWord_4195155 prefixEnd_4195155 2154130935112639170469339 := by
  unfold tailWord_4195155
  simp only [CollatzResearch.WordTrace]
  refine ⟨153009873116677385277586919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102006582077784923518391279 153009873116677385277586919)
  ·
    refine ⟨229514809675016077916380379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153009873116677385277586919 229514809675016077916380379)
    ·
      refine ⟨344272214512524116874570569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229514809675016077916380379 344272214512524116874570569)
      ·
        refine ⟨258204160884393087655927927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344272214512524116874570569 258204160884393087655927927)
        ·
          refine ⟨387306241326589631483891891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258204160884393087655927927 387306241326589631483891891)
          ·
            refine ⟨580959361989884447225837837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387306241326589631483891891 580959361989884447225837837)
            ·
              refine ⟨217859760746206667709689189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 580959361989884447225837837 217859760746206667709689189)
              ·
                refine ⟨40848705139913750195566723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217859760746206667709689189 40848705139913750195566723)
                ·
                  refine ⟨61273057709870625293350085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40848705139913750195566723 61273057709870625293350085)
                  ·
                    refine ⟨11488698320600742242503141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 61273057709870625293350085 11488698320600742242503141)
                    ·
                      refine ⟨2154130935112639170469339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11488698320600742242503141 2154130935112639170469339)
                      ·
                        rfl

theorem cell23_4195155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 4, 1, 4, 4].length) (baseStart_4195155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195155 prefixEnd_4195155 := by exact prefixLift 4195155
  have htrace : WordTrace (prefixWord ++ tailWord_4195155) baseStart_4195155 baseEnd_4195155 := by
    simpa [prefixWord, tailWord_4195155, baseEnd_4195155] using wordTrace_append hprefix tailTrace_4195155
  have hstable : (prefixWord ++ tailWord_4195155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195155).length < 2 ^ (prefixWord ++ tailWord_4195155).sum := by decide
  have hdescent : baseEnd_4195155 < baseStart_4195155 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195162 : List Nat := [3, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5]
def baseStart_4195162 : Nat := 118140960795 + 4195162 * 2 ^ 59
def prefixEnd_4195162 : Nat := 4983230072969 + 3 ^ 40 * 4195162 * 2
def baseEnd_4195162 : Nat := 2154134529477220643081807

theorem tailTrace_4195162 : CollatzResearch.WordTrace tailWord_4195162 prefixEnd_4195162 2154134529477220643081807 := by
  unfold tailWord_4195162
  simp only [CollatzResearch.WordTrace]
  refine ⟨38252532106913006368272935, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102006752285101350315394493 38252532106913006368272935)
  ·
    refine ⟨57378798160369509552409403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38252532106913006368272935 57378798160369509552409403)
    ·
      refine ⟨86068197240554264328614105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57378798160369509552409403 86068197240554264328614105)
      ·
        refine ⟨64551147930415698246460579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86068197240554264328614105 64551147930415698246460579)
        ·
          refine ⟨96826721895623547369690869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64551147930415698246460579 96826721895623547369690869)
          ·
            refine ⟨9077505177714707565908519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 96826721895623547369690869 9077505177714707565908519)
            ·
              refine ⟨13616257766572061348862779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9077505177714707565908519 13616257766572061348862779)
              ·
                refine ⟨20424386649858092023294169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13616257766572061348862779 20424386649858092023294169)
                ·
                  refine ⟨15318289987393569017470627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20424386649858092023294169 15318289987393569017470627)
                  ·
                    refine ⟨22977434981090353526205941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15318289987393569017470627 22977434981090353526205941)
                    ·
                      refine ⟨2154134529477220643081807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22977434981090353526205941 2154134529477220643081807)
                      ·
                        rfl

theorem cell23_4195162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 5, 1, 1, 2, 1, 5].length) (baseStart_4195162 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195162 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195162 prefixEnd_4195162 := by exact prefixLift 4195162
  have htrace : WordTrace (prefixWord ++ tailWord_4195162) baseStart_4195162 baseEnd_4195162 := by
    simpa [prefixWord, tailWord_4195162, baseEnd_4195162] using wordTrace_append hprefix tailTrace_4195162
  have hstable : (prefixWord ++ tailWord_4195162).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195162).length < 2 ^ (prefixWord ++ tailWord_4195162).sum := by decide
  have hdescent : baseEnd_4195162 < baseStart_4195162 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195176 : List Nat := [2, 1, 4, 2, 1, 2, 2, 1, 4, 2, 2]
def baseStart_4195176 : Nat := 118140960795 + 4195176 * 2 ^ 59
def prefixEnd_4195176 : Nat := 4983230072969 + 3 ^ 40 * 4195176 * 2
def baseEnd_4195176 : Nat := 2154141718206383588306743

theorem tailTrace_4195176 : CollatzResearch.WordTrace tailWord_4195176 prefixEnd_4195176 2154141718206383588306743 := by
  unfold tailWord_4195176
  simp only [CollatzResearch.WordTrace]
  refine ⟨76505319524800652932050691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102007092699734203909400921 76505319524800652932050691)
  ·
    refine ⟨114757979287200979398076037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76505319524800652932050691 114757979287200979398076037)
    ·
      refine ⟨21517121116350183637139257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 114757979287200979398076037 21517121116350183637139257)
      ·
        refine ⟨16137840837262637727854443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21517121116350183637139257 16137840837262637727854443)
        ·
          refine ⟨24206761255893956591781665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16137840837262637727854443 24206761255893956591781665)
          ·
            refine ⟨18155070941920467443836249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24206761255893956591781665 18155070941920467443836249)
            ·
              refine ⟨13616303206440350582877187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18155070941920467443836249 13616303206440350582877187)
              ·
                refine ⟨20424454809660525874315781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13616303206440350582877187 20424454809660525874315781)
                ·
                  refine ⟨3829585276811348601434209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 20424454809660525874315781 3829585276811348601434209)
                  ·
                    refine ⟨2872188957608511451075657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3829585276811348601434209 2872188957608511451075657)
                    ·
                      refine ⟨2154141718206383588306743, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2872188957608511451075657 2154141718206383588306743)
                      ·
                        rfl

theorem cell23_4195176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_4195176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195176 prefixEnd_4195176 := by exact prefixLift 4195176
  have htrace : WordTrace (prefixWord ++ tailWord_4195176) baseStart_4195176 baseEnd_4195176 := by
    simpa [prefixWord, tailWord_4195176, baseEnd_4195176] using wordTrace_append hprefix tailTrace_4195176
  have hstable : (prefixWord ++ tailWord_4195176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195176).length < 2 ^ (prefixWord ++ tailWord_4195176).sum := by decide
  have hdescent : baseEnd_4195176 < baseStart_4195176 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195193 : List Nat := [1, 2, 1, 3, 2, 3, 4, 1, 2, 2, 2]
def baseStart_4195193 : Nat := 118140960795 + 4195193 * 2 ^ 59
def prefixEnd_4195193 : Nat := 4983230072969 + 3 ^ 40 * 4195193 * 2
def baseEnd_4195193 : Nat := 2154150447377510021794165

theorem tailTrace_4195193 : CollatzResearch.WordTrace tailWord_4195193 prefixEnd_4195193 2154150447377510021794165 := by
  unfold tailWord_4195193
  simp only [CollatzResearch.WordTrace]
  refine ⟨153011259090539717767470233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102007506060359811844980155 153011259090539717767470233)
  ·
    refine ⟨114758444317904788325602675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153011259090539717767470233 114758444317904788325602675)
    ·
      refine ⟨172137666476857182488404013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114758444317904788325602675 172137666476857182488404013)
      ·
        refine ⟨64551624928821443433151505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172137666476857182488404013 64551624928821443433151505)
        ·
          refine ⟨48413718696616082574863629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64551624928821443433151505 48413718696616082574863629)
          ·
            refine ⟨18155144511231030965573861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48413718696616082574863629 18155144511231030965573861)
            ·
              refine ⟨3404089595855818306045099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 18155144511231030965573861 3404089595855818306045099)
              ·
                refine ⟨5106134393783727459067649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3404089595855818306045099 5106134393783727459067649)
                ·
                  refine ⟨3829600795337795594300737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5106134393783727459067649 3829600795337795594300737)
                  ·
                    refine ⟨2872200596503346695725553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3829600795337795594300737 2872200596503346695725553)
                    ·
                      refine ⟨2154150447377510021794165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2872200596503346695725553 2154150447377510021794165)
                      ·
                        rfl

theorem cell23_4195193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 4, 1, 2, 2, 2].length) (baseStart_4195193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195193 prefixEnd_4195193 := by exact prefixLift 4195193
  have htrace : WordTrace (prefixWord ++ tailWord_4195193) baseStart_4195193 baseEnd_4195193 := by
    simpa [prefixWord, tailWord_4195193, baseEnd_4195193] using wordTrace_append hprefix tailTrace_4195193
  have hstable : (prefixWord ++ tailWord_4195193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195193).length < 2 ^ (prefixWord ++ tailWord_4195193).sum := by decide
  have hdescent : baseEnd_4195193 < baseStart_4195193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195195 : List Nat := [1, 1, 1, 1, 1, 5, 2, 1, 3, 7]
def baseStart_4195195 : Nat := 118140960795 + 4195195 * 2 ^ 59
def prefixEnd_4195195 : Nat := 4983230072969 + 3 ^ 40 * 4195195 * 2
def baseEnd_4195195 : Nat := 718050491446273004656385

theorem tailTrace_4195195 : CollatzResearch.WordTrace tailWord_4195195 prefixEnd_4195195 718050491446273004656385 := by
  unfold tailWord_4195195
  simp only [CollatzResearch.WordTrace]
  refine ⟨153011332036532472109043039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102007554691021648072695359 153011332036532472109043039)
  ·
    refine ⟨229516998054798708163564559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153011332036532472109043039 229516998054798708163564559)
    ·
      refine ⟨344275497082198062245346839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229516998054798708163564559 344275497082198062245346839)
      ·
        refine ⟨516413245623297093368020259, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 344275497082198062245346839 516413245623297093368020259)
        ·
          refine ⟨774619868434945640052030389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 516413245623297093368020259 774619868434945640052030389)
          ·
            refine ⟨72620612665776153754877849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 774619868434945640052030389 72620612665776153754877849)
            ·
              refine ⟨54465459499332115316158387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72620612665776153754877849 54465459499332115316158387)
              ·
                refine ⟨81698189248998172974237581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54465459499332115316158387 81698189248998172974237581)
                ·
                  refine ⟨30636820968374314865339093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81698189248998172974237581 30636820968374314865339093)
                  ·
                    refine ⟨718050491446273004656385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30636820968374314865339093 718050491446273004656385)
                    ·
                      rfl

theorem cell23_4195195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 2, 1, 3, 7].length) (baseStart_4195195 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195195 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195195 prefixEnd_4195195 := by exact prefixLift 4195195
  have htrace : WordTrace (prefixWord ++ tailWord_4195195) baseStart_4195195 baseEnd_4195195 := by
    simpa [prefixWord, tailWord_4195195, baseEnd_4195195] using wordTrace_append hprefix tailTrace_4195195
  have hstable : (prefixWord ++ tailWord_4195195).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195195).length < 2 ^ (prefixWord ++ tailWord_4195195).sum := by decide
  have hdescent : baseEnd_4195195 < baseStart_4195195 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195212 : List Nat := [2, 2, 1, 2, 1, 2, 3, 3, 2, 5]
def baseStart_4195212 : Nat := 118140960795 + 4195212 * 2 ^ 59
def prefixEnd_4195212 : Nat := 4983230072969 + 3 ^ 40 * 4195212 * 2
def baseEnd_4195212 : Nat := 718053401169981815818859

theorem tailTrace_4195212 : CollatzResearch.WordTrace tailWord_4195212 prefixEnd_4195212 718053401169981815818859 := by
  unfold tailWord_4195212
  simp only [CollatzResearch.WordTrace]
  refine ⟨76505976038735442006205945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102007968051647256008274593 76505976038735442006205945)
  ·
    refine ⟨57379482029051581504654459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76505976038735442006205945 57379482029051581504654459)
    ·
      refine ⟨86069223043577372256981689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57379482029051581504654459 86069223043577372256981689)
      ·
        refine ⟨64551917282683029192736267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86069223043577372256981689 64551917282683029192736267)
        ·
          refine ⟨96827875924024543789104401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64551917282683029192736267 96827875924024543789104401)
          ·
            refine ⟨72620906943018407841828301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96827875924024543789104401 72620906943018407841828301)
            ·
              refine ⟨27232840103631902940685613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72620906943018407841828301 27232840103631902940685613)
              ·
                refine ⟨10212315038861963602757105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27232840103631902940685613 10212315038861963602757105)
                ·
                  refine ⟨7659236279146472702067829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10212315038861963602757105 7659236279146472702067829)
                  ·
                    refine ⟨718053401169981815818859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7659236279146472702067829 718053401169981815818859)
                    ·
                      rfl

theorem cell23_4195212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 3, 3, 2, 5].length) (baseStart_4195212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195212 prefixEnd_4195212 := by exact prefixLift 4195212
  have htrace : WordTrace (prefixWord ++ tailWord_4195212) baseStart_4195212 baseEnd_4195212 := by
    simpa [prefixWord, tailWord_4195212, baseEnd_4195212] using wordTrace_append hprefix tailTrace_4195212
  have hstable : (prefixWord ++ tailWord_4195212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195212).length < 2 ^ (prefixWord ++ tailWord_4195212).sum := by decide
  have hdescent : baseEnd_4195212 < baseStart_4195212 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195233 : List Nat := [1, 2, 3, 4, 1, 3, 2, 2, 5]
def baseStart_4195233 : Nat := 118140960795 + 4195233 * 2 ^ 59
def prefixEnd_4195233 : Nat := 4983230072969 + 3 ^ 40 * 4195233 * 2
def baseEnd_4195233 : Nat := 239352331844854429477109

theorem tailTrace_4195233 : CollatzResearch.WordTrace tailWord_4195233 prefixEnd_4195233 239352331844854429477109 := by
  unfold tailWord_4195233
  simp only [CollatzResearch.WordTrace]
  refine ⟨153012718010394804598926353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102008478673596536399284235 153012718010394804598926353)
  ·
    refine ⟨114759538507796103449194765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153012718010394804598926353 114759538507796103449194765)
    ·
      refine ⟨43034826940423538793448037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114759538507796103449194765 43034826940423538793448037)
      ·
        refine ⟨8069030051329413523771507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43034826940423538793448037 8069030051329413523771507)
        ·
          refine ⟨12103545076994120285657261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8069030051329413523771507 12103545076994120285657261)
          ·
            refine ⟨4538829403872795107121473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12103545076994120285657261 4538829403872795107121473)
            ·
              refine ⟨3404122052904596330341105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4538829403872795107121473 3404122052904596330341105)
              ·
                refine ⟨2553091539678447247755829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3404122052904596330341105 2553091539678447247755829)
                ·
                  refine ⟨239352331844854429477109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2553091539678447247755829 239352331844854429477109)
                  ·
                    rfl

theorem cell23_4195233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 3, 2, 2, 5].length) (baseStart_4195233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195233 prefixEnd_4195233 := by exact prefixLift 4195233
  have htrace : WordTrace (prefixWord ++ tailWord_4195233) baseStart_4195233 baseEnd_4195233 := by
    simpa [prefixWord, tailWord_4195233, baseEnd_4195233] using wordTrace_append hprefix tailTrace_4195233
  have hstable : (prefixWord ++ tailWord_4195233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195233).length < 2 ^ (prefixWord ++ tailWord_4195233).sum := by decide
  have hdescent : baseEnd_4195233 < baseStart_4195233 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195289 : List Nat := [1, 2, 1, 2, 5, 1, 3, 2, 6]
def baseStart_4195289 : Nat := 118140960795 + 4195289 * 2 ^ 59
def prefixEnd_4195289 : Nat := 4983230072969 + 3 ^ 40 * 4195289 * 2
def baseEnd_4195289 : Nat := 239355526835593516243747

theorem tailTrace_4195289 : CollatzResearch.WordTrace tailWord_4195289 prefixEnd_4195289 239355526835593516243747 := by
  unfold tailWord_4195289
  simp only [CollatzResearch.WordTrace]
  refine ⟨153014760498191926162964921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102009840332127950775309947 153014760498191926162964921)
  ·
    refine ⟨114761070373643944622223691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153014760498191926162964921 114761070373643944622223691)
    ·
      refine ⟨172141605560465916933335537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114761070373643944622223691 172141605560465916933335537)
      ·
        refine ⟨129106204170349437700001653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172141605560465916933335537 129106204170349437700001653)
        ·
          refine ⟨12103706640970259784375155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 129106204170349437700001653 12103706640970259784375155)
          ·
            refine ⟨18155559961455389676562733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12103706640970259784375155 18155559961455389676562733)
            ·
              refine ⟨6808334985545771128711025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18155559961455389676562733 6808334985545771128711025)
              ·
                refine ⟨5106251239159328346533269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6808334985545771128711025 5106251239159328346533269)
                ·
                  refine ⟨239355526835593516243747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5106251239159328346533269 239355526835593516243747)
                  ·
                    rfl

theorem cell23_4195289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 3, 2, 6].length) (baseStart_4195289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195289 prefixEnd_4195289 := by exact prefixLift 4195289
  have htrace : WordTrace (prefixWord ++ tailWord_4195289) baseStart_4195289 baseEnd_4195289 := by
    simpa [prefixWord, tailWord_4195289, baseEnd_4195289] using wordTrace_append hprefix tailTrace_4195289
  have hstable : (prefixWord ++ tailWord_4195289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195289).length < 2 ^ (prefixWord ++ tailWord_4195289).sum := by decide
  have hdescent : baseEnd_4195289 < baseStart_4195289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195293 : List Nat := [1, 4, 3, 1, 2, 1, 2, 4, 1, 4]
def baseStart_4195293 : Nat := 118140960795 + 4195293 * 2 ^ 59
def prefixEnd_4195293 : Nat := 4983230072969 + 3 ^ 40 * 4195293 * 2
def baseEnd_4195293 : Nat := 718067265147653210181235

theorem tailTrace_4195293 : CollatzResearch.WordTrace tailWord_4195293 prefixEnd_4195293 718067265147653210181235 := by
  unfold tailWord_4195293
  simp only [CollatzResearch.WordTrace]
  refine ⟨153014906390177434846110533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102009937593451623230740355 153014906390177434846110533)
  ·
    refine ⟨28690294948158269033645725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153014906390177434846110533 28690294948158269033645725)
    ·
      refine ⟨10758860605559350887617147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 28690294948158269033645725 10758860605559350887617147)
      ·
        refine ⟨16138290908339026331425721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10758860605559350887617147 16138290908339026331425721)
        ·
          refine ⟨12103718181254269748569291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16138290908339026331425721 12103718181254269748569291)
          ·
            refine ⟨18155577271881404622853937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12103718181254269748569291 18155577271881404622853937)
            ·
              refine ⟨13616682953911053467140453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18155577271881404622853937 13616682953911053467140453)
              ·
                refine ⟨2553128053858322525088835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13616682953911053467140453 2553128053858322525088835)
                ·
                  refine ⟨3829692080787483787633253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2553128053858322525088835 3829692080787483787633253)
                  ·
                    refine ⟨718067265147653210181235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3829692080787483787633253 718067265147653210181235)
                    ·
                      rfl

theorem cell23_4195293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 2, 4, 1, 4].length) (baseStart_4195293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195293 prefixEnd_4195293 := by exact prefixLift 4195293
  have htrace : WordTrace (prefixWord ++ tailWord_4195293) baseStart_4195293 baseEnd_4195293 := by
    simpa [prefixWord, tailWord_4195293, baseEnd_4195293] using wordTrace_append hprefix tailTrace_4195293
  have hstable : (prefixWord ++ tailWord_4195293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195293).length < 2 ^ (prefixWord ++ tailWord_4195293).sum := by decide
  have hdescent : baseEnd_4195293 < baseStart_4195293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195306 : List Nat := [3, 1, 3, 1, 2, 3, 3, 1, 6]
def baseStart_4195306 : Nat := 118140960795 + 4195306 * 2 ^ 59
def prefixEnd_4195306 : Nat := 4983230072969 + 3 ^ 40 * 4195306 * 2
def baseEnd_4195306 : Nat := 239356496743496453297905

theorem tailTrace_4195306 : CollatzResearch.WordTrace tailWord_4195306 prefixEnd_4195306 239356496743496453297905 := by
  unfold tailWord_4195306
  simp only [CollatzResearch.WordTrace]
  refine ⟨38253845134782584516583443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102010253692753558710889181 38253845134782584516583443)
  ·
    refine ⟨57380767702173876774875165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38253845134782584516583443 57380767702173876774875165)
    ·
      refine ⟨21517787888315203790578187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57380767702173876774875165 21517787888315203790578187)
      ·
        refine ⟨32276681832472805685867281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21517787888315203790578187 32276681832472805685867281)
        ·
          refine ⟨24207511374354604264400461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32276681832472805685867281 24207511374354604264400461)
          ·
            refine ⟨9077816765382976599150173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24207511374354604264400461 9077816765382976599150173)
            ·
              refine ⟨3404181287018616224681315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9077816765382976599150173 3404181287018616224681315)
              ·
                refine ⟨5106271930527924337021973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3404181287018616224681315 5106271930527924337021973)
                ·
                  refine ⟨239356496743496453297905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5106271930527924337021973 239356496743496453297905)
                  ·
                    rfl

theorem cell23_4195306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 3, 1, 6].length) (baseStart_4195306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195306 prefixEnd_4195306 := by exact prefixLift 4195306
  have htrace : WordTrace (prefixWord ++ tailWord_4195306) baseStart_4195306 baseEnd_4195306 := by
    simpa [prefixWord, tailWord_4195306, baseEnd_4195306] using wordTrace_append hprefix tailTrace_4195306
  have hstable : (prefixWord ++ tailWord_4195306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195306).length < 2 ^ (prefixWord ++ tailWord_4195306).sum := by decide
  have hdescent : baseEnd_4195306 < baseStart_4195306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195322 : List Nat := [3, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4]
def baseStart_4195322 : Nat := 118140960795 + 4195322 * 2 ^ 59
def prefixEnd_4195322 : Nat := 4983230072969 + 3 ^ 40 * 4195322 * 2
def baseEnd_4195322 : Nat := 2154216686381940017081071

theorem tailTrace_4195322 : CollatzResearch.WordTrace tailWord_4195322 prefixEnd_4195322 2154216686381940017081071 := by
  unfold tailWord_4195322
  simp only [CollatzResearch.WordTrace]
  refine ⟨38253991026768093199729055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102010642738048248532610813 38253991026768093199729055)
  ·
    refine ⟨57380986540152139799593583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38253991026768093199729055 57380986540152139799593583)
    ·
      refine ⟨86071479810228209699390375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57380986540152139799593583 86071479810228209699390375)
      ·
        refine ⟨129107219715342314549085563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86071479810228209699390375 129107219715342314549085563)
        ·
          refine ⟨193660829573013471823628345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129107219715342314549085563 193660829573013471823628345)
          ·
            refine ⟨145245622179760103867721259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193660829573013471823628345 145245622179760103867721259)
            ·
              refine ⟨217868433269640155801581889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145245622179760103867721259 217868433269640155801581889)
              ·
                refine ⟨163401324952230116851186417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217868433269640155801581889 163401324952230116851186417)
                ·
                  refine ⟨122550993714172587638389813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 163401324952230116851186417 122550993714172587638389813)
                  ·
                    refine ⟨11489155660703680091099045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 122550993714172587638389813 11489155660703680091099045)
                    ·
                      refine ⟨2154216686381940017081071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11489155660703680091099045 2154216686381940017081071)
                      ·
                        rfl

theorem cell23_4195322_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 1, 2, 2, 5, 4].length) (baseStart_4195322 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195322 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195322 prefixEnd_4195322 := by exact prefixLift 4195322
  have htrace : WordTrace (prefixWord ++ tailWord_4195322) baseStart_4195322 baseEnd_4195322 := by
    simpa [prefixWord, tailWord_4195322, baseEnd_4195322] using wordTrace_append hprefix tailTrace_4195322
  have hstable : (prefixWord ++ tailWord_4195322).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195322).length < 2 ^ (prefixWord ++ tailWord_4195322).sum := by decide
  have hdescent : baseEnd_4195322 < baseStart_4195322 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195322) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195359 : List Nat := [1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 5]
def baseStart_4195359 : Nat := 118140960795 + 4195359 * 2 ^ 59
def prefixEnd_4195359 : Nat := 4983230072969 + 3 ^ 40 * 4195359 * 2
def baseEnd_4195359 : Nat := 2154235685166156372318401

theorem tailTrace_4195359 : CollatzResearch.WordTrace tailWord_4195359 prefixEnd_4195359 2154235685166156372318401 := by
  unfold tailWord_4195359
  simp only [CollatzResearch.WordTrace]
  refine ⟨153017313607938328118013131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102011542405292218745342087 153017313607938328118013131)
  ·
    refine ⟨229525970411907492177019697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153017313607938328118013131 229525970411907492177019697)
    ·
      refine ⟨172144477808930619132764773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229525970411907492177019697 172144477808930619132764773)
      ·
        refine ⟨32277089589174491087393395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172144477808930619132764773 32277089589174491087393395)
        ·
          refine ⟨48415634383761736631090093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32277089589174491087393395 48415634383761736631090093)
          ·
            refine ⟨18155862893910651236658785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48415634383761736631090093 18155862893910651236658785)
            ·
              refine ⟨13616897170432988427494089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18155862893910651236658785 13616897170432988427494089)
              ·
                refine ⟨10212672877824741320620567, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13616897170432988427494089 10212672877824741320620567)
                ·
                  refine ⟨15319009316737111980930851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10212672877824741320620567 15319009316737111980930851)
                  ·
                    refine ⟨22978513975105667971396277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15319009316737111980930851 22978513975105667971396277)
                    ·
                      refine ⟨2154235685166156372318401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22978513975105667971396277 2154235685166156372318401)
                      ·
                        rfl

theorem cell23_4195359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 5].length) (baseStart_4195359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195359 prefixEnd_4195359 := by exact prefixLift 4195359
  have htrace : WordTrace (prefixWord ++ tailWord_4195359) baseStart_4195359 baseEnd_4195359 := by
    simpa [prefixWord, tailWord_4195359, baseEnd_4195359] using wordTrace_append hprefix tailTrace_4195359
  have hstable : (prefixWord ++ tailWord_4195359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195359).length < 2 ^ (prefixWord ++ tailWord_4195359).sum := by decide
  have hdescent : baseEnd_4195359 < baseStart_4195359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195370 : List Nat := [3, 1, 4, 1, 4, 1, 1, 2, 1, 5]
def baseStart_4195370 : Nat := 118140960795 + 4195370 * 2 ^ 59
def prefixEnd_4195370 : Nat := 4983230072969 + 3 ^ 40 * 4195370 * 2
def baseEnd_4195370 : Nat := 718080444484451943093617

theorem tailTrace_4195370 : CollatzResearch.WordTrace tailWord_4195370 prefixEnd_4195370 718080444484451943093617 := by
  unfold tailWord_4195370
  simp only [CollatzResearch.WordTrace]
  refine ⟨38254428702724619249165891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102011809873932317997775709 38254428702724619249165891)
  ·
    refine ⟨57381643054086928873748837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38254428702724619249165891 57381643054086928873748837)
    ·
      refine ⟨10759058072641299163827907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57381643054086928873748837 10759058072641299163827907)
      ·
        refine ⟨16138587108961948745741861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10759058072641299163827907 16138587108961948745741861)
        ·
          refine ⟨3025985082930365389826599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 16138587108961948745741861 3025985082930365389826599)
          ·
            refine ⟨4538977624395548084739899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3025985082930365389826599 4538977624395548084739899)
            ·
              refine ⟨6808466436593322127109849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4538977624395548084739899 6808466436593322127109849)
              ·
                refine ⟨5106349827444991595332387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6808466436593322127109849 5106349827444991595332387)
                ·
                  refine ⟨7659524741167487392998581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5106349827444991595332387 7659524741167487392998581)
                  ·
                    refine ⟨718080444484451943093617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7659524741167487392998581 718080444484451943093617)
                    ·
                      rfl

theorem cell23_4195370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_4195370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195370 prefixEnd_4195370 := by exact prefixLift 4195370
  have htrace : WordTrace (prefixWord ++ tailWord_4195370) baseStart_4195370 baseEnd_4195370 := by
    simpa [prefixWord, tailWord_4195370, baseEnd_4195370] using wordTrace_append hprefix tailTrace_4195370
  have hstable : (prefixWord ++ tailWord_4195370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195370).length < 2 ^ (prefixWord ++ tailWord_4195370).sum := by decide
  have hdescent : baseEnd_4195370 < baseStart_4195370 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195390 : List Nat := [4, 2, 1, 3, 1, 2, 3, 1, 1, 1, 4]
def baseStart_4195390 : Nat := 118140960795 + 4195390 * 2 ^ 59
def prefixEnd_4195390 : Nat := 4983230072969 + 3 ^ 40 * 4195390 * 2
def baseEnd_4195390 : Nat := 2154251603066445751030759

theorem tailTrace_4195390 : CollatzResearch.WordTrace tailWord_4195390 prefixEnd_4195390 2154251603066445751030759 := by
  unfold tailWord_4195390
  simp only [CollatzResearch.WordTrace]
  refine ⟨19127305533853252551548953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102012296180550680274927749 19127305533853252551548953)
  ·
    refine ⟨14345479150389939413661715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19127305533853252551548953 14345479150389939413661715)
    ·
      refine ⟨21518218725584909120492573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14345479150389939413661715 21518218725584909120492573)
      ·
        refine ⟨8069332022094340920184715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 21518218725584909120492573 8069332022094340920184715)
        ·
          refine ⟨12103998033141511380277073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8069332022094340920184715 12103998033141511380277073)
          ·
            refine ⟨9077998524856133535207805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12103998033141511380277073 9077998524856133535207805)
            ·
              refine ⟨3404249446821050075702927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9077998524856133535207805 3404249446821050075702927)
              ·
                refine ⟨5106374170231575113554391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3404249446821050075702927 5106374170231575113554391)
                ·
                  refine ⟨7659561255347362670331587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5106374170231575113554391 7659561255347362670331587)
                  ·
                    refine ⟨11489341883021044005497381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7659561255347362670331587 11489341883021044005497381)
                    ·
                      refine ⟨2154251603066445751030759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11489341883021044005497381 2154251603066445751030759)
                      ·
                        rfl

theorem cell23_4195390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 1, 1, 4].length) (baseStart_4195390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195390 prefixEnd_4195390 := by exact prefixLift 4195390
  have htrace : WordTrace (prefixWord ++ tailWord_4195390) baseStart_4195390 baseEnd_4195390 := by
    simpa [prefixWord, tailWord_4195390, baseEnd_4195390] using wordTrace_append hprefix tailTrace_4195390
  have hstable : (prefixWord ++ tailWord_4195390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195390).length < 2 ^ (prefixWord ++ tailWord_4195390).sum := by decide
  have hdescent : baseEnd_4195390 < baseStart_4195390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195393 : List Nat := [1, 2, 5, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_4195393 : Nat := 118140960795 + 4195393 * 2 ^ 59
def prefixEnd_4195393 : Nat := 4983230072969 + 3 ^ 40 * 4195393 * 2
def baseEnd_4195393 : Nat := 2154253143508409239293245

theorem tailTrace_4195393 : CollatzResearch.WordTrace tailWord_4195393 prefixEnd_4195393 2154253143508409239293245 := by
  unfold tailWord_4195393
  simp only [CollatzResearch.WordTrace]
  refine ⟨153018553689815151924750833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102012369126543434616500555 153018553689815151924750833)
  ·
    refine ⟨114763915267361363943563125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153018553689815151924750833 114763915267361363943563125)
    ·
      refine ⟨10759117056315127869709043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 114763915267361363943563125 10759117056315127869709043)
      ·
        refine ⟨16138675584472691804563565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10759117056315127869709043 16138675584472691804563565)
        ·
          refine ⟨6052003344177259426711337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16138675584472691804563565 6052003344177259426711337)
          ·
            refine ⟨4539002508132944570033503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6052003344177259426711337 4539002508132944570033503)
            ·
              refine ⟨6808503762199416855050255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4539002508132944570033503 6808503762199416855050255)
              ·
                refine ⟨10212755643299125282575383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6808503762199416855050255 10212755643299125282575383)
                ·
                  refine ⟨15319133464948687923863075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10212755643299125282575383 15319133464948687923863075)
                  ·
                    refine ⟨22978700197423031885794613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15319133464948687923863075 22978700197423031885794613)
                    ·
                      refine ⟨2154253143508409239293245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22978700197423031885794613 2154253143508409239293245)
                      ·
                        rfl

theorem cell23_4195393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_4195393 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195393 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195393 prefixEnd_4195393 := by exact prefixLift 4195393
  have htrace : WordTrace (prefixWord ++ tailWord_4195393) baseStart_4195393 baseEnd_4195393 := by
    simpa [prefixWord, tailWord_4195393, baseEnd_4195393] using wordTrace_append hprefix tailTrace_4195393
  have hstable : (prefixWord ++ tailWord_4195393).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195393).length < 2 ^ (prefixWord ++ tailWord_4195393).sum := by decide
  have hdescent : baseEnd_4195393 < baseStart_4195393 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195416 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 5, 3, 2]
def baseStart_4195416 : Nat := 118140960795 + 4195416 * 2 ^ 59
def prefixEnd_4195416 : Nat := 4983230072969 + 3 ^ 40 * 4195416 * 2
def baseEnd_4195416 : Nat := 2154264953563462649305639

theorem tailTrace_4195416 : CollatzResearch.WordTrace tailWord_4195416 prefixEnd_4195416 2154264953563462649305639 := by
  unfold tailWord_4195416
  simp only [CollatzResearch.WordTrace]
  refine ⟨76509696284365913426419051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102012928379154551235225401 76509696284365913426419051)
  ·
    refine ⟨114764544426548870139628577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76509696284365913426419051 114764544426548870139628577)
    ·
      refine ⟨86073408319911652604721433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114764544426548870139628577 86073408319911652604721433)
      ·
        refine ⟨64555056239933739453541075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86073408319911652604721433 64555056239933739453541075)
        ·
          refine ⟨96832584359900609180311613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64555056239933739453541075 96832584359900609180311613)
          ·
            refine ⟨36312219134962728442616855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96832584359900609180311613 36312219134962728442616855)
            ·
              refine ⟨54468328702444092663925283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36312219134962728442616855 54468328702444092663925283)
              ·
                refine ⟨81702493053666138995887925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54468328702444092663925283 81702493053666138995887925)
                ·
                  refine ⟨7659608723781200530864493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81702493053666138995887925 7659608723781200530864493)
                  ·
                    refine ⟨2872353271417950199074185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7659608723781200530864493 2872353271417950199074185)
                    ·
                      refine ⟨2154264953563462649305639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2872353271417950199074185 2154264953563462649305639)
                      ·
                        rfl

theorem cell23_4195416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 5, 3, 2].length) (baseStart_4195416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195416 prefixEnd_4195416 := by exact prefixLift 4195416
  have htrace : WordTrace (prefixWord ++ tailWord_4195416) baseStart_4195416 baseEnd_4195416 := by
    simpa [prefixWord, tailWord_4195416, baseEnd_4195416] using wordTrace_append hprefix tailTrace_4195416
  have hstable : (prefixWord ++ tailWord_4195416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195416).length < 2 ^ (prefixWord ++ tailWord_4195416).sum := by decide
  have hdescent : baseEnd_4195416 < baseStart_4195416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195429 : List Nat := [1, 3, 1, 3, 2, 1, 1, 2, 2, 3, 4]
def baseStart_4195429 : Nat := 118140960795 + 4195429 * 2 ^ 59
def prefixEnd_4195429 : Nat := 4983230072969 + 3 ^ 40 * 4195429 * 2
def baseEnd_4195429 : Nat := 2154271628811971098443079

theorem tailTrace_4195429 : CollatzResearch.WordTrace tailWord_4195429 prefixEnd_4195429 2154271628811971098443079 := by
  unfold tailWord_4195429
  simp only [CollatzResearch.WordTrace]
  refine ⟨153019866717684730073061341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102013244478456486715374227 153019866717684730073061341)
  ·
    refine ⟨57382450019131773777398003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153019866717684730073061341 57382450019131773777398003)
    ·
      refine ⟨86073675028697660666097005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57382450019131773777398003 86073675028697660666097005)
      ·
        refine ⟨32277628135761622749786377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86073675028697660666097005 32277628135761622749786377)
        ·
          refine ⟨24208221101821217062339783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32277628135761622749786377 24208221101821217062339783)
          ·
            refine ⟨36312331652731825593509675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24208221101821217062339783 36312331652731825593509675)
            ·
              refine ⟨54468497479097738390264513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36312331652731825593509675 54468497479097738390264513)
              ·
                refine ⟨40851373109323303792698385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54468497479097738390264513 40851373109323303792698385)
                ·
                  refine ⟨30638529831992477844523789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40851373109323303792698385 30638529831992477844523789)
                  ·
                    refine ⟨11489448686997179191696421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30638529831992477844523789 11489448686997179191696421)
                    ·
                      refine ⟨2154271628811971098443079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11489448686997179191696421 2154271628811971098443079)
                      ·
                        rfl

theorem cell23_4195429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 1, 2, 2, 3, 4].length) (baseStart_4195429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195429 prefixEnd_4195429 := by exact prefixLift 4195429
  have htrace : WordTrace (prefixWord ++ tailWord_4195429) baseStart_4195429 baseEnd_4195429 := by
    simpa [prefixWord, tailWord_4195429, baseEnd_4195429] using wordTrace_append hprefix tailTrace_4195429
  have hstable : (prefixWord ++ tailWord_4195429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195429).length < 2 ^ (prefixWord ++ tailWord_4195429).sum := by decide
  have hdescent : baseEnd_4195429 < baseStart_4195429 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195459 : List Nat := [1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 4]
def baseStart_4195459 : Nat := 118140960795 + 4195459 * 2 ^ 59
def prefixEnd_4195459 : Nat := 4983230072969 + 3 ^ 40 * 4195459 * 2
def baseEnd_4195459 : Nat := 2154287033231605981067941

theorem tailTrace_4195459 : CollatzResearch.WordTrace tailWord_4195459 prefixEnd_4195459 2154287033231605981067941 := by
  unfold tailWord_4195459
  simp only [CollatzResearch.WordTrace]
  refine ⟨153020960907576045196653431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102013973938384030131102287 153020960907576045196653431)
  ·
    refine ⟨229531441361364067794980147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153020960907576045196653431 229531441361364067794980147)
    ·
      refine ⟨344297162042046101692470221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229531441361364067794980147 344297162042046101692470221)
      ·
        refine ⟨129111435765767288134676333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 344297162042046101692470221 129111435765767288134676333)
        ·
          refine ⟨48416788412162733050503625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129111435765767288134676333 48416788412162733050503625)
          ·
            refine ⟨36312591309122049787877719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48416788412162733050503625 36312591309122049787877719)
            ·
              refine ⟨54468886963683074681816579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36312591309122049787877719 54468886963683074681816579)
              ·
                refine ⟨81703330445524612022724869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54468886963683074681816579 81703330445524612022724869)
                ·
                  refine ⟨15319374458535864754260913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81703330445524612022724869 15319374458535864754260913)
                  ·
                    refine ⟨11489530843901898565695685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 15319374458535864754260913 11489530843901898565695685)
                    ·
                      refine ⟨2154287033231605981067941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11489530843901898565695685 2154287033231605981067941)
                      ·
                        rfl

theorem cell23_4195459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_4195459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195459 prefixEnd_4195459 := by exact prefixLift 4195459
  have htrace : WordTrace (prefixWord ++ tailWord_4195459) baseStart_4195459 baseEnd_4195459 := by
    simpa [prefixWord, tailWord_4195459, baseEnd_4195459] using wordTrace_append hprefix tailTrace_4195459
  have hstable : (prefixWord ++ tailWord_4195459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195459).length < 2 ^ (prefixWord ++ tailWord_4195459).sum := by decide
  have hdescent : baseEnd_4195459 < baseStart_4195459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195480 : List Nat := [2, 1, 2, 4, 2, 3, 1, 1, 1, 4, 2]
def baseStart_4195480 : Nat := 118140960795 + 4195480 * 2 ^ 59
def prefixEnd_4195480 : Nat := 4983230072969 + 3 ^ 40 * 4195480 * 2
def baseEnd_4195480 : Nat := 2154297816325350398905345

theorem tailTrace_4195480 : CollatzResearch.WordTrace tailWord_4195480 prefixEnd_4195480 2154297816325350398905345 := by
  unfold tailWord_4195480
  simp only [CollatzResearch.WordTrace]
  refine ⟨76510863420249982891583947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102014484560333310522111929 76510863420249982891583947)
  ·
    refine ⟨114766295130374974337375921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76510863420249982891583947 114766295130374974337375921)
    ·
      refine ⟨86074721347781230753031941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114766295130374974337375921 86074721347781230753031941)
      ·
        refine ⟨16139010252708980766193489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 86074721347781230753031941 16139010252708980766193489)
        ·
          refine ⟨12104257689531735574645117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16139010252708980766193489 12104257689531735574645117)
          ·
            refine ⟨4539096633574400840491919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12104257689531735574645117 4539096633574400840491919)
            ·
              refine ⟨6808644950361601260737879, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4539096633574400840491919 6808644950361601260737879)
              ·
                refine ⟨10212967425542401891106819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6808644950361601260737879 10212967425542401891106819)
                ·
                  refine ⟨15319451138313602836660229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10212967425542401891106819 15319451138313602836660229)
                  ·
                    refine ⟨2872397088433800531873793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15319451138313602836660229 2872397088433800531873793)
                    ·
                      refine ⟨2154297816325350398905345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2872397088433800531873793 2154297816325350398905345)
                      ·
                        rfl

theorem cell23_4195480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_4195480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195480 prefixEnd_4195480 := by exact prefixLift 4195480
  have htrace : WordTrace (prefixWord ++ tailWord_4195480) baseStart_4195480 baseEnd_4195480 := by
    simpa [prefixWord, tailWord_4195480, baseEnd_4195480] using wordTrace_append hprefix tailTrace_4195480
  have hstable : (prefixWord ++ tailWord_4195480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195480).length < 2 ^ (prefixWord ++ tailWord_4195480).sum := by decide
  have hdescent : baseEnd_4195480 < baseStart_4195480 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195516 : List Nat := [2, 2, 2, 3, 2, 1, 1, 1, 4, 5]
def baseStart_4195516 : Nat := 118140960795 + 4195516 * 2 ^ 59
def prefixEnd_4195516 : Nat := 4983230072969 + 3 ^ 40 * 4195516 * 2
def baseEnd_4195516 : Nat := 718105433876304086018393

theorem tailTrace_4195516 : CollatzResearch.WordTrace tailWord_4195516 prefixEnd_4195516 718105433876304086018393 := by
  unfold tailWord_4195516
  simp only [CollatzResearch.WordTrace]
  refine ⟨76511519934184771965739201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102015359912246362620985601 76511519934184771965739201)
  ·
    refine ⟨57383639950638578974304401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76511519934184771965739201 57383639950638578974304401)
    ·
      refine ⟨43037729962978934230728301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57383639950638578974304401 43037729962978934230728301)
      ·
        refine ⟨16139148736117100336523113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 43037729962978934230728301 16139148736117100336523113)
        ·
          refine ⟨12104361552087825252392335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16139148736117100336523113 12104361552087825252392335)
          ·
            refine ⟨18156542328131737878588503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12104361552087825252392335 18156542328131737878588503)
            ·
              refine ⟨27234813492197606817882755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18156542328131737878588503 27234813492197606817882755)
              ·
                refine ⟨40852220238296410226824133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27234813492197606817882755 40852220238296410226824133)
                ·
                  refine ⟨7659791294680576917529525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40852220238296410226824133 7659791294680576917529525)
                  ·
                    refine ⟨718105433876304086018393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7659791294680576917529525 718105433876304086018393)
                    ·
                      rfl

theorem cell23_4195516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_4195516 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195516 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195516 prefixEnd_4195516 := by exact prefixLift 4195516
  have htrace : WordTrace (prefixWord ++ tailWord_4195516) baseStart_4195516 baseEnd_4195516 := by
    simpa [prefixWord, tailWord_4195516, baseEnd_4195516] using wordTrace_append hprefix tailTrace_4195516
  have hstable : (prefixWord ++ tailWord_4195516).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195516).length < 2 ^ (prefixWord ++ tailWord_4195516).sum := by decide
  have hdescent : baseEnd_4195516 < baseStart_4195516 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195520 : List Nat := [2, 1, 1, 2, 6, 1, 3, 2, 5]
def baseStart_4195520 : Nat := 118140960795 + 4195520 * 2 ^ 59
def prefixEnd_4195520 : Nat := 4983230072969 + 3 ^ 40 * 4195520 * 2
def baseEnd_4195520 : Nat := 239368706172392249156129

theorem tailTrace_4195520 : CollatzResearch.WordTrace tailWord_4195520 prefixEnd_4195520 239368706172392249156129 := by
  unfold tailWord_4195520
  simp only [CollatzResearch.WordTrace]
  refine ⟨76511592880177526307312007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102015457173570035076416009 76511592880177526307312007)
  ·
    refine ⟨114767389320266289460968011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76511592880177526307312007 114767389320266289460968011)
    ·
      refine ⟨172151083980399434191452017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114767389320266289460968011 172151083980399434191452017)
      ·
        refine ⟨129113312985299575643589013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172151083980399434191452017 129113312985299575643589013)
        ·
          refine ⟨6052186546185917608293235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 129113312985299575643589013 6052186546185917608293235)
          ·
            refine ⟨9078279819278876412439853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6052186546185917608293235 9078279819278876412439853)
            ·
              refine ⟨3404354932229578654664945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9078279819278876412439853 3404354932229578654664945)
              ·
                refine ⟨2553266199172183990998709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3404354932229578654664945 2553266199172183990998709)
                ·
                  refine ⟨239368706172392249156129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2553266199172183990998709 239368706172392249156129)
                  ·
                    rfl

theorem cell23_4195520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 6, 1, 3, 2, 5].length) (baseStart_4195520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195520 prefixEnd_4195520 := by exact prefixLift 4195520
  have htrace : WordTrace (prefixWord ++ tailWord_4195520) baseStart_4195520 baseEnd_4195520 := by
    simpa [prefixWord, tailWord_4195520, baseEnd_4195520] using wordTrace_append hprefix tailTrace_4195520
  have hstable : (prefixWord ++ tailWord_4195520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195520).length < 2 ^ (prefixWord ++ tailWord_4195520).sum := by decide
  have hdescent : baseEnd_4195520 < baseStart_4195520 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195546 : List Nat := [3, 1, 1, 2, 2, 1, 1, 3, 5, 4]
def baseStart_4195546 : Nat := 118140960795 + 4195546 * 2 ^ 59
def prefixEnd_4195546 : Nat := 4983230072969 + 3 ^ 40 * 4195546 * 2
def baseEnd_4195546 : Nat := 718110568682849046893347

theorem tailTrace_4195546 : CollatzResearch.WordTrace tailWord_4195546 prefixEnd_4195546 718110568682849046893347 := by
  unfold tailWord_4195546
  simp only [CollatzResearch.WordTrace]
  refine ⟨38256033514565214763767623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102016089372173906036713661 38256033514565214763767623)
  ·
    refine ⟨57384050271847822145651435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38256033514565214763767623 57384050271847822145651435)
    ·
      refine ⟨86076075407771733218477153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57384050271847822145651435 86076075407771733218477153)
      ·
        refine ⟨64557056555828799913857865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86076075407771733218477153 64557056555828799913857865)
        ·
          refine ⟨48417792416871599935393399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64557056555828799913857865 48417792416871599935393399)
          ·
            refine ⟨72626688625307399903090099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48417792416871599935393399 72626688625307399903090099)
            ·
              refine ⟨108940032937961099854635149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72626688625307399903090099 108940032937961099854635149)
              ·
                refine ⟨40852512351735412445488181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 108940032937961099854635149 40852512351735412445488181)
                ·
                  refine ⟨3829923032975194916764517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 40852512351735412445488181 3829923032975194916764517)
                  ·
                    refine ⟨718110568682849046893347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3829923032975194916764517 718110568682849046893347)
                    ·
                      rfl

theorem cell23_4195546_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 3, 5, 4].length) (baseStart_4195546 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195546 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195546 prefixEnd_4195546 := by exact prefixLift 4195546
  have htrace : WordTrace (prefixWord ++ tailWord_4195546) baseStart_4195546 baseEnd_4195546 := by
    simpa [prefixWord, tailWord_4195546, baseEnd_4195546] using wordTrace_append hprefix tailTrace_4195546
  have hstable : (prefixWord ++ tailWord_4195546).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195546).length < 2 ^ (prefixWord ++ tailWord_4195546).sum := by decide
  have hdescent : baseEnd_4195546 < baseStart_4195546 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195546) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195553 : List Nat := [1, 2, 3, 1, 3, 3, 2, 1, 2, 1, 4]
def baseStart_4195553 : Nat := 118140960795 + 4195553 * 2 ^ 59
def prefixEnd_4195553 : Nat := 4983230072969 + 3 ^ 40 * 4195553 * 2
def baseEnd_4195553 : Nat := 2154335300413128613292509

theorem tailTrace_4195553 : CollatzResearch.WordTrace tailWord_4195553 prefixEnd_4195553 2154335300413128613292509 := by
  unfold tailWord_4195553
  simp only [CollatzResearch.WordTrace]
  refine ⟨153024389369235499250575313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102016259579490332833716875 153024389369235499250575313)
  ·
    refine ⟨114768292026926624437931485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153024389369235499250575313 114768292026926624437931485)
    ·
      refine ⟨43038109510097484164224307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114768292026926624437931485 43038109510097484164224307)
      ·
        refine ⟨64557164265146226246336461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43038109510097484164224307 64557164265146226246336461)
        ·
          refine ⟨24208936599429834842376173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 64557164265146226246336461 24208936599429834842376173)
          ·
            refine ⟨9078351224786188065891065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24208936599429834842376173 9078351224786188065891065)
            ·
              refine ⟨6808763418589641049418299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9078351224786188065891065 6808763418589641049418299)
              ·
                refine ⟨10213145127884461574127449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6808763418589641049418299 10213145127884461574127449)
                ·
                  refine ⟨7659858845913346180595587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10213145127884461574127449 7659858845913346180595587)
                  ·
                    refine ⟨11489788268870019270893381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7659858845913346180595587 11489788268870019270893381)
                    ·
                      refine ⟨2154335300413128613292509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11489788268870019270893381 2154335300413128613292509)
                      ·
                        rfl

theorem cell23_4195553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_4195553 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195553 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195553 prefixEnd_4195553 := by exact prefixLift 4195553
  have htrace : WordTrace (prefixWord ++ tailWord_4195553) baseStart_4195553 baseEnd_4195553 := by
    simpa [prefixWord, tailWord_4195553, baseEnd_4195553] using wordTrace_append hprefix tailTrace_4195553
  have hstable : (prefixWord ++ tailWord_4195553).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195553).length < 2 ^ (prefixWord ++ tailWord_4195553).sum := by decide
  have hdescent : baseEnd_4195553 < baseStart_4195553 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195556 : List Nat := [2, 3, 1, 1, 1, 2, 2, 3, 1, 4, 3]
def baseStart_4195556 : Nat := 118140960795 + 4195556 * 2 ^ 59
def prefixEnd_4195556 : Nat := 4983230072969 + 3 ^ 40 * 4195556 * 2
def baseEnd_4195556 : Nat := 2154336840855092101554995

theorem tailTrace_4195556 : CollatzResearch.WordTrace tailWord_4195556 prefixEnd_4195556 2154336840855092101554995 := by
  unfold tailWord_4195556
  simp only [CollatzResearch.WordTrace]
  refine ⟨76512249394112315381467261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102016332525483087175289681 76512249394112315381467261)
  ·
    refine ⟨28692093522792118268050223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76512249394112315381467261 28692093522792118268050223)
    ·
      refine ⟨43038140284188177402075335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28692093522792118268050223 43038140284188177402075335)
      ·
        refine ⟨64557210426282266103113003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43038140284188177402075335 64557210426282266103113003)
        ·
          refine ⟨96835815639423399154669505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64557210426282266103113003 96835815639423399154669505)
          ·
            refine ⟨72626861729567549366002129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96835815639423399154669505 72626861729567549366002129)
            ·
              refine ⟨54470146297175662024501597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72626861729567549366002129 54470146297175662024501597)
              ·
                refine ⟨20426304861440873259188099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 54470146297175662024501597 20426304861440873259188099)
                ·
                  refine ⟨30639457292161309888782149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20426304861440873259188099 30639457292161309888782149)
                  ·
                    refine ⟨5744898242280245604146653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30639457292161309888782149 5744898242280245604146653)
                    ·
                      refine ⟨2154336840855092101554995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5744898242280245604146653 2154336840855092101554995)
                      ·
                        rfl

theorem cell23_4195556_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 2, 3, 1, 4, 3].length) (baseStart_4195556 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195556 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195556 prefixEnd_4195556 := by exact prefixLift 4195556
  have htrace : WordTrace (prefixWord ++ tailWord_4195556) baseStart_4195556 baseEnd_4195556 := by
    simpa [prefixWord, tailWord_4195556, baseEnd_4195556] using wordTrace_append hprefix tailTrace_4195556
  have hstable : (prefixWord ++ tailWord_4195556).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195556).length < 2 ^ (prefixWord ++ tailWord_4195556).sum := by decide
  have hdescent : baseEnd_4195556 < baseStart_4195556 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195556) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195637 : List Nat := [1, 3, 3, 1, 2, 2, 2, 4, 1, 1, 3]
def baseStart_4195637 : Nat := 118140960795 + 4195637 * 2 ^ 59
def prefixEnd_4195637 : Nat := 4983230072969 + 3 ^ 40 * 4195637 * 2
def baseEnd_4195637 : Nat := 2154378432788106284642123

theorem tailTrace_4195637 : CollatzResearch.WordTrace tailWord_4195637 prefixEnd_4195637 2154378432788106284642123 := by
  unfold tailWord_4195637
  simp only [CollatzResearch.WordTrace]
  refine ⟨153027453100931181596633165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102018302067287454397755443 153027453100931181596633165)
  ·
    refine ⟨57385294912849193098737437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153027453100931181596633165 57385294912849193098737437)
    ·
      refine ⟨21519485592318447412026539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57385294912849193098737437 21519485592318447412026539)
      ·
        refine ⟨32279228388477671118039809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21519485592318447412026539 32279228388477671118039809)
        ·
          refine ⟨24209421291358253338529857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32279228388477671118039809 24209421291358253338529857)
          ·
            refine ⟨18157065968518690003897393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24209421291358253338529857 18157065968518690003897393)
            ·
              refine ⟨13617799476389017502923045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18157065968518690003897393 13617799476389017502923045)
              ·
                refine ⟨2553337401822940781798071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 13617799476389017502923045 2553337401822940781798071)
                ·
                  refine ⟨3830006102734411172697107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2553337401822940781798071 3830006102734411172697107)
                  ·
                    refine ⟨5745009154101616759045661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3830006102734411172697107 5745009154101616759045661)
                    ·
                      refine ⟨2154378432788106284642123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5745009154101616759045661 2154378432788106284642123)
                      ·
                        rfl

theorem cell23_4195637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 2, 2, 4, 1, 1, 3].length) (baseStart_4195637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195637 prefixEnd_4195637 := by exact prefixLift 4195637
  have htrace : WordTrace (prefixWord ++ tailWord_4195637) baseStart_4195637 baseEnd_4195637 := by
    simpa [prefixWord, tailWord_4195637, baseEnd_4195637] using wordTrace_append hprefix tailTrace_4195637
  have hstable : (prefixWord ++ tailWord_4195637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195637).length < 2 ^ (prefixWord ++ tailWord_4195637).sum := by decide
  have hdescent : baseEnd_4195637 < baseStart_4195637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195653 : List Nat := [1, 3, 1, 1, 1, 2, 1, 7, 2, 4]
def baseStart_4195653 : Nat := 118140960795 + 4195653 * 2 ^ 59
def prefixEnd_4195653 : Nat := 4983230072969 + 3 ^ 40 * 4195653 * 2
def baseEnd_4195653 : Nat := 718128882826192740680683

theorem tailTrace_4195653 : CollatzResearch.WordTrace tailWord_4195653 prefixEnd_4195653 718128882826192740680683 := by
  unfold tailWord_4195653
  simp only [CollatzResearch.WordTrace]
  refine ⟨153028036668873216329215613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102018691112582144219477075 153028036668873216329215613)
  ·
    refine ⟨57385513750827456123455855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153028036668873216329215613 57385513750827456123455855)
    ·
      refine ⟨86078270626241184185183783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57385513750827456123455855 86078270626241184185183783)
      ·
        refine ⟨129117405939361776277775675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86078270626241184185183783 129117405939361776277775675)
        ·
          refine ⟨193676108909042664416663513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129117405939361776277775675 193676108909042664416663513)
          ·
            refine ⟨145257081681781998312497635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 193676108909042664416663513 145257081681781998312497635)
            ·
              refine ⟨217885622522672997468746453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145257081681781998312497635 217885622522672997468746453)
              ·
                refine ⟨5106694277875148378173745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 217885622522672997468746453 5106694277875148378173745)
                ·
                  refine ⟨3830020708406361283630309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5106694277875148378173745 3830020708406361283630309)
                  ·
                    refine ⟨718128882826192740680683, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3830020708406361283630309 718128882826192740680683)
                    ·
                      rfl

theorem cell23_4195653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 7, 2, 4].length) (baseStart_4195653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195653 prefixEnd_4195653 := by exact prefixLift 4195653
  have htrace : WordTrace (prefixWord ++ tailWord_4195653) baseStart_4195653 baseEnd_4195653 := by
    simpa [prefixWord, tailWord_4195653, baseEnd_4195653] using wordTrace_append hprefix tailTrace_4195653
  have hstable : (prefixWord ++ tailWord_4195653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195653).length < 2 ^ (prefixWord ++ tailWord_4195653).sum := by decide
  have hdescent : baseEnd_4195653 < baseStart_4195653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195660 : List Nat := [2, 2, 1, 3, 2, 3, 2, 2, 1, 1, 4]
def baseStart_4195660 : Nat := 118140960795 + 4195660 * 2 ^ 59
def prefixEnd_4195660 : Nat := 4983230072969 + 3 ^ 40 * 4195660 * 2
def baseEnd_4195660 : Nat := 2154390242843159694654517

theorem tailTrace_4195660 : CollatzResearch.WordTrace tailWord_4195660 prefixEnd_4195660 2154390242843159694654517 := by
  unfold tailWord_4195660
  simp only [CollatzResearch.WordTrace]
  refine ⟨76514145989923928262360217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102018861319898571016480289 76514145989923928262360217)
  ·
    refine ⟨57385609492442946196770163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76514145989923928262360217 57385609492442946196770163)
    ·
      refine ⟨86078414238664419295155245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57385609492442946196770163 86078414238664419295155245)
      ·
        refine ⟨32279405339499157235683217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86078414238664419295155245 32279405339499157235683217)
        ·
          refine ⟨24209554004624367926762413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32279405339499157235683217 24209554004624367926762413)
          ·
            refine ⟨9078582751734137972535905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 24209554004624367926762413 9078582751734137972535905)
            ·
              refine ⟨6808937063800603479401929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9078582751734137972535905 6808937063800603479401929)
              ·
                refine ⟨5106702797850452609551447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6808937063800603479401929 5106702797850452609551447)
                ·
                  refine ⟨7660054196775678914327171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5106702797850452609551447 7660054196775678914327171)
                  ·
                    refine ⟨11490081295163518371490757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7660054196775678914327171 11490081295163518371490757)
                    ·
                      refine ⟨2154390242843159694654517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11490081295163518371490757 2154390242843159694654517)
                      ·
                        rfl

theorem cell23_4195660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 1, 1, 4].length) (baseStart_4195660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195660 prefixEnd_4195660 := by exact prefixLift 4195660
  have htrace : WordTrace (prefixWord ++ tailWord_4195660) baseStart_4195660 baseEnd_4195660 := by
    simpa [prefixWord, tailWord_4195660, baseEnd_4195660] using wordTrace_append hprefix tailTrace_4195660
  have hstable : (prefixWord ++ tailWord_4195660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195660).length < 2 ^ (prefixWord ++ tailWord_4195660).sum := by decide
  have hdescent : baseEnd_4195660 < baseStart_4195660 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195680 : List Nat := [2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 3]
def baseStart_4195680 : Nat := 118140960795 + 4195680 * 2 ^ 59
def prefixEnd_4195680 : Nat := 4983230072969 + 3 ^ 40 * 4195680 * 2
def baseEnd_4195680 : Nat := 2154400512456249616404425

theorem tailTrace_4195680 : CollatzResearch.WordTrace tailWord_4195680 prefixEnd_4195680 2154400512456249616404425 := by
  unfold tailWord_4195680
  simp only [CollatzResearch.WordTrace]
  refine ⟨76514510719887699970224247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102019347626516933293632329 76514510719887699970224247)
  ·
    refine ⟨114771766079831549955336371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76514510719887699970224247 114771766079831549955336371)
    ·
      refine ⟨172157649119747324933004557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114771766079831549955336371 172157649119747324933004557)
      ·
        refine ⟨64559118419905246849876709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172157649119747324933004557 64559118419905246849876709)
        ·
          refine ⟨12104834703732233784351883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64559118419905246849876709 12104834703732233784351883)
          ·
            refine ⟨18157252055598350676527825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12104834703732233784351883 18157252055598350676527825)
            ·
              refine ⟨13617939041698763007395869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18157252055598350676527825 13617939041698763007395869)
              ·
                refine ⟨5106727140637036127773451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13617939041698763007395869 5106727140637036127773451)
                ·
                  refine ⟨7660090710955554191660177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5106727140637036127773451 7660090710955554191660177)
                  ·
                    refine ⟨5745068033216665643745133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7660090710955554191660177 5745068033216665643745133)
                    ·
                      refine ⟨2154400512456249616404425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5745068033216665643745133 2154400512456249616404425)
                      ·
                        rfl

theorem cell23_4195680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 3, 1, 2, 3].length) (baseStart_4195680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195680 prefixEnd_4195680 := by exact prefixLift 4195680
  have htrace : WordTrace (prefixWord ++ tailWord_4195680) baseStart_4195680 baseEnd_4195680 := by
    simpa [prefixWord, tailWord_4195680, baseEnd_4195680] using wordTrace_append hprefix tailTrace_4195680
  have hstable : (prefixWord ++ tailWord_4195680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195680).length < 2 ^ (prefixWord ++ tailWord_4195680).sum := by decide
  have hdescent : baseEnd_4195680 < baseStart_4195680 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195696 : List Nat := [2, 1, 1, 1, 4, 2, 2, 1, 2, 7]
def baseStart_4195696 : Nat := 118140960795 + 4195696 * 2 ^ 59
def prefixEnd_4195696 : Nat := 4983230072969 + 3 ^ 40 * 4195696 * 2
def baseEnd_4195696 : Nat := 718136242715573851268117

theorem tailTrace_4195696 : CollatzResearch.WordTrace tailWord_4195696 prefixEnd_4195696 718136242715573851268117 := by
  unfold tailWord_4195696
  simp only [CollatzResearch.WordTrace]
  refine ⟨76514802503858717336515471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102019736671811623115353961 76514802503858717336515471)
  ·
    refine ⟨114772203755788076004773207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76514802503858717336515471 114772203755788076004773207)
    ·
      refine ⟨172158305633682114007159811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114772203755788076004773207 172158305633682114007159811)
      ·
        refine ⟨258237458450523171010739717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172158305633682114007159811 258237458450523171010739717)
        ·
          refine ⟨48419523459473094564513697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 258237458450523171010739717 48419523459473094564513697)
          ·
            refine ⟨36314642594604820923385273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48419523459473094564513697 36314642594604820923385273)
            ·
              refine ⟨27235981945953615692538955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 36314642594604820923385273 27235981945953615692538955)
              ·
                refine ⟨40853972918930423538808433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27235981945953615692538955 40853972918930423538808433)
                ·
                  refine ⟨30640479689197817654106325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40853972918930423538808433 30640479689197817654106325)
                  ·
                    refine ⟨718136242715573851268117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30640479689197817654106325 718136242715573851268117)
                    ·
                      rfl

theorem cell23_4195696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 2, 2, 1, 2, 7].length) (baseStart_4195696 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195696 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195696 prefixEnd_4195696 := by exact prefixLift 4195696
  have htrace : WordTrace (prefixWord ++ tailWord_4195696) baseStart_4195696 baseEnd_4195696 := by
    simpa [prefixWord, tailWord_4195696, baseEnd_4195696] using wordTrace_append hprefix tailTrace_4195696
  have hstable : (prefixWord ++ tailWord_4195696).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195696).length < 2 ^ (prefixWord ++ tailWord_4195696).sum := by decide
  have hdescent : baseEnd_4195696 < baseStart_4195696 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195706 : List Nat := [3, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5]
def baseStart_4195706 : Nat := 118140960795 + 4195706 * 2 ^ 59
def prefixEnd_4195706 : Nat := 4983230072969 + 3 ^ 40 * 4195706 * 2
def baseEnd_4195706 : Nat := 2154413862953266514679305

theorem tailTrace_4195706 : CollatzResearch.WordTrace tailWord_4195706 prefixEnd_4195706 2154413862953266514679305 := by
  unfold tailWord_4195706
  simp only [CollatzResearch.WordTrace]
  refine ⟨38257492434420301595223743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102019979825120804253929981 38257492434420301595223743)
  ·
    refine ⟨57386238651630452392835615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38257492434420301595223743 57386238651630452392835615)
    ·
      refine ⟨86079357977445678589253423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57386238651630452392835615 86079357977445678589253423)
      ·
        refine ⟨129119036966168517883880135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86079357977445678589253423 129119036966168517883880135)
        ·
          refine ⟨193678555449252776825820203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129119036966168517883880135 193678555449252776825820203)
          ·
            refine ⟨290517833173879165238730305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193678555449252776825820203 290517833173879165238730305)
            ·
              refine ⟨217888374880409373929047729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290517833173879165238730305 217888374880409373929047729)
              ·
                refine ⟨163416281160307030446785797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 217888374880409373929047729 163416281160307030446785797)
                ·
                  refine ⟨30640552717557568208772337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 163416281160307030446785797 30640552717557568208772337)
                  ·
                    refine ⟨22980414538168176156579253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 30640552717557568208772337 22980414538168176156579253)
                    ·
                      refine ⟨2154413862953266514679305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22980414538168176156579253 2154413862953266514679305)
                      ·
                        rfl

theorem cell23_4195706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 2, 4, 2, 5].length) (baseStart_4195706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195706 prefixEnd_4195706 := by exact prefixLift 4195706
  have htrace : WordTrace (prefixWord ++ tailWord_4195706) baseStart_4195706 baseEnd_4195706 := by
    simpa [prefixWord, tailWord_4195706, baseEnd_4195706] using wordTrace_append hprefix tailTrace_4195706
  have hstable : (prefixWord ++ tailWord_4195706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195706).length < 2 ^ (prefixWord ++ tailWord_4195706).sum := by decide
  have hdescent : baseEnd_4195706 < baseStart_4195706 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195714 : List Nat := [3, 4, 2, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_4195714 : Nat := 118140960795 + 4195714 * 2 ^ 59
def prefixEnd_4195714 : Nat := 4983230072969 + 3 ^ 40 * 4195714 * 2
def baseEnd_4195714 : Nat := 2154417970798502483379269

theorem tailTrace_4195714 : CollatzResearch.WordTrace tailWord_4195714 prefixEnd_4195714 2154417970798502483379269 := by
  unfold tailWord_4195714
  simp only [CollatzResearch.WordTrace]
  refine ⟨38257565380413055936796549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102020174347768149164790797 38257565380413055936796549)
  ·
    refine ⟨7173293508827447988149353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 38257565380413055936796549 7173293508827447988149353)
    ·
      refine ⟨5379970131620585991112015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7173293508827447988149353 5379970131620585991112015)
      ·
        refine ⟨8069955197430878986668023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5379970131620585991112015 8069955197430878986668023)
        ·
          refine ⟨12104932796146318480002035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8069955197430878986668023 12104932796146318480002035)
          ·
            refine ⟨18157399194219477720003053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12104932796146318480002035 18157399194219477720003053)
            ·
              refine ⟨6809024697832304145001145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18157399194219477720003053 6809024697832304145001145)
              ·
                refine ⟨5106768523374228108750859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6809024697832304145001145 5106768523374228108750859)
                ·
                  refine ⟨7660152785061342163126289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5106768523374228108750859 7660152785061342163126289)
                  ·
                    refine ⟨5745114588796006622344717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7660152785061342163126289 5745114588796006622344717)
                    ·
                      refine ⟨2154417970798502483379269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5745114588796006622344717 2154417970798502483379269)
                      ·
                        rfl

theorem cell23_4195714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_4195714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195714 prefixEnd_4195714 := by exact prefixLift 4195714
  have htrace : WordTrace (prefixWord ++ tailWord_4195714) baseStart_4195714 baseEnd_4195714 := by
    simpa [prefixWord, tailWord_4195714, baseEnd_4195714] using wordTrace_append hprefix tailTrace_4195714
  have hstable : (prefixWord ++ tailWord_4195714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195714).length < 2 ^ (prefixWord ++ tailWord_4195714).sum := by decide
  have hdescent : baseEnd_4195714 < baseStart_4195714 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195767 : List Nat := [1, 1, 3, 1, 3, 2, 1, 5, 2, 2, 2]
def baseStart_4195767 : Nat := 118140960795 + 4195767 * 2 ^ 59
def prefixEnd_4195767 : Nat := 4983230072969 + 3 ^ 40 * 4195767 * 2
def baseEnd_4195767 : Nat := 2154445185273190776016525

theorem tailTrace_4195767 : CollatzResearch.WordTrace tailWord_4195767 prefixEnd_4195767 2154445185273190776016525 := by
  unfold tailWord_4195767
  simp only [CollatzResearch.WordTrace]
  refine ⟨153032194590460213798865555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102021463060306809199243703 153032194590460213798865555)
  ·
    refine ⟨229548291885690320698298333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153032194590460213798865555 229548291885690320698298333)
    ·
      refine ⟨86080609457133870261861875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 229548291885690320698298333 86080609457133870261861875)
      ·
        refine ⟨129120914185700805392792813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86080609457133870261861875 129120914185700805392792813)
        ·
          refine ⟨48420342819637802022297305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 129120914185700805392792813 48420342819637802022297305)
          ·
            refine ⟨36315257114728351516722979, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48420342819637802022297305 36315257114728351516722979)
            ·
              refine ⟨54472885672092527275084469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36315257114728351516722979 54472885672092527275084469)
              ·
                refine ⟨5106833031758674432039169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54472885672092527275084469 5106833031758674432039169)
                ·
                  refine ⟨3830124773819005824029377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5106833031758674432039169 3830124773819005824029377)
                  ·
                    refine ⟨2872593580364254368022033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3830124773819005824029377 2872593580364254368022033)
                    ·
                      refine ⟨2154445185273190776016525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2872593580364254368022033 2154445185273190776016525)
                      ·
                        rfl

theorem cell23_4195767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 5, 2, 2, 2].length) (baseStart_4195767 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195767 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195767 prefixEnd_4195767 := by exact prefixLift 4195767
  have htrace : WordTrace (prefixWord ++ tailWord_4195767) baseStart_4195767 baseEnd_4195767 := by
    simpa [prefixWord, tailWord_4195767, baseEnd_4195767] using wordTrace_append hprefix tailTrace_4195767
  have hstable : (prefixWord ++ tailWord_4195767).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195767).length < 2 ^ (prefixWord ++ tailWord_4195767).sum := by decide
  have hdescent : baseEnd_4195767 < baseStart_4195767 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195773 : List Nat := [1, 4, 1, 2, 2, 1, 3, 2, 7]
def baseStart_4195773 : Nat := 118140960795 + 4195773 * 2 ^ 59
def prefixEnd_4195773 : Nat := 4983230072969 + 3 ^ 40 * 4195773 * 2
def baseEnd_4195773 : Nat := 239383140684124194726833

theorem tailTrace_4195773 : CollatzResearch.WordTrace tailWord_4195773 prefixEnd_4195773 239383140684124194726833 := by
  unfold tailWord_4195773
  simp only [CollatzResearch.WordTrace]
  refine ⟨153032413428438476823583973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102021608952292317882389315 153032413428438476823583973)
  ·
    refine ⟨28693577517832214404421995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153032413428438476823583973 28693577517832214404421995)
    ·
      refine ⟨43040366276748321606632993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28693577517832214404421995 43040366276748321606632993)
      ·
        refine ⟨32280274707561241204974745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43040366276748321606632993 32280274707561241204974745)
        ·
          refine ⟨24210206030670930903731059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32280274707561241204974745 24210206030670930903731059)
          ·
            refine ⟨36315309046006396355596589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24210206030670930903731059 36315309046006396355596589)
            ·
              refine ⟨13618240892252398633348721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36315309046006396355596589 13618240892252398633348721)
              ·
                refine ⟨10213680669189298975011541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13618240892252398633348721 10213680669189298975011541)
                ·
                  refine ⟨239383140684124194726833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10213680669189298975011541 239383140684124194726833)
                  ·
                    rfl

theorem cell23_4195773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 3, 2, 7].length) (baseStart_4195773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195773 prefixEnd_4195773 := by exact prefixLift 4195773
  have htrace : WordTrace (prefixWord ++ tailWord_4195773) baseStart_4195773 baseEnd_4195773 := by
    simpa [prefixWord, tailWord_4195773, baseEnd_4195773] using wordTrace_append hprefix tailTrace_4195773
  have hstable : (prefixWord ++ tailWord_4195773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195773).length < 2 ^ (prefixWord ++ tailWord_4195773).sum := by decide
  have hdescent : baseEnd_4195773 < baseStart_4195773 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195783 : List Nat := [1, 1, 4, 1, 1, 3, 1, 2, 1, 5, 3]
def baseStart_4195783 : Nat := 118140960795 + 4195783 * 2 ^ 59
def prefixEnd_4195783 : Nat := 4983230072969 + 3 ^ 40 * 4195783 * 2
def baseEnd_4195783 : Nat := 2154453400963662713416451

theorem tailTrace_4195783 : CollatzResearch.WordTrace tailWord_4195783 prefixEnd_4195783 2154453400963662713416451 := by
  unfold tailWord_4195783
  simp only [CollatzResearch.WordTrace]
  refine ⟨153032778158402248531448003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102021852105601499020965335 153032778158402248531448003)
  ·
    refine ⟨229549167237603372797172005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153032778158402248531448003 229549167237603372797172005)
    ·
      refine ⟨43040468857050632399469751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229549167237603372797172005 43040468857050632399469751)
      ·
        refine ⟨64560703285575948599204627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43040468857050632399469751 64560703285575948599204627)
        ·
          refine ⟨96841054928363922898806941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64560703285575948599204627 96841054928363922898806941)
          ·
            refine ⟨36315395598136471087052603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96841054928363922898806941 36315395598136471087052603)
            ·
              refine ⟨54473093397204706630578905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36315395598136471087052603 54473093397204706630578905)
              ·
                refine ⟨40854820047903529972934179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54473093397204706630578905 40854820047903529972934179)
                ·
                  refine ⟨61282230071855294959401269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40854820047903529972934179 61282230071855294959401269)
                  ·
                    refine ⟨5745209069236433902443869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 61282230071855294959401269 5745209069236433902443869)
                    ·
                      refine ⟨2154453400963662713416451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5745209069236433902443869 2154453400963662713416451)
                      ·
                        rfl

theorem cell23_4195783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 1, 2, 1, 5, 3].length) (baseStart_4195783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195783 prefixEnd_4195783 := by exact prefixLift 4195783
  have htrace : WordTrace (prefixWord ++ tailWord_4195783) baseStart_4195783 baseEnd_4195783 := by
    simpa [prefixWord, tailWord_4195783, baseEnd_4195783] using wordTrace_append hprefix tailTrace_4195783
  have hstable : (prefixWord ++ tailWord_4195783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195783).length < 2 ^ (prefixWord ++ tailWord_4195783).sum := by decide
  have hdescent : baseEnd_4195783 < baseStart_4195783 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195790 : List Nat := [4, 1, 1, 1, 2, 1, 3, 5, 5]
def baseStart_4195790 : Nat := 118140960795 + 4195790 * 2 ^ 59
def prefixEnd_4195790 : Nat := 4983230072969 + 3 ^ 40 * 4195790 * 2
def baseEnd_4195790 : Nat := 239384110592027131780991

theorem tailTrace_4195790 : CollatzResearch.WordTrace tailWord_4195790 prefixEnd_4195790 239384110592027131780991 := by
  unfold tailWord_4195790
  simp only [CollatzResearch.WordTrace]
  refine ⟨19129129183672111090869103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102022022312917925817968549 19129129183672111090869103)
  ·
    refine ⟨28693693775508166636303655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19129129183672111090869103 28693693775508166636303655)
    ·
      refine ⟨43040540663262249954455483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28693693775508166636303655 43040540663262249954455483)
      ·
        refine ⟨64560810994893374931683225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43040540663262249954455483 64560810994893374931683225)
        ·
          refine ⟨48420608246170031198762419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64560810994893374931683225 48420608246170031198762419)
          ·
            refine ⟨72630912369255046798143629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48420608246170031198762419 72630912369255046798143629)
            ·
              refine ⟨27236592138470642549303861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72630912369255046798143629 27236592138470642549303861)
              ·
                refine ⟨2553430512981622738997237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 27236592138470642549303861 2553430512981622738997237)
                ·
                  refine ⟨239384110592027131780991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2553430512981622738997237 239384110592027131780991)
                  ·
                    rfl

theorem cell23_4195790_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 3, 5, 5].length) (baseStart_4195790 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195790 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195790 prefixEnd_4195790 := by exact prefixLift 4195790
  have htrace : WordTrace (prefixWord ++ tailWord_4195790) baseStart_4195790 baseEnd_4195790 := by
    simpa [prefixWord, tailWord_4195790, baseEnd_4195790] using wordTrace_append hprefix tailTrace_4195790
  have hstable : (prefixWord ++ tailWord_4195790).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195790).length < 2 ^ (prefixWord ++ tailWord_4195790).sum := by decide
  have hdescent : baseEnd_4195790 < baseStart_4195790 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195790) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195823 : List Nat := [1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 4]
def baseStart_4195823 : Nat := 118140960795 + 4195823 * 2 ^ 59
def prefixEnd_4195823 : Nat := 4983230072969 + 3 ^ 40 * 4195823 * 2
def baseEnd_4195823 : Nat := 2154473940189842556916267

theorem tailTrace_4195823 : CollatzResearch.WordTrace tailWord_4195823 prefixEnd_4195823 2154473940189842556916267 := by
  unfold tailWord_4195823
  simp only [CollatzResearch.WordTrace]
  refine ⟨153034237078257335362904123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102022824718838223575269415 153034237078257335362904123)
  ·
    refine ⟨229551355617386003044356185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153034237078257335362904123 229551355617386003044356185)
    ·
      refine ⟨172163516713039502283267139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229551355617386003044356185 172163516713039502283267139)
      ·
        refine ⟨258245275069559253424900709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172163516713039502283267139 258245275069559253424900709)
        ·
          refine ⟨48420989075542360017168883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 258245275069559253424900709 48420989075542360017168883)
          ·
            refine ⟨72631483613313540025753325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48420989075542360017168883 72631483613313540025753325)
            ·
              refine ⟨27236806354992577509657497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 72631483613313540025753325 27236806354992577509657497)
              ·
                refine ⟨20427604766244433132243123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 27236806354992577509657497 20427604766244433132243123)
                ·
                  refine ⟨30641407149366649698364685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20427604766244433132243123 30641407149366649698364685)
                  ·
                    refine ⟨11490527681012493636886757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30641407149366649698364685 11490527681012493636886757)
                    ·
                      refine ⟨2154473940189842556916267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11490527681012493636886757 2154473940189842556916267)
                      ·
                        rfl

theorem cell23_4195823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 3, 2, 1, 3, 4].length) (baseStart_4195823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195823 prefixEnd_4195823 := by exact prefixLift 4195823
  have htrace : WordTrace (prefixWord ++ tailWord_4195823) baseStart_4195823 baseEnd_4195823 := by
    simpa [prefixWord, tailWord_4195823, baseEnd_4195823] using wordTrace_append hprefix tailTrace_4195823
  have hstable : (prefixWord ++ tailWord_4195823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195823).length < 2 ^ (prefixWord ++ tailWord_4195823).sum := by decide
  have hdescent : baseEnd_4195823 < baseStart_4195823 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195940 : List Nat := [2, 3, 1, 1, 2, 3, 1, 3, 1, 6]
def baseStart_4195940 : Nat := 118140960795 + 4195940 * 2 ^ 59
def prefixEnd_4195940 : Nat := 4983230072969 + 3 ^ 40 * 4195940 * 2
def baseEnd_4195940 : Nat := 718178005808806199717743

theorem tailTrace_4195940 : CollatzResearch.WordTrace tailWord_4195940 prefixEnd_4195940 718178005808806199717743 := by
  unfold tailWord_4195940
  simp only [CollatzResearch.WordTrace]
  refine ⟨76519252209416732172456637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102025669612555642896608849 76519252209416732172456637)
  ·
    refine ⟨28694719578531274564671239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 76519252209416732172456637 28694719578531274564671239)
    ·
      refine ⟨43042079367796911847006859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28694719578531274564671239 43042079367796911847006859)
      ·
        refine ⟨64563119051695367770510289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43042079367796911847006859 64563119051695367770510289)
        ·
          refine ⟨48422339288771525827882717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64563119051695367770510289 48422339288771525827882717)
          ·
            refine ⟨18158377233289322185456019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 48422339288771525827882717 18158377233289322185456019)
            ·
              refine ⟨27237565849933983278184029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18158377233289322185456019 27237565849933983278184029)
              ·
                refine ⟨10214087193725243729319011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27237565849933983278184029 10214087193725243729319011)
                ·
                  refine ⟨15321130790587865593978517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10214087193725243729319011 15321130790587865593978517)
                  ·
                    refine ⟨718178005808806199717743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15321130790587865593978517 718178005808806199717743)
                    ·
                      rfl

theorem cell23_4195940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_4195940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195940 prefixEnd_4195940 := by exact prefixLift 4195940
  have htrace : WordTrace (prefixWord ++ tailWord_4195940) baseStart_4195940 baseEnd_4195940 := by
    simpa [prefixWord, tailWord_4195940, baseEnd_4195940] using wordTrace_append hprefix tailTrace_4195940
  have hstable : (prefixWord ++ tailWord_4195940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195940).length < 2 ^ (prefixWord ++ tailWord_4195940).sum := by decide
  have hdescent : baseEnd_4195940 < baseStart_4195940 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195953 : List Nat := [1, 2, 2, 2, 1, 1, 1, 13]
def baseStart_4195953 : Nat := 118140960795 + 4195953 * 2 ^ 59
def prefixEnd_4195953 : Nat := 4983230072969 + 3 ^ 40 * 4195953 * 2
def baseEnd_4195953 : Nat := 79797803432404705492247

theorem tailTrace_4195953 : CollatzResearch.WordTrace tailWord_4195953 prefixEnd_4195953 79797803432404705492247 := by
  unfold tailWord_4195953
  simp only [CollatzResearch.WordTrace]
  refine ⟨153038978567786367565136513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102025985711857578376757675 153038978567786367565136513)
  ·
    refine ⟨114779233925839775673852385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153038978567786367565136513 114779233925839775673852385)
    ·
      refine ⟨86084425444379831755389289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114779233925839775673852385 86084425444379831755389289)
      ·
        refine ⟨64563319083284873816541967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 86084425444379831755389289 64563319083284873816541967)
        ·
          refine ⟨96844978624927310724812951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 64563319083284873816541967 96844978624927310724812951)
          ·
            refine ⟨145267467937390966087219427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96844978624927310724812951 145267467937390966087219427)
            ·
              refine ⟨217901201906086449130829141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 145267467937390966087219427 217901201906086449130829141)
              ·
                refine ⟨79797803432404705492247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 217901201906086449130829141 79797803432404705492247)
                ·
                  rfl

theorem cell23_4195953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 1, 13].length) (baseStart_4195953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195953 prefixEnd_4195953 := by exact prefixLift 4195953
  have htrace : WordTrace (prefixWord ++ tailWord_4195953) baseStart_4195953 baseEnd_4195953 := by
    simpa [prefixWord, tailWord_4195953, baseEnd_4195953] using wordTrace_append hprefix tailTrace_4195953
  have hstable : (prefixWord ++ tailWord_4195953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195953).length < 2 ^ (prefixWord ++ tailWord_4195953).sum := by decide
  have hdescent : baseEnd_4195953 < baseStart_4195953 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195957 : List Nat := [1, 3, 4, 2, 1, 1, 2, 2, 1, 6]
def baseStart_4195957 : Nat := 118140960795 + 4195957 * 2 ^ 59
def prefixEnd_4195957 : Nat := 4983230072969 + 3 ^ 40 * 4195957 * 2
def baseEnd_4195957 : Nat := 718180915532515010880217

theorem tailTrace_4195957 : CollatzResearch.WordTrace tailWord_4195957 prefixEnd_4195957 718180915532515010880217 := by
  unfold tailWord_4195957
  simp only [CollatzResearch.WordTrace]
  refine ⟨153039124459771876248282125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102026082973181250832188083 153039124459771876248282125)
  ·
    refine ⟨57389671672414453593105797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153039124459771876248282125 57389671672414453593105797)
    ·
      refine ⟨10760563438577710048707337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 57389671672414453593105797 10760563438577710048707337)
      ·
        refine ⟨8070422578933282536530503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 10760563438577710048707337 8070422578933282536530503)
        ·
          refine ⟨12105633868399923804795755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8070422578933282536530503 12105633868399923804795755)
          ·
            refine ⟨18158450802599885707193633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12105633868399923804795755 18158450802599885707193633)
            ·
              refine ⟨13618838101949914280395225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18158450802599885707193633 13618838101949914280395225)
              ·
                refine ⟨10214128576462435710296419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13618838101949914280395225 10214128576462435710296419)
                ·
                  refine ⟨15321192864693653565444629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10214128576462435710296419 15321192864693653565444629)
                  ·
                    refine ⟨718180915532515010880217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15321192864693653565444629 718180915532515010880217)
                    ·
                      rfl

theorem cell23_4195957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 2, 2, 1, 6].length) (baseStart_4195957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195957 prefixEnd_4195957 := by exact prefixLift 4195957
  have htrace : WordTrace (prefixWord ++ tailWord_4195957) baseStart_4195957 baseEnd_4195957 := by
    simpa [prefixWord, tailWord_4195957, baseEnd_4195957] using wordTrace_append hprefix tailTrace_4195957
  have hstable : (prefixWord ++ tailWord_4195957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195957).length < 2 ^ (prefixWord ++ tailWord_4195957).sum := by decide
  have hdescent : baseEnd_4195957 < baseStart_4195957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4195958 : List Nat := [5, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3]
def baseStart_4195958 : Nat := 118140960795 + 4195958 * 2 ^ 59
def prefixEnd_4195958 : Nat := 4983230072969 + 3 ^ 40 * 4195958 * 2
def baseEnd_4195958 : Nat := 2154543260078199528728147

theorem tailTrace_4195958 : CollatzResearch.WordTrace tailWord_4195958 prefixEnd_4195958 2154543260078199528728147 := by
  unfold tailWord_4195958
  simp only [CollatzResearch.WordTrace]
  refine ⟨9564947558298015838691783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 102026107288512168946045685 9564947558298015838691783)
  ·
    refine ⟨14347421337447023758037675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 9564947558298015838691783 14347421337447023758037675)
    ·
      refine ⟨21521132006170535637056513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14347421337447023758037675 21521132006170535637056513)
      ·
        refine ⟨16140849004627901727792385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21521132006170535637056513 16140849004627901727792385)
        ·
          refine ⟨12105636753470926295844289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16140849004627901727792385 12105636753470926295844289)
          ·
            refine ⟨9079227565103194721883217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12105636753470926295844289 9079227565103194721883217)
            ·
              refine ⟨6809420673827396041412413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9079227565103194721883217 6809420673827396041412413)
              ·
                refine ⟨2553532752685273515529655, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6809420673827396041412413 2553532752685273515529655)
                ·
                  refine ⟨3830299129027910273294483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2553532752685273515529655 3830299129027910273294483)
                  ·
                    refine ⟨5745448693541865409941725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3830299129027910273294483 5745448693541865409941725)
                    ·
                      refine ⟨2154543260078199528728147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5745448693541865409941725 2154543260078199528728147)
                      ·
                        rfl

theorem cell23_4195958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3].length) (baseStart_4195958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4195958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4195958 prefixEnd_4195958 := by exact prefixLift 4195958
  have htrace : WordTrace (prefixWord ++ tailWord_4195958) baseStart_4195958 baseEnd_4195958 := by
    simpa [prefixWord, tailWord_4195958, baseEnd_4195958] using wordTrace_append hprefix tailTrace_4195958
  have hstable : (prefixWord ++ tailWord_4195958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4195958).length < 2 ^ (prefixWord ++ tailWord_4195958).sum := by decide
  have hdescent : baseEnd_4195958 < baseStart_4195958 := by decide
  rcases family_descends (prefixWord ++ tailWord_4195958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196037 : List Nat := [1, 3, 1, 1, 1, 1, 2, 4, 3, 4, 2]
def baseStart_4196037 : Nat := 118140960795 + 4196037 * 2 ^ 59
def prefixEnd_4196037 : Nat := 4983230072969 + 3 ^ 40 * 4196037 * 2
def baseEnd_4196037 : Nat := 2154583825049904719640283

theorem tailTrace_4196037 : CollatzResearch.WordTrace tailWord_4196037 prefixEnd_4196037 2154583825049904719640283 := by
  unfold tailWord_4196037
  simp only [CollatzResearch.WordTrace]
  refine ⟨153042042299482049911194365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102028028199654699940796243 153042042299482049911194365)
  ·
    refine ⟨57390765862305768716697887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153042042299482049911194365 57390765862305768716697887)
    ·
      refine ⟨86086148793458653075046831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57390765862305768716697887 86086148793458653075046831)
      ·
        refine ⟨129129223190187979612570247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86086148793458653075046831 129129223190187979612570247)
        ·
          refine ⟨193693834785281969418855371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129129223190187979612570247 193693834785281969418855371)
          ·
            refine ⟨290540752177922954128283057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193693834785281969418855371 290540752177922954128283057)
            ·
              refine ⟨217905564133442215596212293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290540752177922954128283057 217905564133442215596212293)
              ·
                refine ⟨40857293275020415424289805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 217905564133442215596212293 40857293275020415424289805)
                ·
                  refine ⟨15321484978132655784108677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40857293275020415424289805 15321484978132655784108677)
                  ·
                    refine ⟨2872778433399872959520377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15321484978132655784108677 2872778433399872959520377)
                    ·
                      refine ⟨2154583825049904719640283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2872778433399872959520377 2154583825049904719640283)
                      ·
                        rfl

theorem cell23_4196037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 2, 4, 3, 4, 2].length) (baseStart_4196037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196037 prefixEnd_4196037 := by exact prefixLift 4196037
  have htrace : WordTrace (prefixWord ++ tailWord_4196037) baseStart_4196037 baseEnd_4196037 := by
    simpa [prefixWord, tailWord_4196037, baseEnd_4196037] using wordTrace_append hprefix tailTrace_4196037
  have hstable : (prefixWord ++ tailWord_4196037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196037).length < 2 ^ (prefixWord ++ tailWord_4196037).sum := by decide
  have hdescent : baseEnd_4196037 < baseStart_4196037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196040 : List Nat := [2, 1, 3, 1, 2, 2, 1, 2, 1, 3, 5]
def baseStart_4196040 : Nat := 118140960795 + 4196040 * 2 ^ 59
def prefixEnd_4196040 : Nat := 4983230072969 + 3 ^ 40 * 4196040 * 2
def baseEnd_4196040 : Nat := 2154585365491868207902769

theorem tailTrace_4196040 : CollatzResearch.WordTrace tailWord_4196040 prefixEnd_4196040 2154585365491868207902769 := by
  unfold tailWord_4196040
  simp only [CollatzResearch.WordTrace]
  refine ⟨76521075859235590711776787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102028101145647454282369049 76521075859235590711776787)
  ·
    refine ⟨114781613788853386067665181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76521075859235590711776787 114781613788853386067665181)
    ·
      refine ⟨43043105170820019775374443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114781613788853386067665181 43043105170820019775374443)
      ·
        refine ⟨64564657756230029663061665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43043105170820019775374443 64564657756230029663061665)
        ·
          refine ⟨48423493317172522247296249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64564657756230029663061665 48423493317172522247296249)
          ·
            refine ⟨36317619987879391685472187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48423493317172522247296249 36317619987879391685472187)
            ·
              refine ⟨54476429981819087528208281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36317619987879391685472187 54476429981819087528208281)
              ·
                refine ⟨40857322486364315646156211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54476429981819087528208281 40857322486364315646156211)
                ·
                  refine ⟨61285983729546473469234317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 40857322486364315646156211 61285983729546473469234317)
                  ·
                    refine ⟨22982243898579927550962869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 61285983729546473469234317 22982243898579927550962869)
                    ·
                      refine ⟨2154585365491868207902769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22982243898579927550962869 2154585365491868207902769)
                      ·
                        rfl

theorem cell23_4196040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_4196040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196040 prefixEnd_4196040 := by exact prefixLift 4196040
  have htrace : WordTrace (prefixWord ++ tailWord_4196040) baseStart_4196040 baseEnd_4196040 := by
    simpa [prefixWord, tailWord_4196040, baseEnd_4196040] using wordTrace_append hprefix tailTrace_4196040
  have hstable : (prefixWord ++ tailWord_4196040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196040).length < 2 ^ (prefixWord ++ tailWord_4196040).sum := by decide
  have hdescent : baseEnd_4196040 < baseStart_4196040 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196090 : List Nat := [3, 1, 1, 1, 1, 3, 1, 2, 3, 7]
def baseStart_4196090 : Nat := 118140960795 + 4196090 * 2 ^ 59
def prefixEnd_4196090 : Nat := 4983230072969 + 3 ^ 40 * 4196090 * 2
def baseEnd_4196090 : Nat := 718203679841531004092513

theorem tailTrace_4196090 : CollatzResearch.WordTrace tailWord_4196090 prefixEnd_4196090 718203679841531004092513 := by
  unfold tailWord_4196090
  simp only [CollatzResearch.WordTrace]
  refine ⟨38260993842072509990718431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102029316912193359975249149 38260993842072509990718431)
  ·
    refine ⟨57391490763108764986077647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38260993842072509990718431 57391490763108764986077647)
    ·
      refine ⟨86087236144663147479116471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57391490763108764986077647 86087236144663147479116471)
      ·
        refine ⟨129130854216994721218674707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86087236144663147479116471 129130854216994721218674707)
        ·
          refine ⟨193696281325492081828012061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129130854216994721218674707 193696281325492081828012061)
          ·
            refine ⟨72636105497059530685504523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193696281325492081828012061 72636105497059530685504523)
            ·
              refine ⟨108954158245589296028256785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72636105497059530685504523 108954158245589296028256785)
              ·
                refine ⟨81715618684191972021192589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108954158245589296028256785 81715618684191972021192589)
                ·
                  refine ⟨30643357006571989507947221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81715618684191972021192589 30643357006571989507947221)
                  ·
                    refine ⟨718203679841531004092513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30643357006571989507947221 718203679841531004092513)
                    ·
                      rfl

theorem cell23_4196090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_4196090 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196090 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196090 prefixEnd_4196090 := by exact prefixLift 4196090
  have htrace : WordTrace (prefixWord ++ tailWord_4196090) baseStart_4196090 baseEnd_4196090 := by
    simpa [prefixWord, tailWord_4196090, baseEnd_4196090] using wordTrace_append hprefix tailTrace_4196090
  have hstable : (prefixWord ++ tailWord_4196090).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196090).length < 2 ^ (prefixWord ++ tailWord_4196090).sum := by decide
  have hdescent : baseEnd_4196090 < baseStart_4196090 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196127 : List Nat := [1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 4]
def baseStart_4196127 : Nat := 118140960795 + 4196127 * 2 ^ 59
def prefixEnd_4196127 : Nat := 4983230072969 + 3 ^ 40 * 4196127 * 2
def baseEnd_4196127 : Nat := 2154630038308809367514869

theorem tailTrace_4196127 : CollatzResearch.WordTrace tailWord_4196127 prefixEnd_4196127 2154630038308809367514869 := by
  unfold tailWord_4196127
  simp only [CollatzResearch.WordTrace]
  refine ⟨153045324869155995281970635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102030216579437330187980423 153045324869155995281970635)
  ·
    refine ⟨229567987303733992922955953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153045324869155995281970635 229567987303733992922955953)
    ·
      refine ⟨172175990477800494692216965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229567987303733992922955953 172175990477800494692216965)
      ·
        refine ⟨32282998214587592754790681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 172175990477800494692216965 32282998214587592754790681)
        ·
          refine ⟨24212248660940694566093011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 32282998214587592754790681 24212248660940694566093011)
          ·
            refine ⟨36318372991411041849139517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24212248660940694566093011 36318372991411041849139517)
            ·
              refine ⟨13619389871779140693427319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36318372991411041849139517 13619389871779140693427319)
              ·
                refine ⟨20429084807668711040140979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13619389871779140693427319 20429084807668711040140979)
                ·
                  refine ⟨30643627211503066560211469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20429084807668711040140979 30643627211503066560211469)
                  ·
                    refine ⟨11491360204313649960079301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 30643627211503066560211469 11491360204313649960079301)
                    ·
                      refine ⟨2154630038308809367514869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11491360204313649960079301 2154630038308809367514869)
                      ·
                        rfl

theorem cell23_4196127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 4].length) (baseStart_4196127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196127 prefixEnd_4196127 := by exact prefixLift 4196127
  have htrace : WordTrace (prefixWord ++ tailWord_4196127) baseStart_4196127 baseEnd_4196127 := by
    simpa [prefixWord, tailWord_4196127, baseEnd_4196127] using wordTrace_append hprefix tailTrace_4196127
  have hstable : (prefixWord ++ tailWord_4196127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196127).length < 2 ^ (prefixWord ++ tailWord_4196127).sum := by decide
  have hdescent : baseEnd_4196127 < baseStart_4196127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196154 : List Nat := [3, 1, 1, 1, 5, 1, 1, 3, 3, 4]
def baseStart_4196154 : Nat := 118140960795 + 4196154 * 2 ^ 59
def prefixEnd_4196154 : Nat := 4983230072969 + 3 ^ 40 * 4196154 * 2
def baseEnd_4196154 : Nat := 718214634095493587292415

theorem tailTrace_4196154 : CollatzResearch.WordTrace tailWord_4196154 prefixEnd_4196154 718214634095493587292415 := by
  unfold tailWord_4196154
  simp only [CollatzResearch.WordTrace]
  refine ⟨38261577410014544723300879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102030873093372119262135677 38261577410014544723300879)
  ·
    refine ⟨57392366115021817084951319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38261577410014544723300879 57392366115021817084951319)
    ·
      refine ⟨86088549172532725627426979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57392366115021817084951319 86088549172532725627426979)
      ·
        refine ⟨129132823758799088441140469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86088549172532725627426979 129132823758799088441140469)
        ·
          refine ⟨12106202227387414541356919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 129132823758799088441140469 12106202227387414541356919)
          ·
            refine ⟨18159303341081121812035379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12106202227387414541356919 18159303341081121812035379)
            ·
              refine ⟨27238955011621682718053069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18159303341081121812035379 27238955011621682718053069)
              ·
                refine ⟨10214608129358131019269901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27238955011621682718053069 10214608129358131019269901)
                ·
                  refine ⟨3830478048509299132226213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10214608129358131019269901 3830478048509299132226213)
                  ·
                    refine ⟨718214634095493587292415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3830478048509299132226213 718214634095493587292415)
                    ·
                      rfl

theorem cell23_4196154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 5, 1, 1, 3, 3, 4].length) (baseStart_4196154 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196154 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196154 prefixEnd_4196154 := by exact prefixLift 4196154
  have htrace : WordTrace (prefixWord ++ tailWord_4196154) baseStart_4196154 baseEnd_4196154 := by
    simpa [prefixWord, tailWord_4196154, baseEnd_4196154] using wordTrace_append hprefix tailTrace_4196154
  have hstable : (prefixWord ++ tailWord_4196154).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196154).length < 2 ^ (prefixWord ++ tailWord_4196154).sum := by decide
  have hdescent : baseEnd_4196154 < baseStart_4196154 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196167 : List Nat := [1, 1, 4, 1, 2, 1, 2, 5, 6]
def baseStart_4196167 : Nat := 118140960795 + 4196167 * 2 ^ 59
def prefixEnd_4196167 : Nat := 4983230072969 + 3 ^ 40 * 4196167 * 2
def baseEnd_4196167 : Nat := 239405619726109912334965

theorem tailTrace_4196167 : CollatzResearch.WordTrace tailWord_4196167 prefixEnd_4196167 239405619726109912334965 := by
  unfold tailWord_4196167
  simp only [CollatzResearch.WordTrace]
  refine ⟨153046783789011082113426755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102031189192674054742284503 153046783789011082113426755)
  ·
    refine ⟨229570175683516623170140133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153046783789011082113426755 229570175683516623170140133)
    ·
      refine ⟨43044407940659366844401275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229570175683516623170140133 43044407940659366844401275)
      ·
        refine ⟨64566611910989050266601913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43044407940659366844401275 64566611910989050266601913)
        ·
          refine ⟨48424958933241787699951435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64566611910989050266601913 48424958933241787699951435)
          ·
            refine ⟨72637438399862681549927153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48424958933241787699951435 72637438399862681549927153)
            ·
              refine ⟨54478078799897011162445365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72637438399862681549927153 54478078799897011162445365)
              ·
                refine ⟨5107319887490344796479253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 54478078799897011162445365 5107319887490344796479253)
                ·
                  refine ⟨239405619726109912334965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5107319887490344796479253 239405619726109912334965)
                  ·
                    rfl

theorem cell23_4196167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 2, 5, 6].length) (baseStart_4196167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196167 prefixEnd_4196167 := by exact prefixLift 4196167
  have htrace : WordTrace (prefixWord ++ tailWord_4196167) baseStart_4196167 baseEnd_4196167 := by
    simpa [prefixWord, tailWord_4196167, baseEnd_4196167] using wordTrace_append hprefix tailTrace_4196167
  have hstable : (prefixWord ++ tailWord_4196167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196167).length < 2 ^ (prefixWord ++ tailWord_4196167).sum := by decide
  have hdescent : baseEnd_4196167 < baseStart_4196167 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196197 : List Nat := [1, 3, 1, 3, 1, 1, 1, 2, 5, 5]
def baseStart_4196197 : Nat := 118140960795 + 4196197 * 2 ^ 59
def prefixEnd_4196197 : Nat := 4983230072969 + 3 ^ 40 * 4196197 * 2
def baseEnd_4196197 : Nat := 718221993984874697879849

theorem tailTrace_4196197 : CollatzResearch.WordTrace tailWord_4196197 prefixEnd_4196197 718221993984874697879849 := by
  unfold tailWord_4196197
  simp only [CollatzResearch.WordTrace]
  refine ⟨153047877978902397237018845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102031918652601598158012563 153047877978902397237018845)
  ·
    refine ⟨57392954242088398963882067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 153047877978902397237018845 57392954242088398963882067)
    ·
      refine ⟨86089431363132598445823101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57392954242088398963882067 86089431363132598445823101)
      ·
        refine ⟨32283536761174724417183663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 86089431363132598445823101 32283536761174724417183663)
        ·
          refine ⟨48425305141762086625775495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32283536761174724417183663 48425305141762086625775495)
          ·
            refine ⟨72637957712643129938663243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48425305141762086625775495 72637957712643129938663243)
            ·
              refine ⟨108956936568964694907994865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 72637957712643129938663243 108956936568964694907994865)
              ·
                refine ⟨81717702426723521180996149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 108956936568964694907994865 81717702426723521180996149)
                ·
                  refine ⟨7661034602505330110718389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 81717702426723521180996149 7661034602505330110718389)
                  ·
                    refine ⟨718221993984874697879849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 7661034602505330110718389 718221993984874697879849)
                    ·
                      rfl

theorem cell23_4196197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 2, 5, 5].length) (baseStart_4196197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196197 prefixEnd_4196197 := by exact prefixLift 4196197
  have htrace : WordTrace (prefixWord ++ tailWord_4196197) baseStart_4196197 baseEnd_4196197 := by
    simpa [prefixWord, tailWord_4196197, baseEnd_4196197] using wordTrace_append hprefix tailTrace_4196197
  have hstable : (prefixWord ++ tailWord_4196197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196197).length < 2 ^ (prefixWord ++ tailWord_4196197).sum := by decide
  have hdescent : baseEnd_4196197 < baseStart_4196197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196244 : List Nat := [2, 4, 2, 1, 1, 2, 1, 1, 3, 6]
def baseStart_4196244 : Nat := 118140960795 + 4196244 * 2 ^ 59
def prefixEnd_4196244 : Nat := 4983230072969 + 3 ^ 40 * 4196244 * 2
def baseEnd_4196244 : Nat := 718230038515128469917277

theorem tailTrace_4196244 : CollatzResearch.WordTrace tailWord_4196244 prefixEnd_4196244 718230038515128469917277 := by
  unfold tailWord_4196244
  simp only [CollatzResearch.WordTrace]
  refine ⟨76524796104866062131989893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102033061473154749509319857 76524796104866062131989893)
  ·
    refine ⟨14348399269662386649748105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 76524796104866062131989893 14348399269662386649748105)
    ·
      refine ⟨10761299452246789987311079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14348399269662386649748105 10761299452246789987311079)
      ·
        refine ⟨16141949178370184980966619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10761299452246789987311079 16141949178370184980966619)
        ·
          refine ⟨24212923767555277471449929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16141949178370184980966619 24212923767555277471449929)
          ·
            refine ⟨18159692825666458103587447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 24212923767555277471449929 18159692825666458103587447)
            ·
              refine ⟨27239539238499687155381171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 18159692825666458103587447 27239539238499687155381171)
              ·
                refine ⟨40859308857749530733071757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 27239539238499687155381171 40859308857749530733071757)
                ·
                  refine ⟨15322240821656074024901909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 40859308857749530733071757 15322240821656074024901909)
                  ·
                    refine ⟨718230038515128469917277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 15322240821656074024901909 718230038515128469917277)
                    ·
                      rfl

theorem cell23_4196244_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_4196244 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196244 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196244 prefixEnd_4196244 := by exact prefixLift 4196244
  have htrace : WordTrace (prefixWord ++ tailWord_4196244) baseStart_4196244 baseEnd_4196244 := by
    simpa [prefixWord, tailWord_4196244, baseEnd_4196244] using wordTrace_append hprefix tailTrace_4196244
  have hstable : (prefixWord ++ tailWord_4196244).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196244).length < 2 ^ (prefixWord ++ tailWord_4196244).sum := by decide
  have hdescent : baseEnd_4196244 < baseStart_4196244 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196244) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196257 : List Nat := [1, 2, 3, 4, 13]
def baseStart_4196257 : Nat := 118140960795 + 4196257 * 2 ^ 59
def prefixEnd_4196257 : Nat := 4983230072969 + 3 ^ 40 * 4196257 * 2
def baseEnd_4196257 : Nat := 2955688327563640409999

theorem tailTrace_4196257 : CollatzResearch.WordTrace tailWord_4196257 prefixEnd_4196257 2955688327563640409999 := by
  unfold tailWord_4196257
  simp only [CollatzResearch.WordTrace]
  refine ⟨153050066358685027484203025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102033377572456684989468683 153050066358685027484203025)
  ·
    refine ⟨114787549769013770613152269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153050066358685027484203025 114787549769013770613152269)
    ·
      refine ⟨43045331163380163979932101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114787549769013770613152269 43045331163380163979932101)
      ·
        refine ⟨8070999593133780746237269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43045331163380163979932101 8070999593133780746237269)
        ·
          refine ⟨2955688327563640409999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 8070999593133780746237269 2955688327563640409999)
          ·
            rfl

theorem cell23_4196257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 13].length) (baseStart_4196257 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196257 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196257 prefixEnd_4196257 := by exact prefixLift 4196257
  have htrace : WordTrace (prefixWord ++ tailWord_4196257) baseStart_4196257 baseEnd_4196257 := by
    simpa [prefixWord, tailWord_4196257, baseEnd_4196257] using wordTrace_append hprefix tailTrace_4196257
  have hstable : (prefixWord ++ tailWord_4196257).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196257).length < 2 ^ (prefixWord ++ tailWord_4196257).sum := by decide
  have hdescent : baseEnd_4196257 < baseStart_4196257 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196287 : List Nat := [1, 1, 2, 2, 2, 1, 3, 2, 2, 7]
def baseStart_4196287 : Nat := 118140960795 + 4196287 * 2 ^ 59
def prefixEnd_4196287 : Nat := 4983230072969 + 3 ^ 40 * 4196287 * 2
def baseEnd_4196287 : Nat := 718237398404509580504711

theorem tailTrace_4196287 : CollatzResearch.WordTrace tailWord_4196287 prefixEnd_4196287 718237398404509580504711 := by
  unfold tailWord_4196287
  simp only [CollatzResearch.WordTrace]
  refine ⟨153051160548576342607795115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102034107032384228405196743 153051160548576342607795115)
  ·
    refine ⟨229576740822864513911692673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153051160548576342607795115 229576740822864513911692673)
    ·
      refine ⟨172182555617148385433769505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229576740822864513911692673 172182555617148385433769505)
      ·
        refine ⟨129136916712861289075327129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172182555617148385433769505 129136916712861289075327129)
        ·
          refine ⟨96852687534645966806495347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129136916712861289075327129 96852687534645966806495347)
          ·
            refine ⟨145279031301968950209743021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96852687534645966806495347 145279031301968950209743021)
            ·
              refine ⟨54479636738238356328653633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 145279031301968950209743021 54479636738238356328653633)
              ·
                refine ⟨40859727553678767246490225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54479636738238356328653633 40859727553678767246490225)
                ·
                  refine ⟨30644795665259075434867669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40859727553678767246490225 30644795665259075434867669)
                  ·
                    refine ⟨718237398404509580504711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 30644795665259075434867669 718237398404509580504711)
                    ·
                      rfl

theorem cell23_4196287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 3, 2, 2, 7].length) (baseStart_4196287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196287 prefixEnd_4196287 := by exact prefixLift 4196287
  have htrace : WordTrace (prefixWord ++ tailWord_4196287) baseStart_4196287 baseEnd_4196287 := by
    simpa [prefixWord, tailWord_4196287, baseEnd_4196287] using wordTrace_append hprefix tailTrace_4196287
  have hstable : (prefixWord ++ tailWord_4196287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196287).length < 2 ^ (prefixWord ++ tailWord_4196287).sum := by decide
  have hdescent : baseEnd_4196287 < baseStart_4196287 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196297 : List Nat := [1, 2, 1, 1, 2, 1, 2, 3, 1, 4, 5]
def baseStart_4196297 : Nat := 118140960795 + 4196297 * 2 ^ 59
def prefixEnd_4196297 : Nat := 4983230072969 + 3 ^ 40 * 4196297 * 2
def baseEnd_4196297 : Nat := 2154717330020073702389087

theorem tailTrace_4196297 : CollatzResearch.WordTrace tailWord_4196297 prefixEnd_4196297 2154717330020073702389087 := by
  unfold tailWord_4196297
  simp only [CollatzResearch.WordTrace]
  refine ⟨153051525278540114315659145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102034350185693409543772763 153051525278540114315659145)
  ·
    refine ⟨114788643958905085736744359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153051525278540114315659145 114788643958905085736744359)
    ·
      refine ⟨172182965938357628605116539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114788643958905085736744359 172182965938357628605116539)
      ·
        refine ⟨258274448907536442907674809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172182965938357628605116539 258274448907536442907674809)
        ·
          refine ⟨193705836680652332180756107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 258274448907536442907674809 193705836680652332180756107)
          ·
            refine ⟨290558755020978498271134161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193705836680652332180756107 290558755020978498271134161)
            ·
              refine ⟨217919066265733873703350621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290558755020978498271134161 217919066265733873703350621)
              ·
                refine ⟨81719649849650202638756483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217919066265733873703350621 81719649849650202638756483)
                ·
                  refine ⟨122579474774475303958134725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81719649849650202638756483 122579474774475303958134725)
                  ·
                    refine ⟨22983651520214119492150261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 122579474774475303958134725 22983651520214119492150261)
                    ·
                      refine ⟨2154717330020073702389087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22983651520214119492150261 2154717330020073702389087)
                      ·
                        rfl

theorem cell23_4196297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 4, 5].length) (baseStart_4196297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196297 prefixEnd_4196297 := by exact prefixLift 4196297
  have htrace : WordTrace (prefixWord ++ tailWord_4196297) baseStart_4196297 baseEnd_4196297 := by
    simpa [prefixWord, tailWord_4196297, baseEnd_4196297] using wordTrace_append hprefix tailTrace_4196297
  have hstable : (prefixWord ++ tailWord_4196297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196297).length < 2 ^ (prefixWord ++ tailWord_4196297).sum := by decide
  have hdescent : baseEnd_4196297 < baseStart_4196297 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196344 : List Nat := [2, 1, 2, 1, 1, 3, 2, 2, 2, 4, 3]
def baseStart_4196344 : Nat := 118140960795 + 4196344 * 2 ^ 59
def prefixEnd_4196344 : Nat := 4983230072969 + 3 ^ 40 * 4196344 * 2
def baseEnd_4196344 : Nat := 2154741463610835018501371

theorem tailTrace_4196344 : CollatzResearch.WordTrace tailWord_4196344 prefixEnd_4196344 2154741463610835018501371 := by
  unfold tailWord_4196344
  simp only [CollatzResearch.WordTrace]
  refine ⟨76526619754684920671310043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102035493006246560895080057 76526619754684920671310043)
  ·
    refine ⟨114789929632027381006965065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76526619754684920671310043 114789929632027381006965065)
    ·
      refine ⟨86092447224020535755223799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 114789929632027381006965065 86092447224020535755223799)
      ·
        refine ⟨129138670836030803632835699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86092447224020535755223799 129138670836030803632835699)
        ·
          refine ⟨193708006254046205449253549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129138670836030803632835699 193708006254046205449253549)
          ·
            refine ⟨72640502345267327043470081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 193708006254046205449253549 72640502345267327043470081)
            ·
              refine ⟨54480376758950495282602561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72640502345267327043470081 54480376758950495282602561)
              ·
                refine ⟨40860282569212871461951921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54480376758950495282602561 40860282569212871461951921)
                ·
                  refine ⟨30645211926909653596463941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 40860282569212871461951921 30645211926909653596463941)
                  ·
                    refine ⟨5745977236295560049336989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 30645211926909653596463941 5745977236295560049336989)
                    ·
                      refine ⟨2154741463610835018501371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5745977236295560049336989 2154741463610835018501371)
                      ·
                        rfl

theorem cell23_4196344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 2, 2, 2, 4, 3].length) (baseStart_4196344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196344 prefixEnd_4196344 := by exact prefixLift 4196344
  have htrace : WordTrace (prefixWord ++ tailWord_4196344) baseStart_4196344 baseEnd_4196344 := by
    simpa [prefixWord, tailWord_4196344, baseEnd_4196344] using wordTrace_append hprefix tailTrace_4196344
  have hstable : (prefixWord ++ tailWord_4196344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196344).length < 2 ^ (prefixWord ++ tailWord_4196344).sum := by decide
  have hdescent : baseEnd_4196344 < baseStart_4196344 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196381 : List Nat := [1, 4, 2, 2, 2, 1, 3, 1, 7]
def baseStart_4196381 : Nat := 118140960795 + 4196381 * 2 ^ 59
def prefixEnd_4196381 : Nat := 4983230072969 + 3 ^ 40 * 4196381 * 2
def baseEnd_4196381 : Nat := 239417829155005708193189

theorem tailTrace_4196381 : CollatzResearch.WordTrace tailWord_4196381 prefixEnd_4196381 239417829155005708193189 := by
  unfold tailWord_4196381
  simp only [CollatzResearch.WordTrace]
  refine ⟨153054589010235796661716997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102036392673490531107811331 153054589010235796661716997)
  ·
    refine ⟨28697735439419211874071937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 153054589010235796661716997 28697735439419211874071937)
    ·
      refine ⟨21523301579564408905553953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 28697735439419211874071937 21523301579564408905553953)
      ·
        refine ⟨16142476184673306679165465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21523301579564408905553953 16142476184673306679165465)
        ·
          refine ⟨12106857138504980009374099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16142476184673306679165465 12106857138504980009374099)
          ·
            refine ⟨18160285707757470014061149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12106857138504980009374099 18160285707757470014061149)
            ·
              refine ⟨6810107140409051255272931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18160285707757470014061149 6810107140409051255272931)
              ·
                refine ⟨10215160710613576882909397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6810107140409051255272931 10215160710613576882909397)
                ·
                  refine ⟨239417829155005708193189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10215160710613576882909397 239417829155005708193189)
                  ·
                    rfl

theorem cell23_4196381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 3, 1, 7].length) (baseStart_4196381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196381 prefixEnd_4196381 := by exact prefixLift 4196381
  have htrace : WordTrace (prefixWord ++ tailWord_4196381) baseStart_4196381 baseEnd_4196381 := by
    simpa [prefixWord, tailWord_4196381, baseEnd_4196381] using wordTrace_append hprefix tailTrace_4196381
  have hstable : (prefixWord ++ tailWord_4196381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196381).length < 2 ^ (prefixWord ++ tailWord_4196381).sum := by decide
  have hdescent : baseEnd_4196381 < baseStart_4196381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196431 : List Nat := [1, 1, 2, 1, 1, 2, 2, 3, 4, 4, 2]
def baseStart_4196431 : Nat := 118140960795 + 4196431 * 2 ^ 59
def prefixEnd_4196431 : Nat := 4983230072969 + 3 ^ 40 * 4196431 * 2
def baseEnd_4196431 : Nat := 2154786136427776178113471

theorem tailTrace_4196431 : CollatzResearch.WordTrace tailWord_4196431 prefixEnd_4196431 2154786136427776178113471 := by
  unfold tailWord_4196431
  simp only [CollatzResearch.WordTrace]
  refine ⟨153056412660054655201037147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102037608440036436800691431 153056412660054655201037147)
  ·
    refine ⟨229584618990081982801555721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153056412660054655201037147 229584618990081982801555721)
    ·
      refine ⟨172188464242561487101166791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 229584618990081982801555721 172188464242561487101166791)
      ·
        refine ⟨258282696363842230651750187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 172188464242561487101166791 258282696363842230651750187)
        ·
          refine ⟨387424044545763345977625281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258282696363842230651750187 387424044545763345977625281)
          ·
            refine ⟨290568033409322509483218961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 387424044545763345977625281 290568033409322509483218961)
            ·
              refine ⟨217926025056991882112414221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 290568033409322509483218961 217926025056991882112414221)
              ·
                refine ⟨81722259396371955792155333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 217926025056991882112414221 81722259396371955792155333)
                ·
                  refine ⟨15322923636819741711029125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 81722259396371955792155333 15322923636819741711029125)
                  ·
                    refine ⟨2873048181903701570817961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15322923636819741711029125 2873048181903701570817961)
                    ·
                      refine ⟨2154786136427776178113471, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2873048181903701570817961 2154786136427776178113471)
                      ·
                        rfl

theorem cell23_4196431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 3, 4, 4, 2].length) (baseStart_4196431 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196431 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196431 prefixEnd_4196431 := by exact prefixLift 4196431
  have htrace : WordTrace (prefixWord ++ tailWord_4196431) baseStart_4196431 baseEnd_4196431 := by
    simpa [prefixWord, tailWord_4196431, baseEnd_4196431] using wordTrace_append hprefix tailTrace_4196431
  have hstable : (prefixWord ++ tailWord_4196431).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196431).length < 2 ^ (prefixWord ++ tailWord_4196431).sum := by decide
  have hdescent : baseEnd_4196431 < baseStart_4196431 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196441 : List Nat := [1, 2, 1, 2, 2, 1, 4, 3, 3, 4]
def baseStart_4196441 : Nat := 118140960795 + 4196441 * 2 ^ 59
def prefixEnd_4196441 : Nat := 4983230072969 + 3 ^ 40 * 4196441 * 2
def baseEnd_4196441 : Nat := 718263757078107046329475

theorem tailTrace_4196441 : CollatzResearch.WordTrace tailWord_4196441 prefixEnd_4196441 718263757078107046329475 := by
  unfold tailWord_4196441
  simp only [CollatzResearch.WordTrace]
  refine ⟨153056777390018426908901177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102037851593345617939267451 153056777390018426908901177)
  ·
    refine ⟨114792583042513820181675883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 153056777390018426908901177 114792583042513820181675883)
    ·
      refine ⟨172188874563770730272513825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114792583042513820181675883 172188874563770730272513825)
      ·
        refine ⟨129141655922828047704385369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 172188874563770730272513825 129141655922828047704385369)
        ·
          refine ⟨96856241942121035778289027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129141655922828047704385369 96856241942121035778289027)
          ·
            refine ⟨145284362913181553667433541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 96856241942121035778289027 145284362913181553667433541)
            ·
              refine ⟨27240818046221541312643789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 145284362913181553667433541 27240818046221541312643789)
              ·
                refine ⟨10215306767333077992241421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 27240818046221541312643789 10215306767333077992241421)
                ·
                  refine ⟨3830740037749904247090533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10215306767333077992241421 3830740037749904247090533)
                  ·
                    refine ⟨718263757078107046329475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3830740037749904247090533 718263757078107046329475)
                    ·
                      rfl

theorem cell23_4196441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 4, 3, 3, 4].length) (baseStart_4196441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196441 prefixEnd_4196441 := by exact prefixLift 4196441
  have htrace : WordTrace (prefixWord ++ tailWord_4196441) baseStart_4196441 baseEnd_4196441 := by
    simpa [prefixWord, tailWord_4196441, baseEnd_4196441] using wordTrace_append hprefix tailTrace_4196441
  have hstable : (prefixWord ++ tailWord_4196441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196441).length < 2 ^ (prefixWord ++ tailWord_4196441).sum := by decide
  have hdescent : baseEnd_4196441 < baseStart_4196441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196448 : List Nat := [2, 1, 1, 3, 2, 4, 1, 1, 2, 4, 2]
def baseStart_4196448 : Nat := 118140960795 + 4196448 * 2 ^ 59
def prefixEnd_4196448 : Nat := 4983230072969 + 3 ^ 40 * 4196448 * 2
def baseEnd_4196448 : Nat := 2154794865598902611600893

theorem tailTrace_4196448 : CollatzResearch.WordTrace tailWord_4196448 prefixEnd_4196448 2154794865598902611600893 := by
  unfold tailWord_4196448
  simp only [CollatzResearch.WordTrace]
  refine ⟨76528516350496533552202999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102038021800662044736270665 76528516350496533552202999)
  ·
    refine ⟨114792774525744800328304499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76528516350496533552202999 114792774525744800328304499)
    ·
      refine ⟨172189161788617200492456749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 114792774525744800328304499 172189161788617200492456749)
      ·
        refine ⟨64570935670731450184671281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 172189161788617200492456749 64570935670731450184671281)
        ·
          refine ⟨48428201753048587638503461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64570935670731450184671281 48428201753048587638503461)
          ·
            refine ⟨9080287828696610182219399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 48428201753048587638503461 9080287828696610182219399)
            ·
              refine ⟨13620431743044915273329099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9080287828696610182219399 13620431743044915273329099)
              ·
                refine ⟨20430647614567372909993649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13620431743044915273329099 20430647614567372909993649)
                ·
                  refine ⟨15322985710925529682495237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 20430647614567372909993649 15322985710925529682495237)
                  ·
                    refine ⟨2873059820798536815467857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 15322985710925529682495237 2873059820798536815467857)
                    ·
                      refine ⟨2154794865598902611600893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2873059820798536815467857 2154794865598902611600893)
                      ·
                        rfl

theorem cell23_4196448_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 1, 1, 2, 4, 2].length) (baseStart_4196448 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196448 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196448 prefixEnd_4196448 := by exact prefixLift 4196448
  have htrace : WordTrace (prefixWord ++ tailWord_4196448) baseStart_4196448 baseEnd_4196448 := by
    simpa [prefixWord, tailWord_4196448, baseEnd_4196448] using wordTrace_append hprefix tailTrace_4196448
  have hstable : (prefixWord ++ tailWord_4196448).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196448).length < 2 ^ (prefixWord ++ tailWord_4196448).sum := by decide
  have hdescent : baseEnd_4196448 < baseStart_4196448 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196448) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196451 : List Nat := [1, 1, 1, 5, 1, 1, 2, 2, 4, 2, 3]
def baseStart_4196451 : Nat := 118140960795 + 4196451 * 2 ^ 59
def prefixEnd_4196451 : Nat := 4983230072969 + 3 ^ 40 * 4196451 * 2
def baseEnd_4196451 : Nat := 2154796406040866099863379

theorem tailTrace_4196451 : CollatzResearch.WordTrace tailWord_4196451 prefixEnd_4196451 2154796406040866099863379 := by
  unfold tailWord_4196451
  simp only [CollatzResearch.WordTrace]
  refine ⟨153057142119982198616765207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102038094746654799077843471 153057142119982198616765207)
  ·
    refine ⟨229585713179973297925147811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153057142119982198616765207 229585713179973297925147811)
    ·
      refine ⟨344378569769959946887721717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229585713179973297925147811 344378569769959946887721717)
      ·
        refine ⟨32285490915933745020723911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 344378569769959946887721717 32285490915933745020723911)
        ·
          refine ⟨48428236373900617531085867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32285490915933745020723911 48428236373900617531085867)
          ·
            refine ⟨72642354560850926296628801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 48428236373900617531085867 72642354560850926296628801)
            ·
              refine ⟨54481765920638194722471601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 72642354560850926296628801 54481765920638194722471601)
              ·
                refine ⟨40861324440478646041853701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 54481765920638194722471601 40861324440478646041853701)
                ·
                  refine ⟨7661498332589746132847569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 40861324440478646041853701 7661498332589746132847569)
                  ·
                    refine ⟨5746123749442309599635677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 7661498332589746132847569 5746123749442309599635677)
                    ·
                      refine ⟨2154796406040866099863379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5746123749442309599635677 2154796406040866099863379)
                      ·
                        rfl

theorem cell23_4196451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_4196451 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196451 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196451 prefixEnd_4196451 := by exact prefixLift 4196451
  have htrace : WordTrace (prefixWord ++ tailWord_4196451) baseStart_4196451 baseEnd_4196451 := by
    simpa [prefixWord, tailWord_4196451, baseEnd_4196451] using wordTrace_append hprefix tailTrace_4196451
  have hstable : (prefixWord ++ tailWord_4196451).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196451).length < 2 ^ (prefixWord ++ tailWord_4196451).sum := by decide
  have hdescent : baseEnd_4196451 < baseStart_4196451 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196474 : List Nat := [3, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6]
def baseStart_4196474 : Nat := 118140960795 + 4196474 * 2 ^ 59
def prefixEnd_4196474 : Nat := 4983230072969 + 3 ^ 40 * 4196474 * 2
def baseEnd_4196474 : Nat := 2154808216095919509875773

theorem tailTrace_4196474 : CollatzResearch.WordTrace tailWord_4196474 prefixEnd_4196474 2154808216095919509875773 := by
  unfold tailWord_4196474
  simp only [CollatzResearch.WordTrace]
  refine ⟨38264495249724718386213119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102038653999265915696568317 38264495249724718386213119)
  ·
    refine ⟨57396742874587077579319679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38264495249724718386213119 57396742874587077579319679)
    ·
      refine ⟨86095114311880616368979519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57396742874587077579319679 86095114311880616368979519)
      ·
        refine ⟨129142671467820924553469279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86095114311880616368979519 129142671467820924553469279)
        ·
          refine ⟨193714007201731386830203919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 129142671467820924553469279 193714007201731386830203919)
          ·
            refine ⟨290571010802597080245305879, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 193714007201731386830203919 290571010802597080245305879)
            ·
              refine ⟨435856516203895620367958819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 290571010802597080245305879 435856516203895620367958819)
              ·
                refine ⟨653784774305843430551938229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 435856516203895620367958819 653784774305843430551938229)
                ·
                  refine ⟨61292322591172821614244209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 653784774305843430551938229 61292322591172821614244209)
                  ·
                    refine ⟨45969241943379616210683157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 61292322591172821614244209 45969241943379616210683157)
                    ·
                      refine ⟨2154808216095919509875773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 45969241943379616210683157 2154808216095919509875773)
                      ·
                        rfl

theorem cell23_4196474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 5, 2, 6].length) (baseStart_4196474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196474 prefixEnd_4196474 := by exact prefixLift 4196474
  have htrace : WordTrace (prefixWord ++ tailWord_4196474) baseStart_4196474 baseEnd_4196474 := by
    simpa [prefixWord, tailWord_4196474, baseEnd_4196474] using wordTrace_append hprefix tailTrace_4196474
  have hstable : (prefixWord ++ tailWord_4196474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196474).length < 2 ^ (prefixWord ++ tailWord_4196474).sum := by decide
  have hdescent : baseEnd_4196474 < baseStart_4196474 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196488 : List Nat := [2, 1, 3, 4, 1, 1, 3, 2, 6]
def baseStart_4196488 : Nat := 118140960795 + 4196488 * 2 ^ 59
def prefixEnd_4196488 : Nat := 4983230072969 + 3 ^ 40 * 4196488 * 2
def baseEnd_4196488 : Nat := 239423933869453606122301

theorem tailTrace_4196488 : CollatzResearch.WordTrace tailWord_4196488 prefixEnd_4196488 239423933869453606122301 := by
  unfold tailWord_4196488
  simp only [CollatzResearch.WordTrace]
  refine ⟨76529245810424076967931059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102038994413898769290574745 76529245810424076967931059)
  ·
    refine ⟨114793868715636115451896589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 76529245810424076967931059 114793868715636115451896589)
    ·
      refine ⟨43047700768363543294461221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 114793868715636115451896589 43047700768363543294461221)
      ·
        refine ⟨8071443894068164367711479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 43047700768363543294461221 8071443894068164367711479)
        ·
          refine ⟨12107165841102246551567219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8071443894068164367711479 12107165841102246551567219)
          ·
            refine ⟨18160748761653369827350829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12107165841102246551567219 18160748761653369827350829)
            ·
              refine ⟨6810280785620013685256561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 18160748761653369827350829 6810280785620013685256561)
              ·
                refine ⟨5107710589215010263942421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 6810280785620013685256561 5107710589215010263942421)
                ·
                  refine ⟨239423933869453606122301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5107710589215010263942421 239423933869453606122301)
                  ·
                    rfl

theorem cell23_4196488_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 3, 2, 6].length) (baseStart_4196488 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196488 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196488 prefixEnd_4196488 := by exact prefixLift 4196488
  have htrace : WordTrace (prefixWord ++ tailWord_4196488) baseStart_4196488 baseEnd_4196488 := by
    simpa [prefixWord, tailWord_4196488, baseEnd_4196488] using wordTrace_append hprefix tailTrace_4196488
  have hstable : (prefixWord ++ tailWord_4196488).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196488).length < 2 ^ (prefixWord ++ tailWord_4196488).sum := by decide
  have hdescent : baseEnd_4196488 < baseStart_4196488 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196488) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196508 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 3, 5, 2]
def baseStart_4196508 : Nat := 118140960795 + 4196508 * 2 ^ 59
def prefixEnd_4196508 : Nat := 4983230072969 + 3 ^ 40 * 4196508 * 2
def baseEnd_4196508 : Nat := 2154825674438172376850617

theorem tailTrace_4196508 : CollatzResearch.WordTrace tailWord_4196508 prefixEnd_4196508 2154825674438172376850617 := by
  unfold tailWord_4196508
  simp only [CollatzResearch.WordTrace]
  refine ⟨76529610540387848675795089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102039480720517131567726785 76529610540387848675795089)
  ·
    refine ⟨57397207905290886506846317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76529610540387848675795089 57397207905290886506846317)
    ·
      refine ⟨21523952964484082440067369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 57397207905290886506846317 21523952964484082440067369)
      ·
        refine ⟨16142964723363061830050527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 21523952964484082440067369 16142964723363061830050527)
        ·
          refine ⟨24214447085044592745075791, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16142964723363061830050527 24214447085044592745075791)
          ·
            refine ⟨36321670627566889117613687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 24214447085044592745075791 36321670627566889117613687)
            ·
              refine ⟨54482505941350333676420531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36321670627566889117613687 54482505941350333676420531)
              ·
                refine ⟨81723758912025500514630797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54482505941350333676420531 81723758912025500514630797)
                ·
                  refine ⟨30646409592009562692986549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 81723758912025500514630797 30646409592009562692986549)
                  ·
                    refine ⟨2873100899250896502467489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30646409592009562692986549 2873100899250896502467489)
                    ·
                      refine ⟨2154825674438172376850617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2873100899250896502467489 2154825674438172376850617)
                      ·
                        rfl

theorem cell23_4196508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 3, 5, 2].length) (baseStart_4196508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196508 prefixEnd_4196508 := by exact prefixLift 4196508
  have htrace : WordTrace (prefixWord ++ tailWord_4196508) baseStart_4196508 baseEnd_4196508 := by
    simpa [prefixWord, tailWord_4196508, baseEnd_4196508] using wordTrace_append hprefix tailTrace_4196508
  have hstable : (prefixWord ++ tailWord_4196508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196508).length < 2 ^ (prefixWord ++ tailWord_4196508).sum := by decide
  have hdescent : baseEnd_4196508 < baseStart_4196508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196525 : List Nat := [1, 5, 2, 1, 2, 1, 2, 1, 1, 5, 2]
def baseStart_4196525 : Nat := 118140960795 + 4196525 * 2 ^ 59
def prefixEnd_4196525 : Nat := 4983230072969 + 3 ^ 40 * 4196525 * 2
def baseEnd_4196525 : Nat := 2154834403609298810338039

theorem tailTrace_4196525 : CollatzResearch.WordTrace tailWord_4196525 prefixEnd_4196525 2154834403609298810338039 := by
  unfold tailWord_4196525
  simp only [CollatzResearch.WordTrace]
  refine ⟨153059841121714109254959029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102039894081142739503306019 153059841121714109254959029)
  ·
    refine ⟨14349360105160697742652409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 153059841121714109254959029 14349360105160697742652409)
    ·
      refine ⟨10762020078870523306989307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 14349360105160697742652409 10762020078870523306989307)
      ·
        refine ⟨16143030118305784960483961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 10762020078870523306989307 16143030118305784960483961)
        ·
          refine ⟨12107272588729338720362971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16143030118305784960483961 12107272588729338720362971)
          ·
            refine ⟨18160908883094008080544457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12107272588729338720362971 18160908883094008080544457)
            ·
              refine ⟨13620681662320506060408343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18160908883094008080544457 13620681662320506060408343)
              ·
                refine ⟨20431022493480759090612515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13620681662320506060408343 20431022493480759090612515)
                ·
                  refine ⟨30646533740221138635918773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 20431022493480759090612515 30646533740221138635918773)
                  ·
                    refine ⟨2873112538145731747117385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 30646533740221138635918773 2873112538145731747117385)
                    ·
                      refine ⟨2154834403609298810338039, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2873112538145731747117385 2154834403609298810338039)
                      ·
                        rfl

theorem cell23_4196525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 2, 1, 1, 5, 2].length) (baseStart_4196525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196525 prefixEnd_4196525 := by exact prefixLift 4196525
  have htrace : WordTrace (prefixWord ++ tailWord_4196525) baseStart_4196525 baseEnd_4196525 := by
    simpa [prefixWord, tailWord_4196525, baseEnd_4196525] using wordTrace_append hprefix tailTrace_4196525
  have hstable : (prefixWord ++ tailWord_4196525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196525).length < 2 ^ (prefixWord ++ tailWord_4196525).sum := by decide
  have hdescent : baseEnd_4196525 < baseStart_4196525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196526 : List Nat := [4, 1, 4, 2, 1, 2, 1, 3, 1, 4]
def baseStart_4196526 : Nat := 118140960795 + 4196526 * 2 ^ 59
def prefixEnd_4196526 : Nat := 4983230072969 + 3 ^ 40 * 4196526 * 2
def baseEnd_4196526 : Nat := 718278305696651102141845

theorem tailTrace_4196526 : CollatzResearch.WordTrace tailWord_4196526 prefixEnd_4196526 718278305696651102141845 := by
  unfold tailWord_4196526
  simp only [CollatzResearch.WordTrace]
  refine ⟨19132484699338810803218179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102039918396473657617163621 19132484699338810803218179)
  ·
    refine ⟨28698727049008216204827269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19132484699338810803218179 28698727049008216204827269)
    ·
      refine ⟨5381011321689040538405113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 28698727049008216204827269 5381011321689040538405113)
      ·
        refine ⟨4035758491266780403803835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5381011321689040538405113 4035758491266780403803835)
        ·
          refine ⟨6053637736900170605705753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4035758491266780403803835 6053637736900170605705753)
          ·
            refine ⟨4540228302675127954279315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6053637736900170605705753 4540228302675127954279315)
            ·
              refine ⟨6810342454012691931418973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4540228302675127954279315 6810342454012691931418973)
              ·
                refine ⟨2553878420254759474282115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 6810342454012691931418973 2553878420254759474282115)
                ·
                  refine ⟨3830817630382139211423173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2553878420254759474282115 3830817630382139211423173)
                  ·
                    refine ⟨718278305696651102141845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3830817630382139211423173 718278305696651102141845)
                    ·
                      rfl

theorem cell23_4196526_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_4196526 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196526 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196526 prefixEnd_4196526 := by exact prefixLift 4196526
  have htrace : WordTrace (prefixWord ++ tailWord_4196526) baseStart_4196526 baseEnd_4196526 := by
    simpa [prefixWord, tailWord_4196526, baseEnd_4196526] using wordTrace_append hprefix tailTrace_4196526
  have hstable : (prefixWord ++ tailWord_4196526).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196526).length < 2 ^ (prefixWord ++ tailWord_4196526).sum := by decide
  have hdescent : baseEnd_4196526 < baseStart_4196526 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196526) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196538 : List Nat := [3, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4]
def baseStart_4196538 : Nat := 118140960795 + 4196538 * 2 ^ 59
def prefixEnd_4196538 : Nat := 4983230072969 + 3 ^ 40 * 4196538 * 2
def baseEnd_4196538 : Nat := 2154841078857807259475479

theorem tailTrace_4196538 : CollatzResearch.WordTrace tailWord_4196538 prefixEnd_4196538 2154841078857807259475479 := by
  unfold tailWord_4196538
  simp only [CollatzResearch.WordTrace]
  refine ⟨38265078817666753118795567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 102040210180444674983454845 38265078817666753118795567)
  ·
    refine ⟨57397618226500129678193351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 38265078817666753118795567 57397618226500129678193351)
    ·
      refine ⟨86096427339750194517290027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57397618226500129678193351 86096427339750194517290027)
      ·
        refine ⟨129144641009625291775935041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86096427339750194517290027 129144641009625291775935041)
        ·
          refine ⟨96858480757218968831951281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129144641009625291775935041 96858480757218968831951281)
          ·
            refine ⟨72643860567914226623963461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 96858480757218968831951281 72643860567914226623963461)
            ·
              refine ⟨13620723856483917491993149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 72643860567914226623963461 13620723856483917491993149)
              ·
                refine ⟨5107771446181469059497431, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 13620723856483917491993149 5107771446181469059497431)
                ·
                  refine ⟨7661657169272203589246147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5107771446181469059497431 7661657169272203589246147)
                  ·
                    refine ⟨11492485753908305383869221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7661657169272203589246147 11492485753908305383869221)
                    ·
                      refine ⟨2154841078857807259475479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11492485753908305383869221 2154841078857807259475479)
                      ·
                        rfl

theorem cell23_4196538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 4, 3, 1, 1, 4].length) (baseStart_4196538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196538 prefixEnd_4196538 := by exact prefixLift 4196538
  have htrace : WordTrace (prefixWord ++ tailWord_4196538) baseStart_4196538 baseEnd_4196538 := by
    simpa [prefixWord, tailWord_4196538, baseEnd_4196538] using wordTrace_append hprefix tailTrace_4196538
  have hstable : (prefixWord ++ tailWord_4196538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196538).length < 2 ^ (prefixWord ++ tailWord_4196538).sum := by decide
  have hdescent : baseEnd_4196538 < baseStart_4196538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196542 : List Nat := [4, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2]
def baseStart_4196542 : Nat := 118140960795 + 4196542 * 2 ^ 59
def prefixEnd_4196542 : Nat := 4983230072969 + 3 ^ 40 * 4196542 * 2
def baseEnd_4196542 : Nat := 2154843132780425243825461

theorem tailTrace_4196542 : CollatzResearch.WordTrace tailWord_4196542 prefixEnd_4196542 2154843132780425243825461 := by
  unfold tailWord_4196542
  simp only [CollatzResearch.WordTrace]
  refine ⟨19132557645331565144790985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102040307441768347438885253 19132557645331565144790985)
  ·
    refine ⟨14349418233998673858593239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 19132557645331565144790985 14349418233998673858593239)
    ·
      refine ⟨21524127350998010787889859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 14349418233998673858593239 21524127350998010787889859)
      ·
        refine ⟨32286191026497016181834789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 21524127350998010787889859 32286191026497016181834789)
        ·
          refine ⟨6053660817468190534094023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 32286191026497016181834789 6053660817468190534094023)
          ·
            refine ⟨9080491226202285801141035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6053660817468190534094023 9080491226202285801141035)
            ·
              refine ⟨13620736839303428701711553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9080491226202285801141035 13620736839303428701711553)
              ·
                refine ⟨10215552629477571526283665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13620736839303428701711553 10215552629477571526283665)
                ·
                  refine ⟨7661664472108178644712749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10215552629477571526283665 7661664472108178644712749)
                  ·
                    refine ⟨2873124177040566991767281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 7661664472108178644712749 2873124177040566991767281)
                    ·
                      refine ⟨2154843132780425243825461, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2873124177040566991767281 2154843132780425243825461)
                      ·
                        rfl

theorem cell23_4196542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 2, 2, 3, 2].length) (baseStart_4196542 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196542 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196542 prefixEnd_4196542 := by exact prefixLift 4196542
  have htrace : WordTrace (prefixWord ++ tailWord_4196542) baseStart_4196542 baseEnd_4196542 := by
    simpa [prefixWord, tailWord_4196542, baseEnd_4196542] using wordTrace_append hprefix tailTrace_4196542
  have hstable : (prefixWord ++ tailWord_4196542).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196542).length < 2 ^ (prefixWord ++ tailWord_4196542).sum := by decide
  have hdescent : baseEnd_4196542 < baseStart_4196542 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196558 : List Nat := [4, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5]
def baseStart_4196558 : Nat := 118140960795 + 4196558 * 2 ^ 59
def prefixEnd_4196558 : Nat := 4983230072969 + 3 ^ 40 * 4196558 * 2
def baseEnd_4196558 : Nat := 2154851348470897181225387

theorem tailTrace_4196558 : CollatzResearch.WordTrace tailWord_4196558 prefixEnd_4196558 2154851348470897181225387 := by
  unfold tailWord_4196558
  simp only [CollatzResearch.WordTrace]
  refine ⟨19132630591324319486363791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 102040696487063037260606885 19132630591324319486363791)
  ·
    refine ⟨28698945886986479229545687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 19132630591324319486363791 28698945886986479229545687)
    ·
      refine ⟨43048418830479718844318531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 28698945886986479229545687 43048418830479718844318531)
      ·
        refine ⟨64572628245719578266477797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43048418830479718844318531 64572628245719578266477797)
        ·
          refine ⟨12107367796072420924964587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 64572628245719578266477797 12107367796072420924964587)
          ·
            refine ⟨18161051694108631387446881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12107367796072420924964587 18161051694108631387446881)
            ·
              refine ⟨13620788770581473540585161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 18161051694108631387446881 13620788770581473540585161)
              ·
                refine ⟨10215591577936105155438871, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13620788770581473540585161 10215591577936105155438871)
                ·
                  refine ⟨15323387366904157733158307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10215591577936105155438871 15323387366904157733158307)
                  ·
                    refine ⟨22985081050356236599737461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 15323387366904157733158307 22985081050356236599737461)
                    ·
                      refine ⟨2154851348470897181225387, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 22985081050356236599737461 2154851348470897181225387)
                      ·
                        rfl

theorem cell23_4196558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 4, 1, 2, 2, 1, 1, 5].length) (baseStart_4196558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196558 prefixEnd_4196558 := by exact prefixLift 4196558
  have htrace : WordTrace (prefixWord ++ tailWord_4196558) baseStart_4196558 baseEnd_4196558 := by
    simpa [prefixWord, tailWord_4196558, baseEnd_4196558] using wordTrace_append hprefix tailTrace_4196558
  have hstable : (prefixWord ++ tailWord_4196558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196558).length < 2 ^ (prefixWord ++ tailWord_4196558).sum := by decide
  have hdescent : baseEnd_4196558 < baseStart_4196558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196572 : List Nat := [2, 2, 5, 2, 1, 1, 1, 1, 3, 1, 4]
def baseStart_4196572 : Nat := 118140960795 + 4196572 * 2 ^ 59
def prefixEnd_4196572 : Nat := 4983230072969 + 3 ^ 40 * 4196572 * 2
def baseEnd_4196572 : Nat := 2154858537200060126450323

theorem tailTrace_4196572 : CollatzResearch.WordTrace tailWord_4196572 prefixEnd_4196572 2154858537200060126450323 := by
  unfold tailWord_4196572
  simp only [CollatzResearch.WordTrace]
  refine ⟨76530777676271918140959985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102041036901695890854613313 76530777676271918140959985)
  ·
    refine ⟨57398083257203938605719989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76530777676271918140959985 57398083257203938605719989)
    ·
      refine ⟨5381070305362869244286249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 57398083257203938605719989 5381070305362869244286249)
      ·
        refine ⟨4035802729022151933214687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5381070305362869244286249 4035802729022151933214687)
        ·
          refine ⟨6053704093533227899822031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4035802729022151933214687 6053704093533227899822031)
          ·
            refine ⟨9080556140299841849733047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6053704093533227899822031 9080556140299841849733047)
            ·
              refine ⟨13620834210449762774599571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9080556140299841849733047 13620834210449762774599571)
              ·
                refine ⟨20431251315674644161899357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 13620834210449762774599571 20431251315674644161899357)
                ·
                  refine ⟨7661719243377991560712259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 20431251315674644161899357 7661719243377991560712259)
                  ·
                    refine ⟨11492578865066987341068389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 7661719243377991560712259 11492578865066987341068389)
                    ·
                      refine ⟨2154858537200060126450323, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11492578865066987341068389 2154858537200060126450323)
                      ·
                        rfl

theorem cell23_4196572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_4196572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196572 prefixEnd_4196572 := by exact prefixLift 4196572
  have htrace : WordTrace (prefixWord ++ tailWord_4196572) baseStart_4196572 baseEnd_4196572 := by
    simpa [prefixWord, tailWord_4196572, baseEnd_4196572] using wordTrace_append hprefix tailTrace_4196572
  have hstable : (prefixWord ++ tailWord_4196572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196572).length < 2 ^ (prefixWord ++ tailWord_4196572).sum := by decide
  have hdescent : baseEnd_4196572 < baseStart_4196572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196588 : List Nat := [2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 3]
def baseStart_4196588 : Nat := 118140960795 + 4196588 * 2 ^ 59
def prefixEnd_4196588 : Nat := 4983230072969 + 3 ^ 40 * 4196588 * 2
def baseEnd_4196588 : Nat := 2154866752890532063850249

theorem tailTrace_4196588 : CollatzResearch.WordTrace tailWord_4196588 prefixEnd_4196588 2154866752890532063850249 := by
  unfold tailWord_4196588
  simp only [CollatzResearch.WordTrace]
  refine ⟨76531069460242935507251209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102041425946990580676334945 76531069460242935507251209)
  ·
    refine ⟨57398302095182201630438407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76531069460242935507251209 57398302095182201630438407)
    ·
      refine ⟨86097453142773302445657611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 57398302095182201630438407 86097453142773302445657611)
      ·
        refine ⟨129146179714159953668486417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 86097453142773302445657611 129146179714159953668486417)
        ·
          refine ⟨96859634785619965251364813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129146179714159953668486417 96859634785619965251364813)
          ·
            refine ⟨36322363044607486969261805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96859634785619965251364813 36322363044607486969261805)
            ·
              refine ⟨13620886141727807613473177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 36322363044607486969261805 13620886141727807613473177)
              ·
                refine ⟨10215664606295855710104883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 13620886141727807613473177 10215664606295855710104883)
                ·
                  refine ⟨15323496909443783565157325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10215664606295855710104883 15323496909443783565157325)
                  ·
                    refine ⟨5746311341041418836933997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 15323496909443783565157325 5746311341041418836933997)
                    ·
                      refine ⟨2154866752890532063850249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 5746311341041418836933997 2154866752890532063850249)
                      ·
                        rfl

theorem cell23_4196588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 3, 3].length) (baseStart_4196588 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196588 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196588 prefixEnd_4196588 := by exact prefixLift 4196588
  have htrace : WordTrace (prefixWord ++ tailWord_4196588) baseStart_4196588 baseEnd_4196588 := by
    simpa [prefixWord, tailWord_4196588, baseEnd_4196588] using wordTrace_append hprefix tailTrace_4196588
  have hstable : (prefixWord ++ tailWord_4196588).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196588).length < 2 ^ (prefixWord ++ tailWord_4196588).sum := by decide
  have hdescent : baseEnd_4196588 < baseStart_4196588 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196611 : List Nat := [1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 4]
def baseStart_4196611 : Nat := 118140960795 + 4196611 * 2 ^ 59
def prefixEnd_4196611 : Nat := 4983230072969 + 3 ^ 40 * 4196611 * 2
def baseEnd_4196611 : Nat := 2154878562945585473862643

theorem tailTrace_4196611 : CollatzResearch.WordTrace tailWord_4196611 prefixEnd_4196611 2154878562945585473862643 := by
  unfold tailWord_4196611
  simp only [CollatzResearch.WordTrace]
  refine ⟨153062977799402545942589687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102041985199601697295059791 153062977799402545942589687)
  ·
    refine ⟨229594466699103818913884531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153062977799402545942589687 229594466699103818913884531)
    ·
      refine ⟨344391700048655728370826797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229594466699103818913884531 344391700048655728370826797)
      ·
        refine ⟨129146887518245898139060049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 344391700048655728370826797 129146887518245898139060049)
        ·
          refine ⟨96860165638684423604295037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 129146887518245898139060049 96860165638684423604295037)
          ·
            refine ⟨36322562114506658851610639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 96860165638684423604295037 36322562114506658851610639)
            ·
              refine ⟨54483843171759988277415959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 36322562114506658851610639 54483843171759988277415959)
              ·
                refine ⟨81725764757639982416123939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 54483843171759988277415959 81725764757639982416123939)
                ·
                  refine ⟨122588647136459973624185909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 81725764757639982416123939 122588647136459973624185909)
                  ·
                    refine ⟨11492685669043122527267429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 122588647136459973624185909 11492685669043122527267429)
                    ·
                      refine ⟨2154878562945585473862643, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 11492685669043122527267429 2154878562945585473862643)
                      ·
                        rfl

theorem cell23_4196611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_4196611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196611 prefixEnd_4196611 := by exact prefixLift 4196611
  have htrace : WordTrace (prefixWord ++ tailWord_4196611) baseStart_4196611 baseEnd_4196611 := by
    simpa [prefixWord, tailWord_4196611, baseEnd_4196611] using wordTrace_append hprefix tailTrace_4196611
  have hstable : (prefixWord ++ tailWord_4196611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196611).length < 2 ^ (prefixWord ++ tailWord_4196611).sum := by decide
  have hdescent : baseEnd_4196611 < baseStart_4196611 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196668 : List Nat := [2, 2, 2, 2, 1, 2, 4, 1, 7]
def baseStart_4196668 : Nat := 118140960795 + 4196668 * 2 ^ 59
def prefixEnd_4196668 : Nat := 4983230072969 + 3 ^ 40 * 4196668 * 2
def baseEnd_4196668 : Nat := 239434203482543527872209

theorem tailTrace_4196668 : CollatzResearch.WordTrace tailWord_4196668 prefixEnd_4196668 239434203482543527872209 := by
  unfold tailWord_4196668
  simp only [CollatzResearch.WordTrace]
  refine ⟨76532528380098022338707329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 102043371173464029784943105 76532528380098022338707329)
  ·
    refine ⟨57399396285073516754030497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 76532528380098022338707329 57399396285073516754030497)
    ·
      refine ⟨43049547213805137565522873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 57399396285073516754030497 43049547213805137565522873)
      ·
        refine ⟨32287160410353853174142155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 43049547213805137565522873 32287160410353853174142155)
        ·
          refine ⟨48430740615530779761213233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 32287160410353853174142155 48430740615530779761213233)
          ·
            refine ⟨36323055461648084820909925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48430740615530779761213233 36323055461648084820909925)
            ·
              refine ⟨6810572899059015903920611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 36323055461648084820909925 6810572899059015903920611)
              ·
                refine ⟨10215859348588523855880917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 6810572899059015903920611 10215859348588523855880917)
                ·
                  refine ⟨239434203482543527872209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10215859348588523855880917 239434203482543527872209)
                  ·
                    rfl

theorem cell23_4196668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 4, 1, 7].length) (baseStart_4196668 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196668 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196668 prefixEnd_4196668 := by exact prefixLift 4196668
  have htrace : WordTrace (prefixWord ++ tailWord_4196668) baseStart_4196668 baseEnd_4196668 := by
    simpa [prefixWord, tailWord_4196668, baseEnd_4196668] using wordTrace_append hprefix tailTrace_4196668
  have hstable : (prefixWord ++ tailWord_4196668).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196668).length < 2 ^ (prefixWord ++ tailWord_4196668).sum := by decide
  have hdescent : baseEnd_4196668 < baseStart_4196668 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196679 : List Nat := [1, 1, 4, 1, 2, 2, 5, 1, 2, 2, 2]
def baseStart_4196679 : Nat := 118140960795 + 4196679 * 2 ^ 59
def prefixEnd_4196679 : Nat := 4983230072969 + 3 ^ 40 * 4196679 * 2
def baseEnd_4196679 : Nat := 2154913479630091207812331

theorem tailTrace_4196679 : CollatzResearch.WordTrace tailWord_4196679 prefixEnd_4196679 2154913479630091207812331 := by
  unfold tailWord_4196679
  simp only [CollatzResearch.WordTrace]
  refine ⟨153065457963156193556065091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102043638642104129037376727 153065457963156193556065091)
  ·
    refine ⟨229598186944734290334097637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153065457963156193556065091 229598186944734290334097637)
    ·
      refine ⟨43049660052137679437643307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 229598186944734290334097637 43049660052137679437643307)
      ·
        refine ⟨64574490078206519156464961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 43049660052137679437643307 64574490078206519156464961)
        ·
          refine ⟨48430867558654889367348721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 64574490078206519156464961 48430867558654889367348721)
          ·
            refine ⟨36323150668991167025511541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 48430867558654889367348721 36323150668991167025511541)
            ·
              refine ⟨3405295375217921908641707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 36323150668991167025511541 3405295375217921908641707)
              ·
                refine ⟨5107943062826882862962561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3405295375217921908641707 5107943062826882862962561)
                ·
                  refine ⟨3830957297120162147221921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5107943062826882862962561 3830957297120162147221921)
                  ·
                    refine ⟨2873217972840121610416441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3830957297120162147221921 2873217972840121610416441)
                    ·
                      refine ⟨2154913479630091207812331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2873217972840121610416441 2154913479630091207812331)
                      ·
                        rfl

theorem cell23_4196679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 5, 1, 2, 2, 2].length) (baseStart_4196679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196679 prefixEnd_4196679 := by exact prefixLift 4196679
  have htrace : WordTrace (prefixWord ++ tailWord_4196679) baseStart_4196679 baseEnd_4196679 := by
    simpa [prefixWord, tailWord_4196679, baseEnd_4196679] using wordTrace_append hprefix tailTrace_4196679
  have hstable : (prefixWord ++ tailWord_4196679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196679).length < 2 ^ (prefixWord ++ tailWord_4196679).sum := by decide
  have hdescent : baseEnd_4196679 < baseStart_4196679 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4196691 : List Nat := [1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 7]
def baseStart_4196691 : Nat := 118140960795 + 4196691 * 2 ^ 59
def prefixEnd_4196691 : Nat := 4983230072969 + 3 ^ 40 * 4196691 * 2
def baseEnd_4196691 : Nat := 2154919641397945160862275

theorem tailTrace_4196691 : CollatzResearch.WordTrace tailWord_4196691 prefixEnd_4196691 2154919641397945160862275 := by
  unfold tailWord_4196691
  simp only [CollatzResearch.WordTrace]
  refine ⟨153065895639112719605501927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 102043930426075146403667951 153065895639112719605501927)
  ·
    refine ⟨229598843458669079408252891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 153065895639112719605501927 229598843458669079408252891)
    ·
      refine ⟨344398265188003619112379337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 229598843458669079408252891 344398265188003619112379337)
      ·
        refine ⟨258298698891002714334284503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 344398265188003619112379337 258298698891002714334284503)
        ·
          refine ⟨387448048336504071501426755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 258298698891002714334284503 387448048336504071501426755)
          ·
            refine ⟨581172072504756107252140133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 387448048336504071501426755 581172072504756107252140133)
            ·
              refine ⟨108969763594641770109776275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 581172072504756107252140133 108969763594641770109776275)
              ·
                refine ⟨163454645391962655164664413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 108969763594641770109776275 163454645391962655164664413)
                ·
                  refine ⟨61295492021985995686749155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 163454645391962655164664413 61295492021985995686749155)
                  ·
                    refine ⟨91943238032978993530123733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 61295492021985995686749155 91943238032978993530123733)
                    ·
                      refine ⟨2154919641397945160862275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 91943238032978993530123733 2154919641397945160862275)
                      ·
                        rfl

theorem cell23_4196691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 7].length) (baseStart_4196691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4196691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4196691 prefixEnd_4196691 := by exact prefixLift 4196691
  have htrace : WordTrace (prefixWord ++ tailWord_4196691) baseStart_4196691 baseEnd_4196691 := by
    simpa [prefixWord, tailWord_4196691, baseEnd_4196691] using wordTrace_append hprefix tailTrace_4196691
  have hstable : (prefixWord ++ tailWord_4196691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4196691).length < 2 ^ (prefixWord ++ tailWord_4196691).sum := by decide
  have hdescent : baseEnd_4196691 < baseStart_4196691 := by decide
  rcases family_descends (prefixWord ++ tailWord_4196691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
