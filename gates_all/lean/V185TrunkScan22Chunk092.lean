import V185TrunkScan22Chunk091

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_825545 : List Nat := [1, 2, 1, 1, 2, 1, 1, 7, 3, 3]
def baseStart_825545 : Nat := 118140960795 + 825545 * 2 ^ 59
def prefixEnd_825545 : Nat := 4983230072969 + 3 ^ 40 * 825545 * 2
def baseEnd_825545 : Nat := 282600924610718523393929

theorem tailTrace_825545 : CollatzResearch.WordTrace tailWord_825545 prefixEnd_825545 282600924610718523393929 := by
  unfold tailWord_825545
  simp only [CollatzResearch.WordTrace]
  refine ⟨30110099794198931706174089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20073399862799287804116059 30110099794198931706174089)
  ·
    refine ⟨22582574845649198779630567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30110099794198931706174089 22582574845649198779630567)
    ·
      refine ⟨33873862268473798169445851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22582574845649198779630567 33873862268473798169445851)
      ·
        refine ⟨50810793402710697254168777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33873862268473798169445851 50810793402710697254168777)
        ·
          refine ⟨38108095052033022940626583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 50810793402710697254168777 38108095052033022940626583)
          ·
            refine ⟨57162142578049534410939875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38108095052033022940626583 57162142578049534410939875)
            ·
              refine ⟨85743213867074301616409813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57162142578049534410939875 85743213867074301616409813)
              ·
                refine ⟨2009606575009553944134605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 85743213867074301616409813 2009606575009553944134605)
                ·
                  refine ⟨753602465628582729050477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2009606575009553944134605 753602465628582729050477)
                  ·
                    refine ⟨282600924610718523393929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 753602465628582729050477 282600924610718523393929)
                    ·
                      rfl

theorem cell22_825545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 1, 7, 3, 3].length) (baseStart_825545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825545 prefixEnd_825545 := by exact prefixLift 825545
  have htrace : WordTrace (prefixWord ++ tailWord_825545) baseStart_825545 baseEnd_825545 := by
    simpa [prefixWord, tailWord_825545, baseEnd_825545] using wordTrace_append hprefix tailTrace_825545
  have hstable : (prefixWord ++ tailWord_825545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825545).length < 2 ^ (prefixWord ++ tailWord_825545).sum := by decide
  have hdescent : baseEnd_825545 < baseStart_825545 := by decide
  rcases family_descends (prefixWord ++ tailWord_825545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825596 : List Nat := [2, 2, 2, 1, 4, 1, 4, 2, 1, 3]
def baseStart_825596 : Nat := 118140960795 + 825596 * 2 ^ 59
def prefixEnd_825596 : Nat := 4983230072969 + 3 ^ 40 * 825596 * 2
def baseEnd_825596 : Nat := 282618382952971390368773

theorem tailTrace_825596 : CollatzResearch.WordTrace tailWord_825596 prefixEnd_825596 282618382952971390368773 := by
  unfold tailWord_825596
  simp only [CollatzResearch.WordTrace]
  refine ⟨15055979958507083708140321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20074639944676111610853761 15055979958507083708140321)
  ·
    refine ⟨11291984968880312781105241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15055979958507083708140321 11291984968880312781105241)
    ·
      refine ⟨8468988726660234585828931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11291984968880312781105241 8468988726660234585828931)
      ·
        refine ⟨12703483089990351878743397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8468988726660234585828931 12703483089990351878743397)
        ·
          refine ⟨2381903079373190977264387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12703483089990351878743397 2381903079373190977264387)
          ·
            refine ⟨3572854619059786465896581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2381903079373190977264387 3572854619059786465896581)
            ·
              refine ⟨669910241073709962355609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3572854619059786465896581 669910241073709962355609)
              ·
                refine ⟨502432680805282471766707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 669910241073709962355609 502432680805282471766707)
                ·
                  refine ⟨753649021207923707650061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 502432680805282471766707 753649021207923707650061)
                  ·
                    refine ⟨282618382952971390368773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 753649021207923707650061 282618382952971390368773)
                    ·
                      rfl

theorem cell22_825596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 4, 2, 1, 3].length) (baseStart_825596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825596 prefixEnd_825596 := by exact prefixLift 825596
  have htrace : WordTrace (prefixWord ++ tailWord_825596) baseStart_825596 baseEnd_825596 := by
    simpa [prefixWord, tailWord_825596, baseEnd_825596] using wordTrace_append hprefix tailTrace_825596
  have hstable : (prefixWord ++ tailWord_825596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825596).length < 2 ^ (prefixWord ++ tailWord_825596).sum := by decide
  have hdescent : baseEnd_825596 < baseStart_825596 := by decide
  rcases family_descends (prefixWord ++ tailWord_825596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825635 : List Nat := [1, 1, 1, 4, 2, 2, 1, 4, 1, 5]
def baseStart_825635 : Nat := 118140960795 + 825635 * 2 ^ 59
def prefixEnd_825635 : Nat := 4983230072969 + 3 ^ 40 * 825635 * 2
def baseEnd_825635 : Nat := 282631733449988288643653

theorem tailTrace_825635 : CollatzResearch.WordTrace tailWord_825635 prefixEnd_825635 282631733449988288643653 := by
  unfold tailWord_825635
  simp only [CollatzResearch.WordTrace]
  refine ⟨30113382363872877076950359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20075588242581918051300239 30113382363872877076950359)
  ·
    refine ⟨45170073545809315615425539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30113382363872877076950359 45170073545809315615425539)
    ·
      refine ⟨67755110318713973423138309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45170073545809315615425539 67755110318713973423138309)
      ·
        refine ⟨12704083184758870016838433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 67755110318713973423138309 12704083184758870016838433)
        ·
          refine ⟨9528062388569152512628825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12704083184758870016838433 9528062388569152512628825)
          ·
            refine ⟨7146046791426864384471619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9528062388569152512628825 7146046791426864384471619)
            ·
              refine ⟨10719070187140296576707429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7146046791426864384471619 10719070187140296576707429)
              ·
                refine ⟨2009825660088805608132643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10719070187140296576707429 2009825660088805608132643)
                ·
                  refine ⟨3014738490133208412198965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2009825660088805608132643 3014738490133208412198965)
                  ·
                    refine ⟨282631733449988288643653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3014738490133208412198965 282631733449988288643653)
                    ·
                      rfl

theorem cell22_825635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 1, 5].length) (baseStart_825635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825635 prefixEnd_825635 := by exact prefixLift 825635
  have htrace : WordTrace (prefixWord ++ tailWord_825635) baseStart_825635 baseEnd_825635 := by
    simpa [prefixWord, tailWord_825635, baseEnd_825635] using wordTrace_append hprefix tailTrace_825635
  have hstable : (prefixWord ++ tailWord_825635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825635).length < 2 ^ (prefixWord ++ tailWord_825635).sum := by decide
  have hdescent : baseEnd_825635 < baseStart_825635 := by decide
  rcases family_descends (prefixWord ++ tailWord_825635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825682 : List Nat := [3, 2, 2, 1, 1, 1, 6, 6]
def baseStart_825682 : Nat := 118140960795 + 825682 * 2 ^ 59
def prefixEnd_825682 : Nat := 4983230072969 + 3 ^ 40 * 825682 * 2
def baseEnd_825682 : Nat := 31405313612277314746501

theorem tailTrace_825682 : CollatzResearch.WordTrace tailWord_825682 prefixEnd_825682 31405313612277314746501 := by
  unfold tailWord_825682
  simp only [CollatzResearch.WordTrace]
  refine ⟨7528774148675651025977825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20076731063135069402607533 7528774148675651025977825)
  ·
    refine ⟨5646580611506738269483369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7528774148675651025977825 5646580611506738269483369)
    ·
      refine ⟨4234935458630053702112527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5646580611506738269483369 4234935458630053702112527)
      ·
        refine ⟨6352403187945080553168791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4234935458630053702112527 6352403187945080553168791)
        ·
          refine ⟨9528604781917620829753187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6352403187945080553168791 9528604781917620829753187)
          ·
            refine ⟨14292907172876431244629781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9528604781917620829753187 14292907172876431244629781)
            ·
              refine ⟨669980023728582714592021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14292907172876431244629781 669980023728582714592021)
              ·
                refine ⟨31405313612277314746501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 669980023728582714592021 31405313612277314746501)
                ·
                  rfl

theorem cell22_825682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 6, 6].length) (baseStart_825682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825682 prefixEnd_825682 := by exact prefixLift 825682
  have htrace : WordTrace (prefixWord ++ tailWord_825682) baseStart_825682 baseEnd_825682 := by
    simpa [prefixWord, tailWord_825682, baseEnd_825682] using wordTrace_append hprefix tailTrace_825682
  have hstable : (prefixWord ++ tailWord_825682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825682).length < 2 ^ (prefixWord ++ tailWord_825682).sum := by decide
  have hdescent : baseEnd_825682 < baseStart_825682 := by decide
  rcases family_descends (prefixWord ++ tailWord_825682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825714 : List Nat := [3, 2, 1, 2, 1, 3, 3, 1, 3, 3]
def baseStart_825714 : Nat := 118140960795 + 825714 * 2 ^ 59
def prefixEnd_825714 : Nat := 4983230072969 + 3 ^ 40 * 825714 * 2
def baseEnd_825714 : Nat := 282658776764458415918411

theorem tailTrace_825714 : CollatzResearch.WordTrace tailWord_825714 prefixEnd_825714 282658776764458415918411 := by
  unfold tailWord_825714
  simp only [CollatzResearch.WordTrace]
  refine ⟨7529065932646668392269049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20077509153724449046050797 7529065932646668392269049)
  ·
    refine ⟨5646799449485001294201787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7529065932646668392269049 5646799449485001294201787)
    ·
      refine ⟨8470199174227501941302681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5646799449485001294201787 8470199174227501941302681)
      ·
        refine ⟨6352649380670626455977011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8470199174227501941302681 6352649380670626455977011)
        ·
          refine ⟨9528974071005939683965517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6352649380670626455977011 9528974071005939683965517)
          ·
            refine ⟨3573365276627227381487069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9528974071005939683965517 3573365276627227381487069)
            ·
              refine ⟨1340011978735210268057651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3573365276627227381487069 1340011978735210268057651)
              ·
                refine ⟨2010017968102815402086477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1340011978735210268057651 2010017968102815402086477)
                ·
                  refine ⟨753756738038555775782429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2010017968102815402086477 753756738038555775782429)
                  ·
                    refine ⟨282658776764458415918411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 753756738038555775782429 282658776764458415918411)
                    ·
                      rfl

theorem cell22_825714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 3, 1, 3, 3].length) (baseStart_825714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825714 prefixEnd_825714 := by exact prefixLift 825714
  have htrace : WordTrace (prefixWord ++ tailWord_825714) baseStart_825714 baseEnd_825714 := by
    simpa [prefixWord, tailWord_825714, baseEnd_825714] using wordTrace_append hprefix tailTrace_825714
  have hstable : (prefixWord ++ tailWord_825714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825714).length < 2 ^ (prefixWord ++ tailWord_825714).sum := by decide
  have hdescent : baseEnd_825714 < baseStart_825714 := by decide
  rcases family_descends (prefixWord ++ tailWord_825714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825761 : List Nat := [1, 2, 3, 5, 1, 1, 2, 2, 5]
def baseStart_825761 : Nat := 118140960795 + 825761 * 2 ^ 59
def prefixEnd_825761 : Nat := 4983230072969 + 3 ^ 40 * 825761 * 2
def baseEnd_825761 : Nat := 94224955274988653331089

theorem tailTrace_825761 : CollatzResearch.WordTrace tailWord_825761 prefixEnd_825761 94224955274988653331089 := by
  unfold tailWord_825761
  simp only [CollatzResearch.WordTrace]
  refine ⟨30117977961416400596037137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20078651974277600397358091 30117977961416400596037137)
  ·
    refine ⟨22588483471062300447027853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30117977961416400596037137 22588483471062300447027853)
    ·
      refine ⟨8470681301648362667635445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22588483471062300447027853 8470681301648362667635445)
      ·
        refine ⟨794126372029534000090823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8470681301648362667635445 794126372029534000090823)
        ·
          refine ⟨1191189558044301000136235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 794126372029534000090823 1191189558044301000136235)
          ·
            refine ⟨1786784337066451500204353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1191189558044301000136235 1786784337066451500204353)
            ·
              refine ⟨1340088252799838625153265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1786784337066451500204353 1340088252799838625153265)
              ·
                refine ⟨1005066189599878968864949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1340088252799838625153265 1005066189599878968864949)
                ·
                  refine ⟨94224955274988653331089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1005066189599878968864949 94224955274988653331089)
                  ·
                    rfl

theorem cell22_825761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 1, 1, 2, 2, 5].length) (baseStart_825761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825761 prefixEnd_825761 := by exact prefixLift 825761
  have htrace : WordTrace (prefixWord ++ tailWord_825761) baseStart_825761 baseEnd_825761 := by
    simpa [prefixWord, tailWord_825761, baseEnd_825761] using wordTrace_append hprefix tailTrace_825761
  have hstable : (prefixWord ++ tailWord_825761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825761).length < 2 ^ (prefixWord ++ tailWord_825761).sum := by decide
  have hdescent : baseEnd_825761 < baseStart_825761 := by decide
  rcases family_descends (prefixWord ++ tailWord_825761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825802 : List Nat := [3, 1, 2, 1, 2, 2, 3, 1, 1, 6]
def baseStart_825802 : Nat := 118140960795 + 825802 * 2 ^ 59
def prefixEnd_825802 : Nat := 4983230072969 + 3 ^ 40 * 825802 * 2
def baseEnd_825802 : Nat := 282688900962855519718141

theorem tailTrace_825802 : CollatzResearch.WordTrace tailWord_825802 prefixEnd_825802 282688900962855519718141 := by
  unfold tailWord_825802
  simp only [CollatzResearch.WordTrace]
  refine ⟨7529868338566966149569915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20079648902845243065519773 7529868338566966149569915)
  ·
    refine ⟨11294802507850449224354873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7529868338566966149569915 11294802507850449224354873)
    ·
      refine ⟨8471101880887836918266155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11294802507850449224354873 8471101880887836918266155)
      ·
        refine ⟨12706652821331755377399233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8471101880887836918266155 12706652821331755377399233)
        ·
          refine ⟨9529989615998816533049425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12706652821331755377399233 9529989615998816533049425)
          ·
            refine ⟨7147492211999112399787069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9529989615998816533049425 7147492211999112399787069)
            ·
              refine ⟨2680309579499667149920151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7147492211999112399787069 2680309579499667149920151)
              ·
                refine ⟨4020464369249500724880227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2680309579499667149920151 4020464369249500724880227)
                ·
                  refine ⟨6030696553874251087320341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4020464369249500724880227 6030696553874251087320341)
                  ·
                    refine ⟨282688900962855519718141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6030696553874251087320341 282688900962855519718141)
                    ·
                      rfl

theorem cell22_825802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_825802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825802 prefixEnd_825802 := by exact prefixLift 825802
  have htrace : WordTrace (prefixWord ++ tailWord_825802) baseStart_825802 baseEnd_825802 := by
    simpa [prefixWord, tailWord_825802, baseEnd_825802] using wordTrace_append hprefix tailTrace_825802
  have hstable : (prefixWord ++ tailWord_825802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825802).length < 2 ^ (prefixWord ++ tailWord_825802).sum := by decide
  have hdescent : baseEnd_825802 < baseStart_825802 := by decide
  rcases family_descends (prefixWord ++ tailWord_825802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825838 : List Nat := [4, 1, 2, 1, 2, 3, 3, 1, 2, 3]
def baseStart_825838 : Nat := 118140960795 + 825838 * 2 ^ 59
def prefixEnd_825838 : Nat := 4983230072969 + 3 ^ 40 * 825838 * 2
def baseEnd_825838 : Nat := 282701224498563425818031

theorem tailTrace_825838 : CollatzResearch.WordTrace tailWord_825838 prefixEnd_825838 282701224498563425818031 := by
  unfold tailWord_825838
  simp only [CollatzResearch.WordTrace]
  refine ⟨3765098297767180343323771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20080524254758295164393445 3765098297767180343323771)
  ·
    refine ⟨5647647446650770514985657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3765098297767180343323771 5647647446650770514985657)
    ·
      refine ⟨4235735584988077886239243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5647647446650770514985657 4235735584988077886239243)
      ·
        refine ⟨6353603377482116829358865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4235735584988077886239243 6353603377482116829358865)
        ·
          refine ⟨4765202533111587622019149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6353603377482116829358865 4765202533111587622019149)
          ·
            refine ⟨1786950949916845358257181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4765202533111587622019149 1786950949916845358257181)
            ·
              refine ⟨670106606218817009346443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1786950949916845358257181 670106606218817009346443)
              ·
                refine ⟨1005159909328225514019665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 670106606218817009346443 1005159909328225514019665)
                ·
                  refine ⟨753869931996169135514749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1005159909328225514019665 753869931996169135514749)
                  ·
                    refine ⟨282701224498563425818031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 753869931996169135514749 282701224498563425818031)
                    ·
                      rfl

theorem cell22_825838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 1, 2, 3].length) (baseStart_825838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825838 prefixEnd_825838 := by exact prefixLift 825838
  have htrace : WordTrace (prefixWord ++ tailWord_825838) baseStart_825838 baseEnd_825838 := by
    simpa [prefixWord, tailWord_825838, baseEnd_825838] using wordTrace_append hprefix tailTrace_825838
  have hstable : (prefixWord ++ tailWord_825838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825838).length < 2 ^ (prefixWord ++ tailWord_825838).sum := by decide
  have hdescent : baseEnd_825838 < baseStart_825838 := by decide
  rcases family_descends (prefixWord ++ tailWord_825838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825849 : List Nat := [1, 2, 1, 3, 1, 2, 4, 2, 3, 3]
def baseStart_825849 : Nat := 118140960795 + 825849 * 2 ^ 59
def prefixEnd_825849 : Nat := 4983230072969 + 3 ^ 40 * 825849 * 2
def baseEnd_825849 : Nat := 282704990023363063792997

theorem tailTrace_825849 : CollatzResearch.WordTrace tailWord_825849 prefixEnd_825849 282704990023363063792997 := by
  unfold tailWord_825849
  simp only [CollatzResearch.WordTrace]
  refine ⟨30121187585097591625240601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20080791723398394416827067 30121187585097591625240601)
  ·
    refine ⟨22590890688823193718930451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30121187585097591625240601 22590890688823193718930451)
    ·
      refine ⟨33886336033234790578395677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22590890688823193718930451 33886336033234790578395677)
      ·
        refine ⟨12707376012463046466898379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33886336033234790578395677 12707376012463046466898379)
        ·
          refine ⟨19061064018694569700347569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12707376012463046466898379 19061064018694569700347569)
          ·
            refine ⟨14295798014020927275260677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19061064018694569700347569 14295798014020927275260677)
            ·
              refine ⟨2680462127628923864111377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14295798014020927275260677 2680462127628923864111377)
              ·
                refine ⟨2010346595721692898083533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2680462127628923864111377 2010346595721692898083533)
                ·
                  refine ⟨753879973395634836781325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2010346595721692898083533 753879973395634836781325)
                  ·
                    refine ⟨282704990023363063792997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 753879973395634836781325 282704990023363063792997)
                    ·
                      rfl

theorem cell22_825849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 2, 4, 2, 3, 3].length) (baseStart_825849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825849 prefixEnd_825849 := by exact prefixLift 825849
  have htrace : WordTrace (prefixWord ++ tailWord_825849) baseStart_825849 baseEnd_825849 := by
    simpa [prefixWord, tailWord_825849, baseEnd_825849] using wordTrace_append hprefix tailTrace_825849
  have hstable : (prefixWord ++ tailWord_825849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825849).length < 2 ^ (prefixWord ++ tailWord_825849).sum := by decide
  have hdescent : baseEnd_825849 < baseStart_825849 := by decide
  rcases family_descends (prefixWord ++ tailWord_825849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825896 : List Nat := [2, 1, 5, 2, 1, 2, 1, 3, 5]
def baseStart_825896 : Nat := 118140960795 + 825896 * 2 ^ 59
def prefixEnd_825896 : Nat := 4983230072969 + 3 ^ 40 * 825896 * 2
def baseEnd_825896 : Nat := 94240359694623535955951

theorem tailTrace_825896 : CollatzResearch.WordTrace tailWord_825896 prefixEnd_825896 94240359694623535955951 := by
  unfold tailWord_825896
  simp only [CollatzResearch.WordTrace]
  refine ⟨15061450907963659326100771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20081934543951545768134361 15061450907963659326100771)
  ·
    refine ⟨22592176361945488989151157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15061450907963659326100771 22592176361945488989151157)
    ·
      refine ⟨2118016533932389592732921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22592176361945488989151157 2118016533932389592732921)
      ·
        refine ⟨1588512400449292194549691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2118016533932389592732921 1588512400449292194549691)
        ·
          refine ⟨2382768600673938291824537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1588512400449292194549691 2382768600673938291824537)
          ·
            refine ⟨1787076450505453718868403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2382768600673938291824537 1787076450505453718868403)
            ·
              refine ⟨2680614675758180578302605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1787076450505453718868403 2680614675758180578302605)
              ·
                refine ⟨1005230503409317716863477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2680614675758180578302605 1005230503409317716863477)
                ·
                  refine ⟨94240359694623535955951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1005230503409317716863477 94240359694623535955951)
                  ·
                    rfl

theorem cell22_825896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 2, 1, 3, 5].length) (baseStart_825896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825896 prefixEnd_825896 := by exact prefixLift 825896
  have htrace : WordTrace (prefixWord ++ tailWord_825896) baseStart_825896 baseEnd_825896 := by
    simpa [prefixWord, tailWord_825896, baseEnd_825896] using wordTrace_append hprefix tailTrace_825896
  have hstable : (prefixWord ++ tailWord_825896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825896).length < 2 ^ (prefixWord ++ tailWord_825896).sum := by decide
  have hdescent : baseEnd_825896 < baseStart_825896 := by decide
  rcases family_descends (prefixWord ++ tailWord_825896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825907 : List Nat := [1, 1, 1, 2, 4, 2, 2, 1, 8]
def baseStart_825907 : Nat := 118140960795 + 825907 * 2 ^ 59
def prefixEnd_825907 : Nat := 4983230072969 + 3 ^ 40 * 825907 * 2
def baseEnd_825907 : Nat := 94241614869556748614273

theorem tailTrace_825907 : CollatzResearch.WordTrace tailWord_825907 prefixEnd_825907 94241614869556748614273 := by
  unfold tailWord_825907
  simp only [CollatzResearch.WordTrace]
  refine ⟨30123303018887467530851975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20082202012591645020567983 30123303018887467530851975)
  ·
    refine ⟨45184954528331201296277963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30123303018887467530851975 45184954528331201296277963)
    ·
      refine ⟨67777431792496801944416945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45184954528331201296277963 67777431792496801944416945)
      ·
        refine ⟨50833073844372601458312709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67777431792496801944416945 50833073844372601458312709)
        ·
          refine ⟨9531201345819862773433633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50833073844372601458312709 9531201345819862773433633)
          ·
            refine ⟨7148401009364897080075225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9531201345819862773433633 7148401009364897080075225)
            ·
              refine ⟨5361300757023672810056419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7148401009364897080075225 5361300757023672810056419)
              ·
                refine ⟨8041951135535509215084629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5361300757023672810056419 8041951135535509215084629)
                ·
                  refine ⟨94241614869556748614273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8041951135535509215084629 94241614869556748614273)
                  ·
                    rfl

theorem cell22_825907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 8].length) (baseStart_825907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825907 prefixEnd_825907 := by exact prefixLift 825907
  have htrace : WordTrace (prefixWord ++ tailWord_825907) baseStart_825907 baseEnd_825907 := by
    simpa [prefixWord, tailWord_825907, baseEnd_825907] using wordTrace_append hprefix tailTrace_825907
  have hstable : (prefixWord ++ tailWord_825907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825907).length < 2 ^ (prefixWord ++ tailWord_825907).sum := by decide
  have hdescent : baseEnd_825907 < baseStart_825907 := by decide
  rcases family_descends (prefixWord ++ tailWord_825907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825909 : List Nat := [1, 3, 3, 1, 1, 2, 3, 1, 3, 4]
def baseStart_825909 : Nat := 118140960795 + 825909 * 2 ^ 59
def prefixEnd_825909 : Nat := 4983230072969 + 3 ^ 40 * 825909 * 2
def baseEnd_825909 : Nat := 282725529249542907292813

theorem tailTrace_825909 : CollatzResearch.WordTrace tailWord_825909 prefixEnd_825909 282725529249542907292813 := by
  unfold tailWord_825909
  simp only [CollatzResearch.WordTrace]
  refine ⟨30123375964880221872424781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20082250643253481248283187 30123375964880221872424781)
  ·
    refine ⟨11296265986830083202159293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30123375964880221872424781 11296265986830083202159293)
    ·
      refine ⟨4236099745061281200809735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11296265986830083202159293 4236099745061281200809735)
      ·
        refine ⟨6354149617591921801214603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4236099745061281200809735 6354149617591921801214603)
        ·
          refine ⟨9531224426387882701821905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6354149617591921801214603 9531224426387882701821905)
          ·
            refine ⟨7148418319790912026366429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9531224426387882701821905 7148418319790912026366429)
            ·
              refine ⟨2680656869921592009887411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7148418319790912026366429 2680656869921592009887411)
              ·
                refine ⟨4020985304882388014831117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2680656869921592009887411 4020985304882388014831117)
                ·
                  refine ⟨1507869489330895505561669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4020985304882388014831117 1507869489330895505561669)
                  ·
                    refine ⟨282725529249542907292813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1507869489330895505561669 282725529249542907292813)
                    ·
                      rfl

theorem cell22_825909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 3, 4].length) (baseStart_825909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825909 prefixEnd_825909 := by exact prefixLift 825909
  have htrace : WordTrace (prefixWord ++ tailWord_825909) baseStart_825909 baseEnd_825909 := by
    simpa [prefixWord, tailWord_825909, baseEnd_825909] using wordTrace_append hprefix tailTrace_825909
  have hstable : (prefixWord ++ tailWord_825909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825909).length < 2 ^ (prefixWord ++ tailWord_825909).sum := by decide
  have hdescent : baseEnd_825909 < baseStart_825909 := by decide
  rcases family_descends (prefixWord ++ tailWord_825909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_825956 : List Nat := [2, 3, 1, 1, 2, 2, 1, 5, 2, 3]
def baseStart_825956 : Nat := 118140960795 + 825956 * 2 ^ 59
def prefixEnd_825956 : Nat := 4983230072969 + 3 ^ 40 * 825956 * 2
def baseEnd_825956 : Nat := 282741618310050451367669

theorem tailTrace_825956 : CollatzResearch.WordTrace tailWord_825956 prefixEnd_825956 282741618310050451367669 := by
  unfold tailWord_825956
  simp only [CollatzResearch.WordTrace]
  refine ⟨15062545097854974449692861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20083393463806632599590481 15062545097854974449692861)
  ·
    refine ⟨5648454411695615418634823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15062545097854974449692861 5648454411695615418634823)
    ·
      refine ⟨8472681617543423127952235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5648454411695615418634823 8472681617543423127952235)
      ·
        refine ⟨12709022426315134691928353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8472681617543423127952235 12709022426315134691928353)
        ·
          refine ⟨9531766819736351018946265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12709022426315134691928353 9531766819736351018946265)
          ·
            refine ⟨7148825114802263264209699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9531766819736351018946265 7148825114802263264209699)
            ·
              refine ⟨10723237672203394896314549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7148825114802263264209699 10723237672203394896314549)
              ·
                refine ⟨1005303531769068271529489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10723237672203394896314549 1005303531769068271529489)
                ·
                  refine ⟨753977648826801203647117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1005303531769068271529489 753977648826801203647117)
                  ·
                    refine ⟨282741618310050451367669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 753977648826801203647117 282741618310050451367669)
                    ·
                      rfl

theorem cell22_825956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 5, 2, 3].length) (baseStart_825956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_825956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_825956 prefixEnd_825956 := by exact prefixLift 825956
  have htrace : WordTrace (prefixWord ++ tailWord_825956) baseStart_825956 baseEnd_825956 := by
    simpa [prefixWord, tailWord_825956, baseEnd_825956] using wordTrace_append hprefix tailTrace_825956
  have hstable : (prefixWord ++ tailWord_825956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_825956).length < 2 ^ (prefixWord ++ tailWord_825956).sum := by decide
  have hdescent : baseEnd_825956 < baseStart_825956 := by decide
  rcases family_descends (prefixWord ++ tailWord_825956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826035 : List Nat := [1, 1, 1, 2, 3, 6, 1, 3, 1, 3]
def baseStart_826035 : Nat := 118140960795 + 826035 * 2 ^ 59
def prefixEnd_826035 : Nat := 4983230072969 + 3 ^ 40 * 826035 * 2
def baseEnd_826035 : Nat := 282768661624520578642427

theorem tailTrace_826035 : CollatzResearch.WordTrace tailWord_826035 prefixEnd_826035 282768661624520578642427 := by
  unfold tailWord_826035
  simp only [CollatzResearch.WordTrace]
  refine ⟨30127971562423745391511559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20085314374949163594341039 30127971562423745391511559)
  ·
    refine ⟨45191957343635618087267339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30127971562423745391511559 45191957343635618087267339)
    ·
      refine ⟨67787936015453427130901009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45191957343635618087267339 67787936015453427130901009)
      ·
        refine ⟨50840952011590070348175757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67787936015453427130901009 50840952011590070348175757)
        ·
          refine ⟨19065357004346276380565909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50840952011590070348175757 19065357004346276380565909)
          ·
            refine ⟨893688609578731705339027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19065357004346276380565909 893688609578731705339027)
            ·
              refine ⟨1340532914368097558008541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893688609578731705339027 1340532914368097558008541)
              ·
                refine ⟨502699842888036584253203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1340532914368097558008541 502699842888036584253203)
                ·
                  refine ⟨754049764332054876379805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 502699842888036584253203 754049764332054876379805)
                  ·
                    refine ⟨282768661624520578642427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 754049764332054876379805 282768661624520578642427)
                    ·
                      rfl

theorem cell22_826035_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 3, 1, 3].length) (baseStart_826035 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826035 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826035 prefixEnd_826035 := by exact prefixLift 826035
  have htrace : WordTrace (prefixWord ++ tailWord_826035) baseStart_826035 baseEnd_826035 := by
    simpa [prefixWord, tailWord_826035, baseEnd_826035] using wordTrace_append hprefix tailTrace_826035
  have hstable : (prefixWord ++ tailWord_826035).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826035).length < 2 ^ (prefixWord ++ tailWord_826035).sum := by decide
  have hdescent : baseEnd_826035 < baseStart_826035 := by decide
  rcases family_descends (prefixWord ++ tailWord_826035) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826052 : List Nat := [2, 3, 3, 1, 1, 3, 3, 2, 1, 3]
def baseStart_826052 : Nat := 118140960795 + 826052 * 2 ^ 59
def prefixEnd_826052 : Nat := 4983230072969 + 3 ^ 40 * 826052 * 2
def baseEnd_826052 : Nat := 282774481071938200967375

theorem tailTrace_826052 : CollatzResearch.WordTrace tailWord_826052 prefixEnd_826052 282774481071938200967375 := by
  unfold tailWord_826052
  simp only [CollatzResearch.WordTrace]
  refine ⟨15064295801681078647440205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20085727735574771529920273 15064295801681078647440205)
  ·
    refine ⟨5649110925630404492790077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15064295801681078647440205 5649110925630404492790077)
    ·
      refine ⟨2118416597111401684796279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5649110925630404492790077 2118416597111401684796279)
      ·
        refine ⟨3177624895667102527194419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2118416597111401684796279 3177624895667102527194419)
        ·
          refine ⟨4766437343500653790791629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3177624895667102527194419 4766437343500653790791629)
          ·
            refine ⟨1787414003812745171546861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4766437343500653790791629 1787414003812745171546861)
            ·
              refine ⟨670280251429779439330073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1787414003812745171546861 670280251429779439330073)
              ·
                refine ⟨502710188572334579497555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 670280251429779439330073 502710188572334579497555)
                ·
                  refine ⟨754065282858501869246333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 502710188572334579497555 754065282858501869246333)
                  ·
                    refine ⟨282774481071938200967375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 754065282858501869246333 282774481071938200967375)
                    ·
                      rfl

theorem cell22_826052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 3, 2, 1, 3].length) (baseStart_826052 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826052 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826052 prefixEnd_826052 := by exact prefixLift 826052
  have htrace : WordTrace (prefixWord ++ tailWord_826052) baseStart_826052 baseEnd_826052 := by
    simpa [prefixWord, tailWord_826052, baseEnd_826052] using wordTrace_append hprefix tailTrace_826052
  have hstable : (prefixWord ++ tailWord_826052).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826052).length < 2 ^ (prefixWord ++ tailWord_826052).sum := by decide
  have hdescent : baseEnd_826052 < baseStart_826052 := by decide
  rcases family_descends (prefixWord ++ tailWord_826052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826089 : List Nat := [1, 2, 1, 1, 1, 2, 4, 3, 1, 6]
def baseStart_826089 : Nat := 118140960795 + 826089 * 2 ^ 59
def prefixEnd_826089 : Nat := 4983230072969 + 3 ^ 40 * 826089 * 2
def baseEnd_826089 : Nat := 282787146928082437792261

theorem tailTrace_826089 : CollatzResearch.WordTrace tailWord_826089 prefixEnd_826089 282787146928082437792261 := by
  unfold tailWord_826089
  simp only [CollatzResearch.WordTrace]
  refine ⟨30129941104228112613977321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20086627402818741742651547 30129941104228112613977321)
  ·
    refine ⟨22597455828171084460482991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30129941104228112613977321 22597455828171084460482991)
    ·
      refine ⟨33896183742256626690724487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22597455828171084460482991 33896183742256626690724487)
      ·
        refine ⟨50844275613384940036086731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33896183742256626690724487 50844275613384940036086731)
        ·
          refine ⟨76266413420077410054130097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50844275613384940036086731 76266413420077410054130097)
          ·
            refine ⟨57199810065058057540597573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76266413420077410054130097 57199810065058057540597573)
            ·
              refine ⟨10724964387198385788862045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57199810065058057540597573 10724964387198385788862045)
              ·
                refine ⟨4021861645199394670823267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10724964387198385788862045 4021861645199394670823267)
                ·
                  refine ⟨6032792467799092006234901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4021861645199394670823267 6032792467799092006234901)
                  ·
                    refine ⟨282787146928082437792261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6032792467799092006234901 282787146928082437792261)
                    ·
                      rfl

theorem cell22_826089_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 4, 3, 1, 6].length) (baseStart_826089 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826089 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826089 prefixEnd_826089 := by exact prefixLift 826089
  have htrace : WordTrace (prefixWord ++ tailWord_826089) baseStart_826089 baseEnd_826089 := by
    simpa [prefixWord, tailWord_826089, baseEnd_826089] using wordTrace_append hprefix tailTrace_826089
  have hstable : (prefixWord ++ tailWord_826089).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826089).length < 2 ^ (prefixWord ++ tailWord_826089).sum := by decide
  have hdescent : baseEnd_826089 < baseStart_826089 := by decide
  rcases family_descends (prefixWord ++ tailWord_826089) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826093 : List Nat := [1, 5, 1, 2, 1, 1, 2, 5, 4]
def baseStart_826093 : Nat := 118140960795 + 826093 * 2 ^ 59
def prefixEnd_826093 : Nat := 4983230072969 + 3 ^ 40 * 826093 * 2
def baseEnd_826093 : Nat := 94262838736609253564083

theorem tailTrace_826093 : CollatzResearch.WordTrace tailWord_826093 prefixEnd_826093 94262838736609253564083 := by
  unfold tailWord_826093
  simp only [CollatzResearch.WordTrace]
  refine ⟨30130086996213621297122933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20086724664142414198081955 30130086996213621297122933)
  ·
    refine ⟨2824695655895026996605275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30130086996213621297122933 2824695655895026996605275)
    ·
      refine ⟨4237043483842540494907913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2824695655895026996605275 4237043483842540494907913)
      ·
        refine ⟨3177782612881905371180935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4237043483842540494907913 3177782612881905371180935)
        ·
          refine ⟨4766673919322858056771403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3177782612881905371180935 4766673919322858056771403)
          ·
            refine ⟨7150010878984287085157105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4766673919322858056771403 7150010878984287085157105)
            ·
              refine ⟨5362508159238215313867829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7150010878984287085157105 5362508159238215313867829)
              ·
                refine ⟨502735139928582685675109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5362508159238215313867829 502735139928582685675109)
                ·
                  refine ⟨94262838736609253564083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 502735139928582685675109 94262838736609253564083)
                  ·
                    rfl

theorem cell22_826093_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 5, 4].length) (baseStart_826093 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826093 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826093 prefixEnd_826093 := by exact prefixLift 826093
  have htrace : WordTrace (prefixWord ++ tailWord_826093) baseStart_826093 baseEnd_826093 := by
    simpa [prefixWord, tailWord_826093, baseEnd_826093] using wordTrace_append hprefix tailTrace_826093
  have hstable : (prefixWord ++ tailWord_826093).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826093).length < 2 ^ (prefixWord ++ tailWord_826093).sum := by decide
  have hdescent : baseEnd_826093 < baseStart_826093 := by decide
  rcases family_descends (prefixWord ++ tailWord_826093) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826106 : List Nat := [3, 1, 1, 1, 1, 3, 4, 2, 2, 4]
def baseStart_826106 : Nat := 118140960795 + 826106 * 2 ^ 59
def prefixEnd_826106 : Nat := 4983230072969 + 3 ^ 40 * 826106 * 2
def baseEnd_826106 : Nat := 282792966375500060117209

theorem tailTrace_826106 : CollatzResearch.WordTrace tailWord_826106 prefixEnd_826106 282792966375500060117209 := by
  unfold tailWord_826106
  simp only [CollatzResearch.WordTrace]
  refine ⟨7532640286291631129336543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20087040763444349678230781 7532640286291631129336543)
  ·
    refine ⟨11298960429437446694004815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7532640286291631129336543 11298960429437446694004815)
    ·
      refine ⟨16948440644156170041007223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11298960429437446694004815 16948440644156170041007223)
      ·
        refine ⟨25422660966234255061510835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16948440644156170041007223 25422660966234255061510835)
        ·
          refine ⟨38133991449351382592266253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25422660966234255061510835 38133991449351382592266253)
          ·
            refine ⟨14300246793506768472099845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38133991449351382592266253 14300246793506768472099845)
            ·
              refine ⟨2681296273782519088518721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14300246793506768472099845 2681296273782519088518721)
              ·
                refine ⟨2010972205336889316389041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2681296273782519088518721 2010972205336889316389041)
                ·
                  refine ⟨1508229154002666987291781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2010972205336889316389041 1508229154002666987291781)
                  ·
                    refine ⟨282792966375500060117209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1508229154002666987291781 282792966375500060117209)
                    ·
                      rfl

theorem cell22_826106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 2, 4].length) (baseStart_826106 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826106 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826106 prefixEnd_826106 := by exact prefixLift 826106
  have htrace : WordTrace (prefixWord ++ tailWord_826106) baseStart_826106 baseEnd_826106 := by
    simpa [prefixWord, tailWord_826106, baseEnd_826106] using wordTrace_append hprefix tailTrace_826106
  have hstable : (prefixWord ++ tailWord_826106).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826106).length < 2 ^ (prefixWord ++ tailWord_826106).sum := by decide
  have hdescent : baseEnd_826106 < baseStart_826106 := by decide
  rcases family_descends (prefixWord ++ tailWord_826106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826108 : List Nat := [2, 2, 2, 1, 3, 2, 1, 4, 2, 3]
def baseStart_826108 : Nat := 118140960795 + 826108 * 2 ^ 59
def prefixEnd_826108 : Nat := 4983230072969 + 3 ^ 40 * 826108 * 2
def baseEnd_826108 : Nat := 282793651016372721567203

theorem tailTrace_826108 : CollatzResearch.WordTrace tailWord_826108 prefixEnd_826108 282793651016372721567203 := by
  unfold tailWord_826108
  simp only [CollatzResearch.WordTrace]
  refine ⟨15065317045579639429459489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20087089394106185905945985 15065317045579639429459489)
  ·
    refine ⟨11298987784184729572094617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15065317045579639429459489 11298987784184729572094617)
    ·
      refine ⟨8474240838138547179070963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11298987784184729572094617 8474240838138547179070963)
      ·
        refine ⟨12711361257207820768606445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8474240838138547179070963 12711361257207820768606445)
        ·
          refine ⟨4766760471452932788227417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12711361257207820768606445 4766760471452932788227417)
          ·
            refine ⟨3575070353589699591170563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4766760471452932788227417 3575070353589699591170563)
            ·
              refine ⟨5362605530384549386755845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3575070353589699591170563 5362605530384549386755845)
              ·
                refine ⟨1005488536947103010016721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5362605530384549386755845 1005488536947103010016721)
                ·
                  refine ⟨754116402710327257512541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1005488536947103010016721 754116402710327257512541)
                  ·
                    refine ⟨282793651016372721567203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 754116402710327257512541 282793651016372721567203)
                    ·
                      rfl

theorem cell22_826108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 4, 2, 3].length) (baseStart_826108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826108 prefixEnd_826108 := by exact prefixLift 826108
  have htrace : WordTrace (prefixWord ++ tailWord_826108) baseStart_826108 baseEnd_826108 := by
    simpa [prefixWord, tailWord_826108, baseEnd_826108] using wordTrace_append hprefix tailTrace_826108
  have hstable : (prefixWord ++ tailWord_826108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826108).length < 2 ^ (prefixWord ++ tailWord_826108).sum := by decide
  have hdescent : baseEnd_826108 < baseStart_826108 := by decide
  rcases family_descends (prefixWord ++ tailWord_826108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826110 : List Nat := [4, 2, 2, 1, 2, 2, 1, 4, 4]
def baseStart_826110 : Nat := 118140960795 + 826110 * 2 ^ 59
def prefixEnd_826110 : Nat := 4983230072969 + 3 ^ 40 * 826110 * 2
def baseEnd_826110 : Nat := 94264778552415127672399

theorem tailTrace_826110 : CollatzResearch.WordTrace tailWord_826110 prefixEnd_826110 94264778552415127672399 := by
  unfold tailWord_826110
  simp only [CollatzResearch.WordTrace]
  refine ⟨3766338379644004150061473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20087138024768022133661189 3766338379644004150061473)
  ·
    refine ⟨2824753784733003112546105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3766338379644004150061473 2824753784733003112546105)
    ·
      refine ⟨2118565338549752334409579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2824753784733003112546105 2118565338549752334409579)
      ·
        refine ⟨3177848007824628501614369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2118565338549752334409579 3177848007824628501614369)
        ·
          refine ⟨2383386005868471376210777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3177848007824628501614369 2383386005868471376210777)
          ·
            refine ⟨1787539504401353532158083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2383386005868471376210777 1787539504401353532158083)
            ·
              refine ⟨2681309256602030298237125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1787539504401353532158083 2681309256602030298237125)
              ·
                refine ⟨502745485612880680919461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2681309256602030298237125 502745485612880680919461)
                ·
                  refine ⟨94264778552415127672399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 502745485612880680919461 94264778552415127672399)
                  ·
                    rfl

theorem cell22_826110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 4, 4].length) (baseStart_826110 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826110 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826110 prefixEnd_826110 := by exact prefixLift 826110
  have htrace : WordTrace (prefixWord ++ tailWord_826110) baseStart_826110 baseEnd_826110 := by
    simpa [prefixWord, tailWord_826110, baseEnd_826110] using wordTrace_append hprefix tailTrace_826110
  have hstable : (prefixWord ++ tailWord_826110).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826110).length < 2 ^ (prefixWord ++ tailWord_826110).sum := by decide
  have hdescent : baseEnd_826110 < baseStart_826110 := by decide
  rcases family_descends (prefixWord ++ tailWord_826110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826170 : List Nat := [3, 1, 1, 1, 6, 1, 2, 1, 3, 3]
def baseStart_826170 : Nat := 118140960795 + 826170 * 2 ^ 59
def prefixEnd_826170 : Nat := 4983230072969 + 3 ^ 40 * 826170 * 2
def baseEnd_826170 : Nat := 282814874883425226517013

theorem tailTrace_826170 : CollatzResearch.WordTrace tailWord_826170 prefixEnd_826170 282814874883425226517013 := by
  unfold tailWord_826170
  simp only [CollatzResearch.WordTrace]
  refine ⟨7533223854233665861918991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20088596944623108965117309 7533223854233665861918991)
  ·
    refine ⟨11299835781350498792878487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7533223854233665861918991 11299835781350498792878487)
    ·
      refine ⟨16949753672025748189317731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11299835781350498792878487 16949753672025748189317731)
      ·
        refine ⟨25424630508038622283976597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16949753672025748189317731 25424630508038622283976597)
        ·
          refine ⟨1191779555064310419561403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25424630508038622283976597 1191779555064310419561403)
          ·
            refine ⟨1787669332596465629342105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1191779555064310419561403 1787669332596465629342105)
            ·
              refine ⟨1340751999447349222006579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1787669332596465629342105 1340751999447349222006579)
              ·
                refine ⟨2011127999171023833009869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1340751999447349222006579 2011127999171023833009869)
                ·
                  refine ⟨754172999689133937378701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2011127999171023833009869 754172999689133937378701)
                  ·
                    refine ⟨282814874883425226517013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 754172999689133937378701 282814874883425226517013)
                    ·
                      rfl

theorem cell22_826170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 1, 2, 1, 3, 3].length) (baseStart_826170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826170 prefixEnd_826170 := by exact prefixLift 826170
  have htrace : WordTrace (prefixWord ++ tailWord_826170) baseStart_826170 baseEnd_826170 := by
    simpa [prefixWord, tailWord_826170, baseEnd_826170] using wordTrace_append hprefix tailTrace_826170
  have hstable : (prefixWord ++ tailWord_826170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826170).length < 2 ^ (prefixWord ++ tailWord_826170).sum := by decide
  have hdescent : baseEnd_826170 < baseStart_826170 := by decide
  rcases family_descends (prefixWord ++ tailWord_826170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826204 : List Nat := [2, 2, 4, 2, 1, 3, 1, 3, 1, 3]
def baseStart_826204 : Nat := 118140960795 + 826204 * 2 ^ 59
def prefixEnd_826204 : Nat := 4983230072969 + 3 ^ 40 * 826204 * 2
def baseEnd_826204 : Nat := 282826513778260471166909

theorem tailTrace_826204 : CollatzResearch.WordTrace tailWord_826204 prefixEnd_826204 282826513778260471166909 := by
  unfold tailWord_826204
  simp only [CollatzResearch.WordTrace]
  refine ⟨15067067749405743627206833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20089423665874324836275777 15067067749405743627206833)
  ·
    refine ⟨11300300812054307720405125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15067067749405743627206833 11300300812054307720405125)
    ·
      refine ⟨2118806402260182697575961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11300300812054307720405125 2118806402260182697575961)
      ·
        refine ⟨1589104801695137023181971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2118806402260182697575961 1589104801695137023181971)
        ·
          refine ⟨2383657202542705534772957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1589104801695137023181971 2383657202542705534772957)
          ·
            refine ⟨893871450953514575539859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2383657202542705534772957 893871450953514575539859)
            ·
              refine ⟨1340807176430271863309789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893871450953514575539859 1340807176430271863309789)
              ·
                refine ⟨502802691161351948741171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1340807176430271863309789 502802691161351948741171)
                ·
                  refine ⟨754204036742027923111757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 502802691161351948741171 754204036742027923111757)
                  ·
                    refine ⟨282826513778260471166909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 754204036742027923111757 282826513778260471166909)
                    ·
                      rfl

theorem cell22_826204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 3, 1, 3, 1, 3].length) (baseStart_826204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826204 prefixEnd_826204 := by exact prefixLift 826204
  have htrace : WordTrace (prefixWord ++ tailWord_826204) baseStart_826204 baseEnd_826204 := by
    simpa [prefixWord, tailWord_826204, baseEnd_826204] using wordTrace_append hprefix tailTrace_826204
  have hstable : (prefixWord ++ tailWord_826204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826204).length < 2 ^ (prefixWord ++ tailWord_826204).sum := by decide
  have hdescent : baseEnd_826204 < baseStart_826204 := by decide
  rcases family_descends (prefixWord ++ tailWord_826204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826213 : List Nat := [1, 3, 1, 3, 1, 1, 4, 3, 1, 4]
def baseStart_826213 : Nat := 118140960795 + 826213 * 2 ^ 59
def prefixEnd_826213 : Nat := 4983230072969 + 3 ^ 40 * 826213 * 2
def baseEnd_826213 : Nat := 282829594662187447691881

theorem tailTrace_826213 : CollatzResearch.WordTrace tailWord_826213 prefixEnd_826213 282829594662187447691881 := by
  unfold tailWord_826213
  simp only [CollatzResearch.WordTrace]
  refine ⟨30134463755778881791491293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20089642503852587860994195 30134463755778881791491293)
  ·
    refine ⟨11300423908417080671809235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30134463755778881791491293 11300423908417080671809235)
    ·
      refine ⟨16950635862625621007713853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11300423908417080671809235 16950635862625621007713853)
      ·
        refine ⟨6356488448484607877892695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16950635862625621007713853 6356488448484607877892695)
        ·
          refine ⟨9534732672726911816839043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6356488448484607877892695 9534732672726911816839043)
          ·
            refine ⟨14302099009090367725258565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9534732672726911816839043 14302099009090367725258565)
            ·
              refine ⟨2681643564204443948485981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14302099009090367725258565 2681643564204443948485981)
              ·
                refine ⟨1005616336576666480682243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2681643564204443948485981 1005616336576666480682243)
                ·
                  refine ⟨1508424504864999721023365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1005616336576666480682243 1508424504864999721023365)
                  ·
                    refine ⟨282829594662187447691881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1508424504864999721023365 282829594662187447691881)
                    ·
                      rfl

theorem cell22_826213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 4, 3, 1, 4].length) (baseStart_826213 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826213 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826213 prefixEnd_826213 := by exact prefixLift 826213
  have htrace : WordTrace (prefixWord ++ tailWord_826213) baseStart_826213 baseEnd_826213 := by
    simpa [prefixWord, tailWord_826213, baseEnd_826213] using wordTrace_append hprefix tailTrace_826213
  have hstable : (prefixWord ++ tailWord_826213).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826213).length < 2 ^ (prefixWord ++ tailWord_826213).sum := by decide
  have hdescent : baseEnd_826213 < baseStart_826213 := by decide
  rcases family_descends (prefixWord ++ tailWord_826213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826279 : List Nat := [1, 1, 6, 1, 3, 2, 2, 2, 4]
def baseStart_826279 : Nat := 118140960795 + 826279 * 2 ^ 59
def prefixEnd_826279 : Nat := 4983230072969 + 3 ^ 40 * 826279 * 2
def baseEnd_826279 : Nat := 94284062603661758513893

theorem tailTrace_826279 : CollatzResearch.WordTrace tailWord_826279 prefixEnd_826279 94284062603661758513893 := by
  unfold tailWord_826279
  simp only [CollatzResearch.WordTrace]
  refine ⟨30136870973539775063393891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20091247315693183375595927 30136870973539775063393891)
  ·
    refine ⟨45205306460309662595090837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30136870973539775063393891 45205306460309662595090837)
    ·
      refine ⟨2118998740327015434144883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45205306460309662595090837 2118998740327015434144883)
      ·
        refine ⟨3178498110490523151217325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2118998740327015434144883 3178498110490523151217325)
        ·
          refine ⟨1191936791433946181706497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3178498110490523151217325 1191936791433946181706497)
          ·
            refine ⟨893952593575459636279873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1191936791433946181706497 893952593575459636279873)
            ·
              refine ⟨670464445181594727209905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 893952593575459636279873 670464445181594727209905)
              ·
                refine ⟨502848333886196045407429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 670464445181594727209905 502848333886196045407429)
                ·
                  refine ⟨94284062603661758513893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 502848333886196045407429 94284062603661758513893)
                  ·
                    rfl

theorem cell22_826279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 2, 4].length) (baseStart_826279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826279 prefixEnd_826279 := by exact prefixLift 826279
  have htrace : WordTrace (prefixWord ++ tailWord_826279) baseStart_826279 baseEnd_826279 := by
    simpa [prefixWord, tailWord_826279, baseEnd_826279] using wordTrace_append hprefix tailTrace_826279
  have hstable : (prefixWord ++ tailWord_826279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826279).length < 2 ^ (prefixWord ++ tailWord_826279).sum := by decide
  have hdescent : baseEnd_826279 < baseStart_826279 := by decide
  rcases family_descends (prefixWord ++ tailWord_826279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826393 : List Nat := [1, 2, 1, 2, 1, 1, 5, 1, 4, 4]
def baseStart_826393 : Nat := 118140960795 + 826393 * 2 ^ 59
def prefixEnd_826393 : Nat := 4983230072969 + 3 ^ 40 * 826393 * 2
def baseEnd_826393 : Nat := 282891212340726978191329

theorem tailTrace_826393 : CollatzResearch.WordTrace tailWord_826393 prefixEnd_826393 282891212340726978191329 := by
  unfold tailWord_826393
  simp only [CollatzResearch.WordTrace]
  refine ⟨30141028895126772533043833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20094019263417848355362555 30141028895126772533043833)
  ·
    refine ⟨22605771671345079399782875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30141028895126772533043833 22605771671345079399782875)
    ·
      refine ⟨33908657507017619099674313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22605771671345079399782875 33908657507017619099674313)
      ·
        refine ⟨25431493130263214324755735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33908657507017619099674313 25431493130263214324755735)
        ·
          refine ⟨38147239695394821487133603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25431493130263214324755735 38147239695394821487133603)
          ·
            refine ⟨57220859543092232230700405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38147239695394821487133603 57220859543092232230700405)
            ·
              refine ⟨5364455582164896771628163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57220859543092232230700405 5364455582164896771628163)
              ·
                refine ⟨8046683373247345157442245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5364455582164896771628163 8046683373247345157442245)
                ·
                  refine ⟨1508753132483877217020421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8046683373247345157442245 1508753132483877217020421)
                  ·
                    refine ⟨282891212340726978191329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1508753132483877217020421 282891212340726978191329)
                    ·
                      rfl

theorem cell22_826393_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 5, 1, 4, 4].length) (baseStart_826393 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826393 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826393 prefixEnd_826393 := by exact prefixLift 826393
  have htrace : WordTrace (prefixWord ++ tailWord_826393) baseStart_826393 baseEnd_826393 := by
    simpa [prefixWord, tailWord_826393, baseEnd_826393] using wordTrace_append hprefix tailTrace_826393
  have hstable : (prefixWord ++ tailWord_826393).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826393).length < 2 ^ (prefixWord ++ tailWord_826393).sum := by decide
  have hdescent : baseEnd_826393 < baseStart_826393 := by decide
  rcases family_descends (prefixWord ++ tailWord_826393) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826397 : List Nat := [1, 4, 2, 2, 3, 2, 1, 1, 6]
def baseStart_826397 : Nat := 118140960795 + 826397 * 2 ^ 59
def prefixEnd_826397 : Nat := 4983230072969 + 3 ^ 40 * 826397 * 2
def baseEnd_826397 : Nat := 94297527207490767030439

theorem tailTrace_826397 : CollatzResearch.WordTrace tailWord_826397 prefixEnd_826397 94297527207490767030439 := by
  unfold tailWord_826397
  simp only [CollatzResearch.WordTrace]
  refine ⟨30141174787112281216189445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20094116524741520810792963 30141174787112281216189445)
  ·
    refine ⟨5651470272583552728035521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30141174787112281216189445 5651470272583552728035521)
    ·
      refine ⟨4238602704437664546026641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5651470272583552728035521 4238602704437664546026641)
      ·
        refine ⟨3178952028328248409519981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4238602704437664546026641 3178952028328248409519981)
        ·
          refine ⟨1192107010623093153569993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3178952028328248409519981 1192107010623093153569993)
          ·
            refine ⟨894080257967319865177495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1192107010623093153569993 894080257967319865177495)
            ·
              refine ⟨1341120386950979797766243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894080257967319865177495 1341120386950979797766243)
              ·
                refine ⟨2011680580426469696649365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1341120386950979797766243 2011680580426469696649365)
                ·
                  refine ⟨94297527207490767030439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2011680580426469696649365 94297527207490767030439)
                  ·
                    rfl

theorem cell22_826397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 1, 6].length) (baseStart_826397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826397 prefixEnd_826397 := by exact prefixLift 826397
  have htrace : WordTrace (prefixWord ++ tailWord_826397) baseStart_826397 baseEnd_826397 := by
    simpa [prefixWord, tailWord_826397, baseEnd_826397] using wordTrace_append hprefix tailTrace_826397
  have hstable : (prefixWord ++ tailWord_826397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826397).length < 2 ^ (prefixWord ++ tailWord_826397).sum := by decide
  have hdescent : baseEnd_826397 < baseStart_826397 := by decide
  rcases family_descends (prefixWord ++ tailWord_826397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826504 : List Nat := [2, 1, 3, 4, 2, 2, 1, 2, 5]
def baseStart_826504 : Nat := 118140960795 + 826504 * 2 ^ 59
def prefixEnd_826504 : Nat := 4983230072969 + 3 ^ 40 * 826504 * 2
def baseEnd_826504 : Nat := 94309736636386562888663

theorem tailTrace_826504 : CollatzResearch.WordTrace tailWord_826504 prefixEnd_826504 94309736636386562888663 := by
  unfold tailWord_826504
  simp only [CollatzResearch.WordTrace]
  refine ⟨15072538698862319245167283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20096718265149758993556377 15072538698862319245167283)
  ·
    refine ⟨22608808048293478867750925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15072538698862319245167283 22608808048293478867750925)
    ·
      refine ⟨8478303018110054575406597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22608808048293478867750925 8478303018110054575406597)
      ·
        refine ⟨1589681815895635232888737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8478303018110054575406597 1589681815895635232888737)
        ·
          refine ⟨1192261361921726424666553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1589681815895635232888737 1192261361921726424666553)
          ·
            refine ⟨894196021441294818499915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1192261361921726424666553 894196021441294818499915)
            ·
              refine ⟨1341294032161942227749873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894196021441294818499915 1341294032161942227749873)
              ·
                refine ⟨1005970524121456670812405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1341294032161942227749873 1005970524121456670812405)
                ·
                  refine ⟨94309736636386562888663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1005970524121456670812405 94309736636386562888663)
                  ·
                    rfl

theorem cell22_826504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 2, 2, 1, 2, 5].length) (baseStart_826504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826504 prefixEnd_826504 := by exact prefixLift 826504
  have htrace : WordTrace (prefixWord ++ tailWord_826504) baseStart_826504 baseEnd_826504 := by
    simpa [prefixWord, tailWord_826504, baseEnd_826504] using wordTrace_append hprefix tailTrace_826504
  have hstable : (prefixWord ++ tailWord_826504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826504).length < 2 ^ (prefixWord ++ tailWord_826504).sum := by decide
  have hdescent : baseEnd_826504 < baseStart_826504 := by decide
  rcases family_descends (prefixWord ++ tailWord_826504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826513 : List Nat := [1, 2, 2, 1, 1, 1, 1, 1, 1, 11]
def baseStart_826513 : Nat := 118140960795 + 826513 * 2 ^ 59
def prefixEnd_826513 : Nat := 4983230072969 + 3 ^ 40 * 826513 * 2
def baseEnd_826513 : Nat := 282932290793086665190961

theorem tailTrace_826513 : CollatzResearch.WordTrace tailWord_826513 prefixEnd_826513 282932290793086665190961 := by
  unfold tailWord_826513
  simp only [CollatzResearch.WordTrace]
  refine ⟨30145405654692033027412193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20096937103128022018274795 30145405654692033027412193)
  ·
    refine ⟨22609054241019024770559145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30145405654692033027412193 22609054241019024770559145)
    ·
      refine ⟨16956790680764268577919359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22609054241019024770559145 16956790680764268577919359)
      ·
        refine ⟨25435186021146402866879039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16956790680764268577919359 25435186021146402866879039)
        ·
          refine ⟨38152779031719604300318559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25435186021146402866879039 38152779031719604300318559)
          ·
            refine ⟨57229168547579406450477839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38152779031719604300318559 57229168547579406450477839)
            ·
              refine ⟨85843752821369109675716759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57229168547579406450477839 85843752821369109675716759)
              ·
                refine ⟨128765629232053664513575139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 85843752821369109675716759 128765629232053664513575139)
                ·
                  refine ⟨193148443848080496770362709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 128765629232053664513575139 193148443848080496770362709)
                  ·
                    refine ⟨282932290793086665190961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 11 193148443848080496770362709 282932290793086665190961)
                    ·
                      rfl

theorem cell22_826513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 11].length) (baseStart_826513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826513 prefixEnd_826513 := by exact prefixLift 826513
  have htrace : WordTrace (prefixWord ++ tailWord_826513) baseStart_826513 baseEnd_826513 := by
    simpa [prefixWord, tailWord_826513, baseEnd_826513] using wordTrace_append hprefix tailTrace_826513
  have hstable : (prefixWord ++ tailWord_826513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826513).length < 2 ^ (prefixWord ++ tailWord_826513).sum := by decide
  have hdescent : baseEnd_826513 < baseStart_826513 := by decide
  rcases family_descends (prefixWord ++ tailWord_826513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826581 : List Nat := [1, 3, 2, 4, 1, 1, 4, 1, 2, 3]
def baseStart_826581 : Nat := 118140960795 + 826581 * 2 ^ 59
def prefixEnd_826581 : Nat := 4983230072969 + 3 ^ 40 * 826581 * 2
def baseEnd_826581 : Nat := 282955568582757154490753

theorem tailTrace_826581 : CollatzResearch.WordTrace tailWord_826581 prefixEnd_826581 282955568582757154490753 := by
  unfold tailWord_826581
  simp only [CollatzResearch.WordTrace]
  refine ⟨30147885818445680640887597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20098590545630453760591731 30147885818445680640887597)
  ·
    refine ⟨11305457181917130240332849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30147885818445680640887597 11305457181917130240332849)
    ·
      refine ⟨8479092886437847680249637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11305457181917130240332849 8479092886437847680249637)
      ·
        refine ⟨1589829916207096440046807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8479092886437847680249637 1589829916207096440046807)
        ·
          refine ⟨2384744874310644660070211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1589829916207096440046807 2384744874310644660070211)
          ·
            refine ⟨3577117311465966990105317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2384744874310644660070211 3577117311465966990105317)
            ·
              refine ⟨670709495899868810644747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3577117311465966990105317 670709495899868810644747)
              ·
                refine ⟨1006064243849803215967121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 670709495899868810644747 1006064243849803215967121)
                ·
                  refine ⟨754548182887352411975341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1006064243849803215967121 754548182887352411975341)
                  ·
                    refine ⟨282955568582757154490753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 754548182887352411975341 282955568582757154490753)
                    ·
                      rfl

theorem cell22_826581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 4, 1, 2, 3].length) (baseStart_826581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826581 prefixEnd_826581 := by exact prefixLift 826581
  have htrace : WordTrace (prefixWord ++ tailWord_826581) baseStart_826581 baseEnd_826581 := by
    simpa [prefixWord, tailWord_826581, baseEnd_826581] using wordTrace_append hprefix tailTrace_826581
  have hstable : (prefixWord ++ tailWord_826581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826581).length < 2 ^ (prefixWord ++ tailWord_826581).sum := by decide
  have hdescent : baseEnd_826581 < baseStart_826581 := by decide
  rcases family_descends (prefixWord ++ tailWord_826581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826609 : List Nat := [1, 2, 2, 2, 2, 1, 1, 7, 1, 3]
def baseStart_826609 : Nat := 118140960795 + 826609 * 2 ^ 59
def prefixEnd_826609 : Nat := 4983230072969 + 3 ^ 40 * 826609 * 2
def baseEnd_826609 : Nat := 282965153554974414790667

theorem tailTrace_826609 : CollatzResearch.WordTrace tailWord_826609 prefixEnd_826609 282965153554974414790667 := by
  unfold tailWord_826609
  simp only [CollatzResearch.WordTrace]
  refine ⟨30148907062344241422906881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20099271374896160948604587 30148907062344241422906881)
  ·
    refine ⟨22611680296758181067180161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30148907062344241422906881 22611680296758181067180161)
    ·
      refine ⟨16958760222568635800385121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22611680296758181067180161 16958760222568635800385121)
      ·
        refine ⟨12719070166926476850288841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16958760222568635800385121 12719070166926476850288841)
        ·
          refine ⟨9539302625194857637716631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12719070166926476850288841 9539302625194857637716631)
          ·
            refine ⟨14308953937792286456574947, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9539302625194857637716631 14308953937792286456574947)
            ·
              refine ⟨21463430906688429684862421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14308953937792286456574947 21463430906688429684862421)
              ·
                refine ⟨503049161875510070738963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21463430906688429684862421 503049161875510070738963)
                ·
                  refine ⟨754573742813265106108445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 503049161875510070738963 754573742813265106108445)
                  ·
                    refine ⟨282965153554974414790667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 754573742813265106108445 282965153554974414790667)
                    ·
                      rfl

theorem cell22_826609_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 7, 1, 3].length) (baseStart_826609 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826609 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826609 prefixEnd_826609 := by exact prefixLift 826609
  have htrace : WordTrace (prefixWord ++ tailWord_826609) baseStart_826609 baseEnd_826609 := by
    simpa [prefixWord, tailWord_826609, baseEnd_826609] using wordTrace_append hprefix tailTrace_826609
  have hstable : (prefixWord ++ tailWord_826609).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826609).length < 2 ^ (prefixWord ++ tailWord_826609).sum := by decide
  have hdescent : baseEnd_826609 < baseStart_826609 := by decide
  rcases family_descends (prefixWord ++ tailWord_826609) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826652 : List Nat := [2, 2, 3, 1, 1, 1, 4, 1, 3, 4]
def baseStart_826652 : Nat := 118140960795 + 826652 * 2 ^ 59
def prefixEnd_826652 : Nat := 4983230072969 + 3 ^ 40 * 826652 * 2
def baseEnd_826652 : Nat := 282979873333736635965535

theorem tailTrace_826652 : CollatzResearch.WordTrace tailWord_826652 prefixEnd_826652 282979873333736635965535 := by
  unfold tailWord_826652
  simp only [CollatzResearch.WordTrace]
  refine ⟨15075237700594229883361105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20100316934125639844481473 15075237700594229883361105)
  ·
    refine ⟨11306428275445672412520829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15075237700594229883361105 11306428275445672412520829)
    ·
      refine ⟨4239910603292127154695311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11306428275445672412520829 4239910603292127154695311)
      ·
        refine ⟨6359865904938190732042967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4239910603292127154695311 6359865904938190732042967)
        ·
          refine ⟨9539798857407286098064451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6359865904938190732042967 9539798857407286098064451)
          ·
            refine ⟨14309698286110929147096677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9539798857407286098064451 14309698286110929147096677)
            ·
              refine ⟨2683068428645799215080627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14309698286110929147096677 2683068428645799215080627)
              ·
                refine ⟨4024602642968698822620941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2683068428645799215080627 4024602642968698822620941)
                ·
                  refine ⟨1509225991113262058482853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4024602642968698822620941 1509225991113262058482853)
                  ·
                    refine ⟨282979873333736635965535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1509225991113262058482853 282979873333736635965535)
                    ·
                      rfl

theorem cell22_826652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 4, 1, 3, 4].length) (baseStart_826652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826652 prefixEnd_826652 := by exact prefixLift 826652
  have htrace : WordTrace (prefixWord ++ tailWord_826652) baseStart_826652 baseEnd_826652 := by
    simpa [prefixWord, tailWord_826652, baseEnd_826652] using wordTrace_append hprefix tailTrace_826652
  have hstable : (prefixWord ++ tailWord_826652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826652).length < 2 ^ (prefixWord ++ tailWord_826652).sum := by decide
  have hdescent : baseEnd_826652 < baseStart_826652 := by decide
  rcases family_descends (prefixWord ++ tailWord_826652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826665 : List Nat := [1, 2, 1, 1, 1, 1, 1, 2, 7, 5]
def baseStart_826665 : Nat := 118140960795 + 826665 * 2 ^ 59
def prefixEnd_826665 : Nat := 4983230072969 + 3 ^ 40 * 826665 * 2
def baseEnd_826665 : Nat := 282984323499408935390495

theorem tailTrace_826665 : CollatzResearch.WordTrace tailWord_826665 prefixEnd_826665 282984323499408935390495 := by
  unfold tailWord_826665
  simp only [CollatzResearch.WordTrace]
  refine ⟨30150949550141362986945449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20100633033427575324630299 30150949550141362986945449)
  ·
    refine ⟨22613212162606022240209087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30150949550141362986945449 22613212162606022240209087)
    ·
      refine ⟨33919818243909033360313631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22613212162606022240209087 33919818243909033360313631)
      ·
        refine ⟨50879727365863550040470447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33919818243909033360313631 50879727365863550040470447)
        ·
          refine ⟨76319591048795325060705671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50879727365863550040470447 76319591048795325060705671)
          ·
            refine ⟨114479386573192987591058507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76319591048795325060705671 114479386573192987591058507)
            ·
              refine ⟨171719079859789481386587761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 114479386573192987591058507 171719079859789481386587761)
              ·
                refine ⟨128789309894842111039940821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 171719079859789481386587761 128789309894842111039940821)
                ·
                  refine ⟨3018499450660361977498613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 128789309894842111039940821 3018499450660361977498613)
                  ·
                    refine ⟨282984323499408935390495, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3018499450660361977498613 282984323499408935390495)
                    ·
                      rfl

theorem cell22_826665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 2, 7, 5].length) (baseStart_826665 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826665 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826665 prefixEnd_826665 := by exact prefixLift 826665
  have htrace : WordTrace (prefixWord ++ tailWord_826665) baseStart_826665 baseEnd_826665 := by
    simpa [prefixWord, tailWord_826665, baseEnd_826665] using wordTrace_append hprefix tailTrace_826665
  have hstable : (prefixWord ++ tailWord_826665).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826665).length < 2 ^ (prefixWord ++ tailWord_826665).sum := by decide
  have hdescent : baseEnd_826665 < baseStart_826665 := by decide
  rcases family_descends (prefixWord ++ tailWord_826665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826684 : List Nat := [2, 2, 2, 2, 1, 3, 2, 4, 4]
def baseStart_826684 : Nat := 118140960795 + 826684 * 2 ^ 59
def prefixEnd_826684 : Nat := 4983230072969 + 3 ^ 40 * 826684 * 2
def baseEnd_826684 : Nat := 94330275862566406388479

theorem tailTrace_826684 : CollatzResearch.WordTrace tailWord_826684 prefixEnd_826684 94330275862566406388479 := by
  unfold tailWord_826684
  simp only [CollatzResearch.WordTrace]
  refine ⟨15075821268536264615943553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20101095024715019487924737 15075821268536264615943553)
  ·
    refine ⟨11306865951402198461957665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15075821268536264615943553 11306865951402198461957665)
    ·
      refine ⟨8480149463551648846468249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11306865951402198461957665 8480149463551648846468249)
      ·
        refine ⟨6360112097663736634851187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8480149463551648846468249 6360112097663736634851187)
        ·
          refine ⟨9540168146495604952276781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6360112097663736634851187 9540168146495604952276781)
          ·
            refine ⟨3577563054935851857103793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9540168146495604952276781 3577563054935851857103793)
            ·
              refine ⟨2683172291201888892827845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3577563054935851857103793 2683172291201888892827845)
              ·
                refine ⟨503094804600354167405221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2683172291201888892827845 503094804600354167405221)
                ·
                  refine ⟨94330275862566406388479, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 503094804600354167405221 94330275862566406388479)
                  ·
                    rfl

theorem cell22_826684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 2, 4, 4].length) (baseStart_826684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826684 prefixEnd_826684 := by exact prefixLift 826684
  have htrace : WordTrace (prefixWord ++ tailWord_826684) baseStart_826684 baseEnd_826684 := by
    simpa [prefixWord, tailWord_826684, baseEnd_826684] using wordTrace_append hprefix tailTrace_826684
  have hstable : (prefixWord ++ tailWord_826684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826684).length < 2 ^ (prefixWord ++ tailWord_826684).sum := by decide
  have hdescent : baseEnd_826684 < baseStart_826684 := by decide
  rcases family_descends (prefixWord ++ tailWord_826684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826750 : List Nat := [4, 2, 3, 2, 1, 1, 1, 3, 2, 3]
def baseStart_826750 : Nat := 118140960795 + 826750 * 2 ^ 59
def prefixEnd_826750 : Nat := 4983230072969 + 3 ^ 40 * 826750 * 2
def baseEnd_826750 : Nat := 283013420736497047015235

theorem tailTrace_826750 : CollatzResearch.WordTrace tailWord_826750 prefixEnd_826750 283013420736497047015235 := by
  unfold tailWord_826750
  simp only [CollatzResearch.WordTrace]
  refine ⟨3769256219354177812973713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20102699836555615002526469 3769256219354177812973713)
  ·
    refine ⟨2826942164515633359730285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3769256219354177812973713 2826942164515633359730285)
    ·
      refine ⟨1060103311693362509898857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2826942164515633359730285 1060103311693362509898857)
      ·
        refine ⟨795077483770021882424143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1060103311693362509898857 795077483770021882424143)
        ·
          refine ⟨1192616225655032823636215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795077483770021882424143 1192616225655032823636215)
          ·
            refine ⟨1788924338482549235454323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192616225655032823636215 1788924338482549235454323)
            ·
              refine ⟨2683386507723823853181485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1788924338482549235454323 2683386507723823853181485)
              ·
                refine ⟨1006269940396433944943057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2683386507723823853181485 1006269940396433944943057)
                ·
                  refine ⟨754702455297325458707293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1006269940396433944943057 754702455297325458707293)
                  ·
                    refine ⟨283013420736497047015235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 754702455297325458707293 283013420736497047015235)
                    ·
                      rfl

theorem cell22_826750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_826750 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826750 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826750 prefixEnd_826750 := by exact prefixLift 826750
  have htrace : WordTrace (prefixWord ++ tailWord_826750) baseStart_826750 baseEnd_826750 := by
    simpa [prefixWord, tailWord_826750, baseEnd_826750] using wordTrace_append hprefix tailTrace_826750
  have hstable : (prefixWord ++ tailWord_826750).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826750).length < 2 ^ (prefixWord ++ tailWord_826750).sum := by decide
  have hdescent : baseEnd_826750 < baseStart_826750 := by decide
  rcases family_descends (prefixWord ++ tailWord_826750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826832 : List Nat := [2, 1, 1, 1, 1, 2, 2, 5, 1, 6]
def baseStart_826832 : Nat := 118140960795 + 826832 * 2 ^ 59
def prefixEnd_826832 : Nat := 4983230072969 + 3 ^ 40 * 826832 * 2
def baseEnd_826832 : Nat := 283041491012276166464983

theorem tailTrace_826832 : CollatzResearch.WordTrace tailWord_826832 prefixEnd_826832 283041491012276166464983 := by
  unfold tailWord_826832
  simp only [CollatzResearch.WordTrace]
  refine ⟨15078520270268175254137375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20104693693690900338849833 15078520270268175254137375)
  ·
    refine ⟨22617780405402262881206063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15078520270268175254137375 22617780405402262881206063)
    ·
      refine ⟨33926670608103394321809095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22617780405402262881206063 33926670608103394321809095)
      ·
        refine ⟨50890005912155091482713643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33926670608103394321809095 50890005912155091482713643)
        ·
          refine ⟨76335008868232637224070465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50890005912155091482713643 76335008868232637224070465)
          ·
            refine ⟨57251256651174477918052849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76335008868232637224070465 57251256651174477918052849)
            ·
              refine ⟨42938442488380858438539637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57251256651174477918052849 42938442488380858438539637)
              ·
                refine ⟨4025478983285705478613091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 42938442488380858438539637 4025478983285705478613091)
                ·
                  refine ⟨6038218474928558217919637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4025478983285705478613091 6038218474928558217919637)
                  ·
                    refine ⟨283041491012276166464983, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6038218474928558217919637 283041491012276166464983)
                    ·
                      rfl

theorem cell22_826832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 2, 5, 1, 6].length) (baseStart_826832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826832 prefixEnd_826832 := by exact prefixLift 826832
  have htrace : WordTrace (prefixWord ++ tailWord_826832) baseStart_826832 baseEnd_826832 := by
    simpa [prefixWord, tailWord_826832, baseEnd_826832] using wordTrace_append hprefix tailTrace_826832
  have hstable : (prefixWord ++ tailWord_826832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826832).length < 2 ^ (prefixWord ++ tailWord_826832).sum := by decide
  have hdescent : baseEnd_826832 < baseStart_826832 := by decide
  rcases family_descends (prefixWord ++ tailWord_826832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826838 : List Nat := [5, 2, 1, 1, 1, 3, 1, 3, 1, 4]
def baseStart_826838 : Nat := 118140960795 + 826838 * 2 ^ 59
def prefixEnd_826838 : Nat := 4983230072969 + 3 ^ 40 * 826838 * 2
def baseEnd_826838 : Nat := 283043544934894150814965

theorem tailTrace_826838 : CollatzResearch.WordTrace tailWord_826838 prefixEnd_826838 283043544934894150814965 := by
  unfold tailWord_826838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1884828711157163345812073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20104839585676409021995445 1884828711157163345812073)
  ·
    refine ⟨1413621533367872509359055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1884828711157163345812073 1413621533367872509359055)
    ·
      refine ⟨2120432300051808764038583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1413621533367872509359055 2120432300051808764038583)
      ·
        refine ⟨3180648450077713146057875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2120432300051808764038583 3180648450077713146057875)
        ·
          refine ⟨4770972675116569719086813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3180648450077713146057875 4770972675116569719086813)
          ·
            refine ⟨1789114753168713644657555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4770972675116569719086813 1789114753168713644657555)
            ·
              refine ⟨2683672129753070466986333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1789114753168713644657555 2683672129753070466986333)
              ·
                refine ⟨1006377048657401425119875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2683672129753070466986333 1006377048657401425119875)
                ·
                  refine ⟨1509565572986102137679813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1006377048657401425119875 1509565572986102137679813)
                  ·
                    refine ⟨283043544934894150814965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1509565572986102137679813 283043544934894150814965)
                    ·
                      rfl

theorem cell22_826838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_826838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826838 prefixEnd_826838 := by exact prefixLift 826838
  have htrace : WordTrace (prefixWord ++ tailWord_826838) baseStart_826838 baseEnd_826838 := by
    simpa [prefixWord, tailWord_826838, baseEnd_826838] using wordTrace_append hprefix tailTrace_826838
  have hstable : (prefixWord ++ tailWord_826838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826838).length < 2 ^ (prefixWord ++ tailWord_826838).sum := by decide
  have hdescent : baseEnd_826838 < baseStart_826838 := by decide
  rcases family_descends (prefixWord ++ tailWord_826838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826847 : List Nat := [1, 1, 2, 3, 3, 1, 11]
def baseStart_826847 : Nat := 118140960795 + 826847 * 2 ^ 59
def prefixEnd_826847 : Nat := 4983230072969 + 3 ^ 40 * 826847 * 2
def baseEnd_826847 : Nat := 10483208363660041753331

theorem tailTrace_826847 : CollatzResearch.WordTrace tailWord_826847 prefixEnd_826847 10483208363660041753331 := by
  unfold tailWord_826847
  simp only [CollatzResearch.WordTrace]
  refine ⟨30157587635482008070070795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20105058423654672046713863 30157587635482008070070795)
  ·
    refine ⟨45236381453223012105106193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30157587635482008070070795 45236381453223012105106193)
    ·
      refine ⟨33927286089917259078829645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45236381453223012105106193 33927286089917259078829645)
      ·
        refine ⟨12722732283718972154561117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33927286089917259078829645 12722732283718972154561117)
        ·
          refine ⟨4771024606394614557960419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12722732283718972154561117 4771024606394614557960419)
          ·
            refine ⟨7156536909591921836940629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4771024606394614557960419 7156536909591921836940629)
            ·
              refine ⟨10483208363660041753331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7156536909591921836940629 10483208363660041753331)
              ·
                rfl

theorem cell22_826847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 11].length) (baseStart_826847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826847 prefixEnd_826847 := by exact prefixLift 826847
  have htrace : WordTrace (prefixWord ++ tailWord_826847) baseStart_826847 baseEnd_826847 := by
    simpa [prefixWord, tailWord_826847, baseEnd_826847] using wordTrace_append hprefix tailTrace_826847
  have hstable : (prefixWord ++ tailWord_826847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826847).length < 2 ^ (prefixWord ++ tailWord_826847).sum := by decide
  have hdescent : baseEnd_826847 < baseStart_826847 := by decide
  rcases family_descends (prefixWord ++ tailWord_826847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826851 : List Nat := [1, 1, 1, 6, 2, 2, 1, 1, 4, 3]
def baseStart_826851 : Nat := 118140960795 + 826851 * 2 ^ 59
def prefixEnd_826851 : Nat := 4983230072969 + 3 ^ 40 * 826851 * 2
def baseEnd_826851 : Nat := 283047995100566450239925

theorem tailTrace_826851 : CollatzResearch.WordTrace tailWord_826851 prefixEnd_826851 283047995100566450239925 := by
  unfold tailWord_826851
  simp only [CollatzResearch.WordTrace]
  refine ⟨30157733527467516753216407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20105155684978344502144271 30157733527467516753216407)
  ·
    refine ⟨45236600291201275129824611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30157733527467516753216407 45236600291201275129824611)
    ·
      refine ⟨67854900436801912694736917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45236600291201275129824611 67854900436801912694736917)
      ·
        refine ⟨3180698457975089657565793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 67854900436801912694736917 3180698457975089657565793)
        ·
          refine ⟨2385523843481317243174345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3180698457975089657565793 2385523843481317243174345)
          ·
            refine ⟨1789142882610987932380759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2385523843481317243174345 1789142882610987932380759)
            ·
              refine ⟨2683714323916481898571139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1789142882610987932380759 2683714323916481898571139)
              ·
                refine ⟨4025571485874722847856709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2683714323916481898571139 4025571485874722847856709)
                ·
                  refine ⟨754794653601510533973133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4025571485874722847856709 754794653601510533973133)
                  ·
                    refine ⟨283047995100566450239925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 754794653601510533973133 283047995100566450239925)
                    ·
                      rfl

theorem cell22_826851_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 2, 1, 1, 4, 3].length) (baseStart_826851 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826851 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826851 prefixEnd_826851 := by exact prefixLift 826851
  have htrace : WordTrace (prefixWord ++ tailWord_826851) baseStart_826851 baseEnd_826851 := by
    simpa [prefixWord, tailWord_826851, baseEnd_826851] using wordTrace_append hprefix tailTrace_826851
  have hstable : (prefixWord ++ tailWord_826851).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826851).length < 2 ^ (prefixWord ++ tailWord_826851).sum := by decide
  have hdescent : baseEnd_826851 < baseStart_826851 := by decide
  rcases family_descends (prefixWord ++ tailWord_826851) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826879 : List Nat := [1, 1, 2, 2, 1, 2, 2, 3, 5, 3]
def baseStart_826879 : Nat := 118140960795 + 826879 * 2 ^ 59
def prefixEnd_826879 : Nat := 4983230072969 + 3 ^ 40 * 826879 * 2
def baseEnd_826879 : Nat := 283057580072783710539839

theorem tailTrace_826879 : CollatzResearch.WordTrace tailWord_826879 prefixEnd_826879 283057580072783710539839 := by
  unfold tailWord_826879
  simp only [CollatzResearch.WordTrace]
  refine ⟨30158754771366077535235691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20105836514244051690157127 30158754771366077535235691)
  ·
    refine ⟨45238132157049116302853537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30158754771366077535235691 45238132157049116302853537)
    ·
      refine ⟨33928599117786837227140153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45238132157049116302853537 33928599117786837227140153)
      ·
        refine ⟨25446449338340127920355115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33928599117786837227140153 25446449338340127920355115)
        ·
          refine ⟨38169674007510191880532673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25446449338340127920355115 38169674007510191880532673)
          ·
            refine ⟨28627255505632643910399505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38169674007510191880532673 28627255505632643910399505)
            ·
              refine ⟨21470441629224482932799629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28627255505632643910399505 21470441629224482932799629)
              ·
                refine ⟨8051415610959181099799861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21470441629224482932799629 8051415610959181099799861)
                ·
                  refine ⟨754820213527423228106237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8051415610959181099799861 754820213527423228106237)
                  ·
                    refine ⟨283057580072783710539839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 754820213527423228106237 283057580072783710539839)
                    ·
                      rfl

theorem cell22_826879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 2, 3, 5, 3].length) (baseStart_826879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826879 prefixEnd_826879 := by exact prefixLift 826879
  have htrace : WordTrace (prefixWord ++ tailWord_826879) baseStart_826879 baseEnd_826879 := by
    simpa [prefixWord, tailWord_826879, baseEnd_826879] using wordTrace_append hprefix tailTrace_826879
  have hstable : (prefixWord ++ tailWord_826879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826879).length < 2 ^ (prefixWord ++ tailWord_826879).sum := by decide
  have hdescent : baseEnd_826879 < baseStart_826879 := by decide
  rcases family_descends (prefixWord ++ tailWord_826879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826909 : List Nat := [1, 4, 2, 2, 1, 1, 1, 3, 7]
def baseStart_826909 : Nat := 118140960795 + 826909 * 2 ^ 59
def prefixEnd_826909 : Nat := 4983230072969 + 3 ^ 40 * 826909 * 2
def baseEnd_826909 : Nat := 94355949895291210763249

theorem tailTrace_826909 : CollatzResearch.WordTrace tailWord_826909 prefixEnd_826909 94355949895291210763249 := by
  unfold tailWord_826909
  simp only [CollatzResearch.WordTrace]
  refine ⟨30159848961257392658827781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20106565974171595105885187 30159848961257392658827781)
  ·
    refine ⟨5654971680235761123530209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30159848961257392658827781 5654971680235761123530209)
    ·
      refine ⟨4241228760176820842647657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5654971680235761123530209 4241228760176820842647657)
      ·
        refine ⟨3180921570132615631985743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4241228760176820842647657 3180921570132615631985743)
        ·
          refine ⟨4771382355198923447978615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3180921570132615631985743 4771382355198923447978615)
          ·
            refine ⟨7157073532798385171967923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4771382355198923447978615 7157073532798385171967923)
            ·
              refine ⟨10735610299197577757951885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7157073532798385171967923 10735610299197577757951885)
              ·
                refine ⟨4025853862199091659231957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10735610299197577757951885 4025853862199091659231957)
                ·
                  refine ⟨94355949895291210763249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4025853862199091659231957 94355949895291210763249)
                  ·
                    rfl

theorem cell22_826909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 3, 7].length) (baseStart_826909 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826909 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826909 prefixEnd_826909 := by exact prefixLift 826909
  have htrace : WordTrace (prefixWord ++ tailWord_826909) baseStart_826909 baseEnd_826909 := by
    simpa [prefixWord, tailWord_826909, baseEnd_826909] using wordTrace_append hprefix tailTrace_826909
  have hstable : (prefixWord ++ tailWord_826909).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826909).length < 2 ^ (prefixWord ++ tailWord_826909).sum := by decide
  have hdescent : baseEnd_826909 < baseStart_826909 := by decide
  rcases family_descends (prefixWord ++ tailWord_826909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826913 : List Nat := [1, 2, 3, 2, 2, 4, 1, 1, 3, 3]
def baseStart_826913 : Nat := 118140960795 + 826913 * 2 ^ 59
def prefixEnd_826913 : Nat := 4983230072969 + 3 ^ 40 * 826913 * 2
def baseEnd_826913 : Nat := 283069218967618955189735

theorem tailTrace_826913 : CollatzResearch.WordTrace tailWord_826913 prefixEnd_826913 283069218967618955189735 := by
  unfold tailWord_826913
  simp only [CollatzResearch.WordTrace]
  refine ⟨30159994853242901341973393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20106663235495267561315595 30159994853242901341973393)
  ·
    refine ⟨22619996139932176006480045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30159994853242901341973393 22619996139932176006480045)
    ·
      refine ⟨8482498552474566002430017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22619996139932176006480045 8482498552474566002430017)
      ·
        refine ⟨6361873914355924501822513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8482498552474566002430017 6361873914355924501822513)
        ·
          refine ⟨4771405435766943376366885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6361873914355924501822513 4771405435766943376366885)
          ·
            refine ⟨894638519206301883068791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4771405435766943376366885 894638519206301883068791)
            ·
              refine ⟨1341957778809452824603187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894638519206301883068791 1341957778809452824603187)
              ·
                refine ⟨2012936668214179236904781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1341957778809452824603187 2012936668214179236904781)
                ·
                  refine ⟨754851250580317213839293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2012936668214179236904781 754851250580317213839293)
                  ·
                    refine ⟨283069218967618955189735, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 754851250580317213839293 283069218967618955189735)
                    ·
                      rfl

theorem cell22_826913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 4, 1, 1, 3, 3].length) (baseStart_826913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826913 prefixEnd_826913 := by exact prefixLift 826913
  have htrace : WordTrace (prefixWord ++ tailWord_826913) baseStart_826913 baseEnd_826913 := by
    simpa [prefixWord, tailWord_826913, baseEnd_826913] using wordTrace_append hprefix tailTrace_826913
  have hstable : (prefixWord ++ tailWord_826913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826913).length < 2 ^ (prefixWord ++ tailWord_826913).sum := by decide
  have hdescent : baseEnd_826913 < baseStart_826913 := by decide
  rcases family_descends (prefixWord ++ tailWord_826913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_826986 : List Nat := [3, 1, 3, 2, 1, 2, 1, 3, 1, 5]
def baseStart_826986 : Nat := 118140960795 + 826986 * 2 ^ 59
def prefixEnd_826986 : Nat := 4983230072969 + 3 ^ 40 * 826986 * 2
def baseEnd_826986 : Nat := 283094208359471098114511

theorem tailTrace_826986 : CollatzResearch.WordTrace tailWord_826986 prefixEnd_826986 283094208359471098114511 := by
  unfold tailWord_826986
  simp only [CollatzResearch.WordTrace]
  refine ⟨7540664345494608702345203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20108438254652289872920541 7540664345494608702345203)
  ·
    refine ⟨11310996518241913053517805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7540664345494608702345203 11310996518241913053517805)
    ·
      refine ⟨4241623694340717395069177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11310996518241913053517805 4241623694340717395069177)
      ·
        refine ⟨3181217770755538046301883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4241623694340717395069177 3181217770755538046301883)
        ·
          refine ⟨4771826656133307069452825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3181217770755538046301883 4771826656133307069452825)
          ·
            refine ⟨3578869992099980302089619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4771826656133307069452825 3578869992099980302089619)
            ·
              refine ⟨5368304988149970453134429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3578869992099980302089619 5368304988149970453134429)
              ·
                refine ⟨2013114370556238919925411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5368304988149970453134429 2013114370556238919925411)
                ·
                  refine ⟨3019671555834358379888117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2013114370556238919925411 3019671555834358379888117)
                  ·
                    refine ⟨283094208359471098114511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3019671555834358379888117 283094208359471098114511)
                    ·
                      rfl

theorem cell22_826986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 2, 1, 3, 1, 5].length) (baseStart_826986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_826986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_826986 prefixEnd_826986 := by exact prefixLift 826986
  have htrace : WordTrace (prefixWord ++ tailWord_826986) baseStart_826986 baseEnd_826986 := by
    simpa [prefixWord, tailWord_826986, baseEnd_826986] using wordTrace_append hprefix tailTrace_826986
  have hstable : (prefixWord ++ tailWord_826986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_826986).length < 2 ^ (prefixWord ++ tailWord_826986).sum := by decide
  have hdescent : baseEnd_826986 < baseStart_826986 := by decide
  rcases family_descends (prefixWord ++ tailWord_826986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827029 : List Nat := [1, 3, 2, 1, 1, 1, 1, 3, 1, 8]
def baseStart_827029 : Nat := 118140960795 + 827029 * 2 ^ 59
def prefixEnd_827029 : Nat := 4983230072969 + 3 ^ 40 * 827029 * 2
def baseEnd_827029 : Nat := 283108928138233319289379

theorem tailTrace_827029 : CollatzResearch.WordTrace tailWord_827029 prefixEnd_827029 283108928138233319289379 := by
  unfold tailWord_827029
  simp only [CollatzResearch.WordTrace]
  refine ⟨30164225720822653153196141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20109483813881768768797427 30164225720822653153196141)
  ·
    refine ⟨11311584645308494932448553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30164225720822653153196141 11311584645308494932448553)
    ·
      refine ⟨8483688483981371199336415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11311584645308494932448553 8483688483981371199336415)
      ·
        refine ⟨12725532725972056799004623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8483688483981371199336415 12725532725972056799004623)
        ·
          refine ⟨19088299088958085198506935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12725532725972056799004623 19088299088958085198506935)
          ·
            refine ⟨28632448633437127797760403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19088299088958085198506935 28632448633437127797760403)
            ·
              refine ⟨42948672950155691696640605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28632448633437127797760403 42948672950155691696640605)
              ·
                refine ⟨16105752356308384386240227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 42948672950155691696640605 16105752356308384386240227)
                ·
                  refine ⟨24158628534462576579360341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16105752356308384386240227 24158628534462576579360341)
                  ·
                    refine ⟨283108928138233319289379, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24158628534462576579360341 283108928138233319289379)
                    ·
                      rfl

theorem cell22_827029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_827029 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827029 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827029 prefixEnd_827029 := by exact prefixLift 827029
  have htrace : WordTrace (prefixWord ++ tailWord_827029) baseStart_827029 baseEnd_827029 := by
    simpa [prefixWord, tailWord_827029, baseEnd_827029] using wordTrace_append hprefix tailTrace_827029
  have hstable : (prefixWord ++ tailWord_827029).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827029).length < 2 ^ (prefixWord ++ tailWord_827029).sum := by decide
  have hdescent : baseEnd_827029 < baseStart_827029 := by decide
  rcases family_descends (prefixWord ++ tailWord_827029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827065 : List Nat := [1, 2, 1, 4, 1, 1, 5, 3, 1, 3]
def baseStart_827065 : Nat := 118140960795 + 827065 * 2 ^ 59
def prefixEnd_827065 : Nat := 4983230072969 + 3 ^ 40 * 827065 * 2
def baseEnd_827065 : Nat := 283121251673941225389269

theorem tailTrace_827065 : CollatzResearch.WordTrace tailWord_827065 prefixEnd_827065 283121251673941225389269 := by
  unfold tailWord_827065
  simp only [CollatzResearch.WordTrace]
  refine ⟨30165538748692231301506649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20110359165794820867671099 30165538748692231301506649)
  ·
    refine ⟨22624154061519173476129987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30165538748692231301506649 22624154061519173476129987)
    ·
      refine ⟨33936231092278760214194981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22624154061519173476129987 33936231092278760214194981)
      ·
        refine ⟨6363043329802267540161559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33936231092278760214194981 6363043329802267540161559)
        ·
          refine ⟨9544564994703401310242339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6363043329802267540161559 9544564994703401310242339)
          ·
            refine ⟨14316847492055101965363509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9544564994703401310242339 14316847492055101965363509)
            ·
              refine ⟨1342204452380165809252829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14316847492055101965363509 1342204452380165809252829)
              ·
                refine ⟨503326669642562178469811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1342204452380165809252829 503326669642562178469811)
                ·
                  refine ⟨754990004463843267704717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 503326669642562178469811 754990004463843267704717)
                  ·
                    refine ⟨283121251673941225389269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 754990004463843267704717 283121251673941225389269)
                    ·
                      rfl

theorem cell22_827065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 5, 3, 1, 3].length) (baseStart_827065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827065 prefixEnd_827065 := by exact prefixLift 827065
  have htrace : WordTrace (prefixWord ++ tailWord_827065) baseStart_827065 baseEnd_827065 := by
    simpa [prefixWord, tailWord_827065, baseEnd_827065] using wordTrace_append hprefix tailTrace_827065
  have hstable : (prefixWord ++ tailWord_827065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827065).length < 2 ^ (prefixWord ++ tailWord_827065).sum := by decide
  have hdescent : baseEnd_827065 < baseStart_827065 := by decide
  rcases family_descends (prefixWord ++ tailWord_827065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827082 : List Nat := [3, 1, 2, 1, 6, 1, 1, 1, 3, 3]
def baseStart_827082 : Nat := 118140960795 + 827082 * 2 ^ 59
def prefixEnd_827082 : Nat := 4983230072969 + 3 ^ 40 * 827082 * 2
def baseEnd_827082 : Nat := 283127071121358847714217

theorem tailTrace_827082 : CollatzResearch.WordTrace tailWord_827082 prefixEnd_827082 283127071121358847714217 := by
  unfold tailWord_827082
  simp only [CollatzResearch.WordTrace]
  refine ⟨7541539697407660801218875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20110772526420428803250333 7541539697407660801218875)
  ·
    refine ⟨11312309546111491201828313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7541539697407660801218875 11312309546111491201828313)
    ·
      refine ⟨8484232159583618401371235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11312309546111491201828313 8484232159583618401371235)
      ·
        refine ⟨12726348239375427602056853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8484232159583618401371235 12726348239375427602056853)
        ·
          refine ⟨596547573720723168846415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 12726348239375427602056853 596547573720723168846415)
          ·
            refine ⟨894821360581084753269623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596547573720723168846415 894821360581084753269623)
            ·
              refine ⟨1342232040871627129904435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894821360581084753269623 1342232040871627129904435)
              ·
                refine ⟨2013348061307440694856653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1342232040871627129904435 2013348061307440694856653)
                ·
                  refine ⟨755005522990290260571245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2013348061307440694856653 755005522990290260571245)
                  ·
                    refine ⟨283127071121358847714217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 755005522990290260571245 283127071121358847714217)
                    ·
                      rfl

theorem cell22_827082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 6, 1, 1, 1, 3, 3].length) (baseStart_827082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827082 prefixEnd_827082 := by exact prefixLift 827082
  have htrace : WordTrace (prefixWord ++ tailWord_827082) baseStart_827082 baseEnd_827082 := by
    simpa [prefixWord, tailWord_827082, baseEnd_827082] using wordTrace_append hprefix tailTrace_827082
  have hstable : (prefixWord ++ tailWord_827082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827082).length < 2 ^ (prefixWord ++ tailWord_827082).sum := by decide
  have hdescent : baseEnd_827082 < baseStart_827082 := by decide
  rcases family_descends (prefixWord ++ tailWord_827082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827121 : List Nat := [1, 2, 2, 2, 2, 3, 1, 1, 3, 5]
def baseStart_827121 : Nat := 118140960795 + 827121 * 2 ^ 59
def prefixEnd_827121 : Nat := 4983230072969 + 3 ^ 40 * 827121 * 2
def baseEnd_827121 : Nat := 283140421618375745989097

theorem tailTrace_827121 : CollatzResearch.WordTrace tailWord_827121 prefixEnd_827121 283140421618375745989097 := by
  unfold tailWord_827121
  simp only [CollatzResearch.WordTrace]
  refine ⟨30167581236489352865545217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20111720824326235243696811 30167581236489352865545217)
  ·
    refine ⟨22625685927367014649158913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30167581236489352865545217 22625685927367014649158913)
    ·
      refine ⟨16969264445525260986869185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22625685927367014649158913 16969264445525260986869185)
      ·
        refine ⟨12726948334143945740151889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16969264445525260986869185 12726948334143945740151889)
        ·
          refine ⟨9545211250607959305113917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12726948334143945740151889 9545211250607959305113917)
          ·
            refine ⟨3579454218977984739417719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9545211250607959305113917 3579454218977984739417719)
            ·
              refine ⟨5369181328466977109126579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3579454218977984739417719 5369181328466977109126579)
              ·
                refine ⟨8053771992700465663689869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5369181328466977109126579 8053771992700465663689869)
                ·
                  refine ⟨3020164497262674623883701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8053771992700465663689869 3020164497262674623883701)
                  ·
                    refine ⟨283140421618375745989097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3020164497262674623883701 283140421618375745989097)
                    ·
                      rfl

theorem cell22_827121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 5].length) (baseStart_827121 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827121 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827121 prefixEnd_827121 := by exact prefixLift 827121
  have htrace : WordTrace (prefixWord ++ tailWord_827121) baseStart_827121 baseEnd_827121 := by
    simpa [prefixWord, tailWord_827121, baseEnd_827121] using wordTrace_append hprefix tailTrace_827121
  have hstable : (prefixWord ++ tailWord_827121).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827121).length < 2 ^ (prefixWord ++ tailWord_827121).sum := by decide
  have hdescent : baseEnd_827121 < baseStart_827121 := by decide
  rcases family_descends (prefixWord ++ tailWord_827121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827138 : List Nat := [3, 4, 1, 1, 1, 1, 1, 2, 3, 5]
def baseStart_827138 : Nat := 118140960795 + 827138 * 2 ^ 59
def prefixEnd_827138 : Nat := 4983230072969 + 3 ^ 40 * 827138 * 2
def baseEnd_827138 : Nat := 283146241065793368314045

theorem tailTrace_827138 : CollatzResearch.WordTrace tailWord_827138 prefixEnd_827138 283146241065793368314045 := by
  unfold tailWord_827138
  simp only [CollatzResearch.WordTrace]
  refine ⟨7542050319356941192228517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20112134184951843179276045 7542050319356941192228517)
  ·
    refine ⟨1414134434879426473542847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7542050319356941192228517 1414134434879426473542847)
    ·
      refine ⟨2121201652319139710314271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1414134434879426473542847 2121201652319139710314271)
      ·
        refine ⟨3181802478478709565471407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2121201652319139710314271 3181802478478709565471407)
        ·
          refine ⟨4772703717718064348207111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3181802478478709565471407 4772703717718064348207111)
          ·
            refine ⟨7159055576577096522310667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4772703717718064348207111 7159055576577096522310667)
            ·
              refine ⟨10738583364865644783466001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7159055576577096522310667 10738583364865644783466001)
              ·
                refine ⟨8053937523649233587599501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10738583364865644783466001 8053937523649233587599501)
                ·
                  refine ⟨3020226571368462595349813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8053937523649233587599501 3020226571368462595349813)
                  ·
                    refine ⟨283146241065793368314045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3020226571368462595349813 283146241065793368314045)
                    ·
                      rfl

theorem cell22_827138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_827138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827138 prefixEnd_827138 := by exact prefixLift 827138
  have htrace : WordTrace (prefixWord ++ tailWord_827138) baseStart_827138 baseEnd_827138 := by
    simpa [prefixWord, tailWord_827138, baseEnd_827138] using wordTrace_append hprefix tailTrace_827138
  have hstable : (prefixWord ++ tailWord_827138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827138).length < 2 ^ (prefixWord ++ tailWord_827138).sum := by decide
  have hdescent : baseEnd_827138 < baseStart_827138 := by decide
  rcases family_descends (prefixWord ++ tailWord_827138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827140 : List Nat := [2, 3, 2, 2, 1, 3, 1, 4, 4]
def baseStart_827140 : Nat := 118140960795 + 827140 * 2 ^ 59
def prefixEnd_827140 : Nat := 4983230072969 + 3 ^ 40 * 827140 * 2
def baseEnd_827140 : Nat := 94382308568888676588013

theorem tailTrace_827140 : CollatzResearch.WordTrace tailWord_827140 prefixEnd_827140 94382308568888676588013 := by
  unfold tailWord_827140
  simp only [CollatzResearch.WordTrace]
  refine ⟨15084137111710259555243437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20112182815613679406991249 15084137111710259555243437)
  ·
    refine ⟨5656551416891347333216289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15084137111710259555243437 5656551416891347333216289)
    ·
      refine ⟨4242413562668510499912217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5656551416891347333216289 4242413562668510499912217)
      ·
        refine ⟨3181810172001382874934163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4242413562668510499912217 3181810172001382874934163)
        ·
          refine ⟨4772715258002074312401245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3181810172001382874934163 4772715258002074312401245)
          ·
            refine ⟨1789768221750777867150467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4772715258002074312401245 1789768221750777867150467)
            ·
              refine ⟨2684652332626166800725701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1789768221750777867150467 2684652332626166800725701)
              ·
                refine ⟨503372312367406275136069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2684652332626166800725701 503372312367406275136069)
                ·
                  refine ⟨94382308568888676588013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 503372312367406275136069 94382308568888676588013)
                  ·
                    rfl

theorem cell22_827140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 3, 1, 4, 4].length) (baseStart_827140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827140 prefixEnd_827140 := by exact prefixLift 827140
  have htrace : WordTrace (prefixWord ++ tailWord_827140) baseStart_827140 baseEnd_827140 := by
    simpa [prefixWord, tailWord_827140, baseEnd_827140] using wordTrace_append hprefix tailTrace_827140
  have hstable : (prefixWord ++ tailWord_827140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827140).length < 2 ^ (prefixWord ++ tailWord_827140).sum := by decide
  have hdescent : baseEnd_827140 < baseStart_827140 := by decide
  rcases family_descends (prefixWord ++ tailWord_827140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827168 : List Nat := [2, 1, 1, 5, 1, 1, 5, 6]
def baseStart_827168 : Nat := 118140960795 + 827168 * 2 ^ 59
def prefixEnd_827168 : Nat := 4983230072969 + 3 ^ 40 * 827168 * 2
def baseEnd_827168 : Nat := 31461834519875921118217

theorem tailTrace_827168 : CollatzResearch.WordTrace tailWord_827168 prefixEnd_827168 31461834519875921118217 := by
  unfold tailWord_827168
  simp only [CollatzResearch.WordTrace]
  refine ⟨15084647733659539946253079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20112863644879386595004105 15084647733659539946253079)
  ·
    refine ⟨22626971600489309919379619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15084647733659539946253079 22626971600489309919379619)
    ·
      refine ⟨33940457400733964879069429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22626971600489309919379619 33940457400733964879069429)
      ·
        refine ⟨3181917881318809207412759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 33940457400733964879069429 3181917881318809207412759)
        ·
          refine ⟨4772876821978213811119139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3181917881318809207412759 4772876821978213811119139)
          ·
            refine ⟨7159315232967320716678709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4772876821978213811119139 7159315232967320716678709)
            ·
              refine ⟨671185803090686317188629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7159315232967320716678709 671185803090686317188629)
              ·
                refine ⟨31461834519875921118217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 671185803090686317188629 31461834519875921118217)
                ·
                  rfl

theorem cell22_827168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 5, 6].length) (baseStart_827168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827168 prefixEnd_827168 := by exact prefixLift 827168
  have htrace : WordTrace (prefixWord ++ tailWord_827168) baseStart_827168 baseEnd_827168 := by
    simpa [prefixWord, tailWord_827168, baseEnd_827168] using wordTrace_append hprefix tailTrace_827168
  have hstable : (prefixWord ++ tailWord_827168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827168).length < 2 ^ (prefixWord ++ tailWord_827168).sum := by decide
  have hdescent : baseEnd_827168 < baseStart_827168 := by decide
  rcases family_descends (prefixWord ++ tailWord_827168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827189 : List Nat := [1, 3, 3, 1, 5, 1, 1, 2, 2, 3]
def baseStart_827189 : Nat := 118140960795 + 827189 * 2 ^ 59
def prefixEnd_827189 : Nat := 4983230072969 + 3 ^ 40 * 827189 * 2
def baseEnd_827189 : Nat := 283163699408046235288889

theorem tailTrace_827189 : CollatzResearch.WordTrace tailWord_827189 prefixEnd_827189 283163699408046235288889 := by
  unfold tailWord_827189
  simp only [CollatzResearch.WordTrace]
  refine ⟨30170061400243000479020621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20113374266828666986013747 30170061400243000479020621)
  ·
    refine ⟨11313773025091125179632733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30170061400243000479020621 11313773025091125179632733)
    ·
      refine ⟨4242664884409171942362275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11313773025091125179632733 4242664884409171942362275)
      ·
        refine ⟨6363997326613757913543413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4242664884409171942362275 6363997326613757913543413)
        ·
          refine ⟨596624749370039804394695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6363997326613757913543413 596624749370039804394695)
          ·
            refine ⟨894937124055059706592043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596624749370039804394695 894937124055059706592043)
            ·
              refine ⟨1342405686082589559888065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894937124055059706592043 1342405686082589559888065)
              ·
                refine ⟨1006804264561942169916049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1342405686082589559888065 1006804264561942169916049)
                ·
                  refine ⟨755103198421456627437037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1006804264561942169916049 755103198421456627437037)
                  ·
                    refine ⟨283163699408046235288889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 755103198421456627437037 283163699408046235288889)
                    ·
                      rfl

theorem cell22_827189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_827189 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827189 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827189 prefixEnd_827189 := by exact prefixLift 827189
  have htrace : WordTrace (prefixWord ++ tailWord_827189) baseStart_827189 baseEnd_827189 := by
    simpa [prefixWord, tailWord_827189, baseEnd_827189] using wordTrace_append hprefix tailTrace_827189
  have hstable : (prefixWord ++ tailWord_827189).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827189).length < 2 ^ (prefixWord ++ tailWord_827189).sum := by decide
  have hdescent : baseEnd_827189 < baseStart_827189 := by decide
  rcases family_descends (prefixWord ++ tailWord_827189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827206 : List Nat := [6, 1, 1, 2, 1, 2, 3, 1, 2, 3]
def baseStart_827206 : Nat := 118140960795 + 827206 * 2 ^ 59
def prefixEnd_827206 : Nat := 4983230072969 + 3 ^ 40 * 827206 * 2
def baseEnd_827206 : Nat := 283169518855463857613837

theorem tailTrace_827206 : CollatzResearch.WordTrace tailWord_827206 prefixEnd_827206 283169518855463857613837 := by
  unfold tailWord_827206
  simp only [CollatzResearch.WordTrace]
  refine ⟨942833795036919136949671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20113787627454274921592981 942833795036919136949671)
  ·
    refine ⟨1414250692555378705424507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 942833795036919136949671 1414250692555378705424507)
    ·
      refine ⟨2121376038833068058136761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1414250692555378705424507 2121376038833068058136761)
      ·
        refine ⟨1591032029124801043602571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2121376038833068058136761 1591032029124801043602571)
        ·
          refine ⟨2386548043687201565403857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1591032029124801043602571 2386548043687201565403857)
          ·
            refine ⟨1789911032765401174052893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2386548043687201565403857 1789911032765401174052893)
            ·
              refine ⟨671216637287025440269835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1789911032765401174052893 671216637287025440269835)
              ·
                refine ⟨1006824955930538160404753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671216637287025440269835 1006824955930538160404753)
                ·
                  refine ⟨755118716947903620303565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1006824955930538160404753 755118716947903620303565)
                  ·
                    refine ⟨283169518855463857613837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 755118716947903620303565 283169518855463857613837)
                    ·
                      rfl

theorem cell22_827206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 3, 1, 2, 3].length) (baseStart_827206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827206 prefixEnd_827206 := by exact prefixLift 827206
  have htrace : WordTrace (prefixWord ++ tailWord_827206) baseStart_827206 baseEnd_827206 := by
    simpa [prefixWord, tailWord_827206, baseEnd_827206] using wordTrace_append hprefix tailTrace_827206
  have hstable : (prefixWord ++ tailWord_827206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827206).length < 2 ^ (prefixWord ++ tailWord_827206).sum := by decide
  have hdescent : baseEnd_827206 < baseStart_827206 := by decide
  rcases family_descends (prefixWord ++ tailWord_827206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827234 : List Nat := [3, 3, 2, 1, 2, 1, 3, 3, 1, 3]
def baseStart_827234 : Nat := 118140960795 + 827234 * 2 ^ 59
def prefixEnd_827234 : Nat := 4983230072969 + 3 ^ 40 * 827234 * 2
def baseEnd_827234 : Nat := 283179103827681117913751

theorem tailTrace_827234 : CollatzResearch.WordTrace tailWord_827234 prefixEnd_827234 283179103827681117913751 := by
  unfold tailWord_827234
  simp only [CollatzResearch.WordTrace]
  refine ⟨7542925671269993291102189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20114468456719982109605837 7542925671269993291102189)
  ·
    refine ⟨2828597126726247484163321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7542925671269993291102189 2828597126726247484163321)
    ·
      refine ⟨2121447845044685613122491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2828597126726247484163321 2121447845044685613122491)
      ·
        refine ⟨3182171767567028419683737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2121447845044685613122491 3182171767567028419683737)
        ·
          refine ⟨2386628825675271314762803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3182171767567028419683737 2386628825675271314762803)
          ·
            refine ⟨3579943238512906972144205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2386628825675271314762803 3579943238512906972144205)
            ·
              refine ⟨1342478714442340114554077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3579943238512906972144205 1342478714442340114554077)
              ·
                refine ⟨503429517915877542957779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1342478714442340114554077 503429517915877542957779)
                ·
                  refine ⟨755144276873816314436669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 503429517915877542957779 755144276873816314436669)
                  ·
                    refine ⟨283179103827681117913751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 755144276873816314436669 283179103827681117913751)
                    ·
                      rfl

theorem cell22_827234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 3, 1, 3].length) (baseStart_827234 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827234 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827234 prefixEnd_827234 := by exact prefixLift 827234
  have htrace : WordTrace (prefixWord ++ tailWord_827234) baseStart_827234 baseEnd_827234 := by
    simpa [prefixWord, tailWord_827234, baseEnd_827234] using wordTrace_append hprefix tailTrace_827234
  have hstable : (prefixWord ++ tailWord_827234).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827234).length < 2 ^ (prefixWord ++ tailWord_827234).sum := by decide
  have hdescent : baseEnd_827234 < baseStart_827234 := by decide
  rcases family_descends (prefixWord ++ tailWord_827234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827241 : List Nat := [1, 2, 1, 1, 1, 3, 1, 4, 8]
def baseStart_827241 : Nat := 118140960795 + 827241 * 2 ^ 59
def prefixEnd_827241 : Nat := 4983230072969 + 3 ^ 40 * 827241 * 2
def baseEnd_827241 : Nat := 94393833356911810996243

theorem tailTrace_827241 : CollatzResearch.WordTrace tailWord_827241 prefixEnd_827241 94393833356911810996243 := by
  unfold tailWord_827241
  simp only [CollatzResearch.WordTrace]
  refine ⟨30171957996054613359913577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20114638664036408906609051 30171957996054613359913577)
  ·
    refine ⟨22628968497040960019935183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30171957996054613359913577 22628968497040960019935183)
    ·
      refine ⟨33943452745561440029902775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22628968497040960019935183 33943452745561440029902775)
      ·
        refine ⟨50915179118342160044854163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33943452745561440029902775 50915179118342160044854163)
        ·
          refine ⟨76372768677513240067281245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50915179118342160044854163 76372768677513240067281245)
          ·
            refine ⟨28639788254067465025230467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76372768677513240067281245 28639788254067465025230467)
            ·
              refine ⟨42959682381101197537845701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28639788254067465025230467 42959682381101197537845701)
              ·
                refine ⟨8054940446456474538346069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 42959682381101197537845701 8054940446456474538346069)
                ·
                  refine ⟨94393833356911810996243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8054940446456474538346069 94393833356911810996243)
                  ·
                    rfl

theorem cell22_827241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 1, 4, 8].length) (baseStart_827241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827241 prefixEnd_827241 := by exact prefixLift 827241
  have htrace : WordTrace (prefixWord ++ tailWord_827241) baseStart_827241 baseEnd_827241 := by
    simpa [prefixWord, tailWord_827241, baseEnd_827241] using wordTrace_append hprefix tailTrace_827241
  have hstable : (prefixWord ++ tailWord_827241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827241).length < 2 ^ (prefixWord ++ tailWord_827241).sum := by decide
  have hdescent : baseEnd_827241 < baseStart_827241 := by decide
  rcases family_descends (prefixWord ++ tailWord_827241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827258 : List Nat := [3, 1, 1, 1, 1, 1, 7, 1, 6]
def baseStart_827258 : Nat := 118140960795 + 827258 * 2 ^ 59
def prefixEnd_827258 : Nat := 4983230072969 + 3 ^ 40 * 827258 * 2
def baseEnd_827258 : Nat := 94395773172717685104559

theorem tailTrace_827258 : CollatzResearch.WordTrace tailWord_827258 prefixEnd_827258 94395773172717685104559 := by
  unfold tailWord_827258
  simp only [CollatzResearch.WordTrace]
  refine ⟨7543144509248256315820607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20115052024662016842188285 7543144509248256315820607)
  ·
    refine ⟨11314716763872384473730911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7543144509248256315820607 11314716763872384473730911)
    ·
      refine ⟨16972075145808576710596367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11314716763872384473730911 16972075145808576710596367)
      ·
        refine ⟨25458112718712865065894551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16972075145808576710596367 25458112718712865065894551)
        ·
          refine ⟨38187169078069297598841827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25458112718712865065894551 38187169078069297598841827)
          ·
            refine ⟨57280753617103946398262741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38187169078069297598841827 57280753617103946398262741)
            ·
              refine ⟨1342517662900873743709283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 57280753617103946398262741 1342517662900873743709283)
              ·
                refine ⟨2013776494351310615563925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1342517662900873743709283 2013776494351310615563925)
                ·
                  refine ⟨94395773172717685104559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2013776494351310615563925 94395773172717685104559)
                  ·
                    rfl

theorem cell22_827258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 1, 6].length) (baseStart_827258 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827258 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827258 prefixEnd_827258 := by exact prefixLift 827258
  have htrace : WordTrace (prefixWord ++ tailWord_827258) baseStart_827258 baseEnd_827258 := by
    simpa [prefixWord, tailWord_827258, baseEnd_827258] using wordTrace_append hprefix tailTrace_827258
  have hstable : (prefixWord ++ tailWord_827258).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827258).length < 2 ^ (prefixWord ++ tailWord_827258).sum := by decide
  have hdescent : baseEnd_827258 < baseStart_827258 := by decide
  rcases family_descends (prefixWord ++ tailWord_827258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827273 : List Nat := [1, 2, 1, 1, 5, 1, 2, 3, 1, 5]
def baseStart_827273 : Nat := 118140960795 + 827273 * 2 ^ 59
def prefixEnd_827273 : Nat := 4983230072969 + 3 ^ 40 * 827273 * 2
def baseEnd_827273 : Nat := 283192454324698016188631

theorem tailTrace_827273 : CollatzResearch.WordTrace tailWord_827273 prefixEnd_827273 283192454324698016188631 := by
  unfold tailWord_827273
  simp only [CollatzResearch.WordTrace]
  refine ⟨30173125131938682825078473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20115416754625788550052315 30173125131938682825078473)
  ·
    refine ⟨22629843848954012118808855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30173125131938682825078473 22629843848954012118808855)
    ·
      refine ⟨33944765773431018178213283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22629843848954012118808855 33944765773431018178213283)
      ·
        refine ⟨50917148660146527267319925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33944765773431018178213283 50917148660146527267319925)
        ·
          refine ⟨4773482686888736931311243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50917148660146527267319925 4773482686888736931311243)
          ·
            refine ⟨7160224030333105396966865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4773482686888736931311243 7160224030333105396966865)
            ·
              refine ⟨5370168022749829047725149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7160224030333105396966865 5370168022749829047725149)
              ·
                refine ⟨2013813008531185892896931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5370168022749829047725149 2013813008531185892896931)
                ·
                  refine ⟨3020719512796778839345397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2013813008531185892896931 3020719512796778839345397)
                  ·
                    refine ⟨283192454324698016188631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3020719512796778839345397 283192454324698016188631)
                    ·
                      rfl

theorem cell22_827273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 2, 3, 1, 5].length) (baseStart_827273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827273 prefixEnd_827273 := by exact prefixLift 827273
  have htrace : WordTrace (prefixWord ++ tailWord_827273) baseStart_827273 baseEnd_827273 := by
    simpa [prefixWord, tailWord_827273, baseEnd_827273] using wordTrace_append hprefix tailTrace_827273
  have hstable : (prefixWord ++ tailWord_827273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827273).length < 2 ^ (prefixWord ++ tailWord_827273).sum := by decide
  have hdescent : baseEnd_827273 < baseStart_827273 := by decide
  rcases family_descends (prefixWord ++ tailWord_827273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827290 : List Nat := [3, 1, 1, 4, 2, 2, 1, 2, 1, 5]
def baseStart_827290 : Nat := 118140960795 + 827290 * 2 ^ 59
def prefixEnd_827290 : Nat := 4983230072969 + 3 ^ 40 * 827290 * 2
def baseEnd_827290 : Nat := 283198273772115638513579

theorem tailTrace_827290 : CollatzResearch.WordTrace tailWord_827290 prefixEnd_827290 283198273772115638513579 := by
  unfold tailWord_827290
  simp only [CollatzResearch.WordTrace]
  refine ⟨7543436293219273682111831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20115830115251396485631549 7543436293219273682111831)
  ·
    refine ⟨11315154439828910523167747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7543436293219273682111831 11315154439828910523167747)
    ·
      refine ⟨16972731659743365784751621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11315154439828910523167747 16972731659743365784751621)
      ·
        refine ⟨3182387186201881084640929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16972731659743365784751621 3182387186201881084640929)
        ·
          refine ⟨2386790389651410813480697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3182387186201881084640929 2386790389651410813480697)
          ·
            refine ⟨1790092792238558110110523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2386790389651410813480697 1790092792238558110110523)
            ·
              refine ⟨2685139188357837165165785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1790092792238558110110523 2685139188357837165165785)
              ·
                refine ⟨2013854391268377873874339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2685139188357837165165785 2013854391268377873874339)
                ·
                  refine ⟨3020781586902566810811509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2013854391268377873874339 3020781586902566810811509)
                  ·
                    refine ⟨283198273772115638513579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3020781586902566810811509 283198273772115638513579)
                    ·
                      rfl

theorem cell22_827290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 2, 1, 2, 1, 5].length) (baseStart_827290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827290 prefixEnd_827290 := by exact prefixLift 827290
  have htrace : WordTrace (prefixWord ++ tailWord_827290) baseStart_827290 baseEnd_827290 := by
    simpa [prefixWord, tailWord_827290, baseEnd_827290] using wordTrace_append hprefix tailTrace_827290
  have hstable : (prefixWord ++ tailWord_827290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827290).length < 2 ^ (prefixWord ++ tailWord_827290).sum := by decide
  have hdescent : baseEnd_827290 < baseStart_827290 := by decide
  rcases family_descends (prefixWord ++ tailWord_827290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827303 : List Nat := [1, 1, 6, 1, 2, 11]
def baseStart_827303 : Nat := 118140960795 + 827303 * 2 ^ 59
def prefixEnd_827303 : Nat := 4983230072969 + 3 ^ 40 * 827303 * 2
def baseEnd_827303 : Nat := 3496329925157875777019

theorem tailTrace_827303 : CollatzResearch.WordTrace tailWord_827303 prefixEnd_827303 3496329925157875777019 := by
  unfold tailWord_827303
  simp only [CollatzResearch.WordTrace]
  refine ⟨30174219321829997948670563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20116146214553331965780375 30174219321829997948670563)
  ·
    refine ⟨45261328982744996923005845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30174219321829997948670563 45261328982744996923005845)
    ·
      refine ⟨2121624796066171730765899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45261328982744996923005845 2121624796066171730765899)
      ·
        refine ⟨3182437194099257596148849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2121624796066171730765899 3182437194099257596148849)
        ·
          refine ⟨2386827895574443197111637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3182437194099257596148849 2386827895574443197111637)
          ·
            refine ⟨3496329925157875777019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 2386827895574443197111637 3496329925157875777019)
            ·
              rfl

theorem cell22_827303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 11].length) (baseStart_827303 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827303 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827303 prefixEnd_827303 := by exact prefixLift 827303
  have htrace : WordTrace (prefixWord ++ tailWord_827303) baseStart_827303 baseEnd_827303 := by
    simpa [prefixWord, tailWord_827303, baseEnd_827303] using wordTrace_append hprefix tailTrace_827303
  have hstable : (prefixWord ++ tailWord_827303).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827303).length < 2 ^ (prefixWord ++ tailWord_827303).sum := by decide
  have hdescent : baseEnd_827303 < baseStart_827303 := by decide
  rcases family_descends (prefixWord ++ tailWord_827303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827457 : List Nat := [1, 2, 5, 1, 2, 1, 1, 3, 2, 4]
def baseStart_827457 : Nat := 118140960795 + 827457 * 2 ^ 59
def prefixEnd_827457 : Nat := 4983230072969 + 3 ^ 40 * 827457 * 2
def baseEnd_827457 : Nat := 283255441284982869588067

theorem tailTrace_827457 : CollatzResearch.WordTrace tailWord_827457 prefixEnd_827457 283255441284982869588067 := by
  unfold tailWord_827457
  simp only [CollatzResearch.WordTrace]
  refine ⟨30179836163272082249776625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20119890775514721499851083 30179836163272082249776625)
  ·
    refine ⟨22634877122454061687332469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30179836163272082249776625 22634877122454061687332469)
    ·
      refine ⟨2122019730230068283187419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22634877122454061687332469 2122019730230068283187419)
      ·
        refine ⟨3183029595345102424781129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2122019730230068283187419 3183029595345102424781129)
        ·
          refine ⟨2387272196508826818585847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3183029595345102424781129 2387272196508826818585847)
          ·
            refine ⟨3580908294763240227878771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2387272196508826818585847 3580908294763240227878771)
            ·
              refine ⟨5371362442144860341818157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3580908294763240227878771 5371362442144860341818157)
              ·
                refine ⟨2014260915804322628181809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5371362442144860341818157 2014260915804322628181809)
                ·
                  refine ⟨1510695686853241971136357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2014260915804322628181809 1510695686853241971136357)
                  ·
                    refine ⟨283255441284982869588067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1510695686853241971136357 283255441284982869588067)
                    ·
                      rfl

theorem cell22_827457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_827457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827457 prefixEnd_827457 := by exact prefixLift 827457
  have htrace : WordTrace (prefixWord ++ tailWord_827457) baseStart_827457 baseEnd_827457 := by
    simpa [prefixWord, tailWord_827457, baseEnd_827457] using wordTrace_append hprefix tailTrace_827457
  have hstable : (prefixWord ++ tailWord_827457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827457).length < 2 ^ (prefixWord ++ tailWord_827457).sum := by decide
  have hdescent : baseEnd_827457 < baseStart_827457 := by decide
  rcases family_descends (prefixWord ++ tailWord_827457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827478 : List Nat := [5, 2, 2, 1, 1, 1, 4, 2, 4]
def baseStart_827478 : Nat := 118140960795 + 827478 * 2 ^ 59
def prefixEnd_827478 : Nat := 4983230072969 + 3 ^ 40 * 827478 * 2
def baseEnd_827478 : Nat := 94420876671381938271001

theorem tailTrace_827478 : CollatzResearch.WordTrace tailWord_827478 prefixEnd_827478 94420876671381938271001 := by
  unfold tailWord_827478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1886287631012250177268193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20120401397464001890860725 1886287631012250177268193)
  ·
    refine ⟨1414715723259187632951145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1886287631012250177268193 1414715723259187632951145)
    ·
      refine ⟨1061036792444390724713359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1414715723259187632951145 1061036792444390724713359)
      ·
        refine ⟨1591555188666586087070039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1061036792444390724713359 1591555188666586087070039)
        ·
          refine ⟨2387332782999879130605059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1591555188666586087070039 2387332782999879130605059)
          ·
            refine ⟨3580999174499818695907589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2387332782999879130605059 3580999174499818695907589)
            ·
              refine ⟨671437345218716005482673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3580999174499818695907589 671437345218716005482673)
              ·
                refine ⟨503578008914037004112005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 671437345218716005482673 503578008914037004112005)
                ·
                  refine ⟨94420876671381938271001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 503578008914037004112005 94420876671381938271001)
                  ·
                    rfl

theorem cell22_827478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_827478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827478 prefixEnd_827478 := by exact prefixLift 827478
  have htrace : WordTrace (prefixWord ++ tailWord_827478) baseStart_827478 baseEnd_827478 := by
    simpa [prefixWord, tailWord_827478, baseEnd_827478] using wordTrace_append hprefix tailTrace_827478
  have hstable : (prefixWord ++ tailWord_827478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827478).length < 2 ^ (prefixWord ++ tailWord_827478).sum := by decide
  have hdescent : baseEnd_827478 < baseStart_827478 := by decide
  rcases family_descends (prefixWord ++ tailWord_827478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827577 : List Nat := [1, 2, 1, 4, 1, 2, 1, 1, 6, 3]
def baseStart_827577 : Nat := 118140960795 + 827577 * 2 ^ 59
def prefixEnd_827577 : Nat := 4983230072969 + 3 ^ 40 * 827577 * 2
def baseEnd_827577 : Nat := 283296519737342556587699

theorem tailTrace_827577 : CollatzResearch.WordTrace tailWord_827577 prefixEnd_827577 283296519737342556587699 := by
  unfold tailWord_827577
  simp only [CollatzResearch.WordTrace]
  refine ⟨30184212922837342744144985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20122808615224895162763323 30184212922837342744144985)
  ·
    refine ⟨22638159692128007058108739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30184212922837342744144985 22638159692128007058108739)
    ·
      refine ⟨33957239538192010587163109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22638159692128007058108739 33957239538192010587163109)
      ·
        refine ⟨6366982413411001985093083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33957239538192010587163109 6366982413411001985093083)
        ·
          refine ⟨9550473620116502977639625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6366982413411001985093083 9550473620116502977639625)
          ·
            refine ⟨7162855215087377233229719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9550473620116502977639625 7162855215087377233229719)
            ·
              refine ⟨10744282822631065849844579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7162855215087377233229719 10744282822631065849844579)
              ·
                refine ⟨16116424233946598774766869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10744282822631065849844579 16116424233946598774766869)
                ·
                  refine ⟨755457385966246817567197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16116424233946598774766869 755457385966246817567197)
                  ·
                    refine ⟨283296519737342556587699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 755457385966246817567197 283296519737342556587699)
                    ·
                      rfl

theorem cell22_827577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 1, 1, 6, 3].length) (baseStart_827577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827577 prefixEnd_827577 := by exact prefixLift 827577
  have htrace : WordTrace (prefixWord ++ tailWord_827577) baseStart_827577 baseEnd_827577 := by
    simpa [prefixWord, tailWord_827577, baseEnd_827577] using wordTrace_append hprefix tailTrace_827577
  have hstable : (prefixWord ++ tailWord_827577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827577).length < 2 ^ (prefixWord ++ tailWord_827577).sum := by decide
  have hdescent : baseEnd_827577 < baseStart_827577 := by decide
  rcases family_descends (prefixWord ++ tailWord_827577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827594 : List Nat := [3, 1, 2, 1, 3, 1, 2, 4, 2, 3]
def baseStart_827594 : Nat := 118140960795 + 827594 * 2 ^ 59
def prefixEnd_827594 : Nat := 4983230072969 + 3 ^ 40 * 827594 * 2
def baseEnd_827594 : Nat := 283302339184760178912647

theorem tailTrace_827594 : CollatzResearch.WordTrace tailWord_827594 prefixEnd_827594 283302339184760178912647 := by
  unfold tailWord_827594
  simp only [CollatzResearch.WordTrace]
  refine ⟨7546208240943938661878459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20123221975850503098342557 7546208240943938661878459)
  ·
    refine ⟨11319312361415907992817689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7546208240943938661878459 11319312361415907992817689)
    ·
      refine ⟨8489484271061930994613267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11319312361415907992817689 8489484271061930994613267)
      ·
        refine ⟨12734226406592896491919901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8489484271061930994613267 12734226406592896491919901)
        ·
          refine ⟨4775334902472336184469963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12734226406592896491919901 4775334902472336184469963)
          ·
            refine ⟨7163002353708504276704945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4775334902472336184469963 7163002353708504276704945)
            ·
              refine ⟨5372251765281378207528709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7163002353708504276704945 5372251765281378207528709)
              ·
                refine ⟨1007297205990258413911633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5372251765281378207528709 1007297205990258413911633)
                ·
                  refine ⟨755472904492693810433725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1007297205990258413911633 755472904492693810433725)
                  ·
                    refine ⟨283302339184760178912647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 755472904492693810433725 283302339184760178912647)
                    ·
                      rfl

theorem cell22_827594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 1, 2, 4, 2, 3].length) (baseStart_827594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827594 prefixEnd_827594 := by exact prefixLift 827594
  have htrace : WordTrace (prefixWord ++ tailWord_827594) baseStart_827594 baseEnd_827594 := by
    simpa [prefixWord, tailWord_827594, baseEnd_827594] using wordTrace_append hprefix tailTrace_827594
  have hstable : (prefixWord ++ tailWord_827594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827594).length < 2 ^ (prefixWord ++ tailWord_827594).sum := by decide
  have hdescent : baseEnd_827594 < baseStart_827594 := by decide
  rcases family_descends (prefixWord ++ tailWord_827594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827596 : List Nat := [2, 2, 1, 6, 1, 2, 1, 1, 6]
def baseStart_827596 : Nat := 118140960795 + 827596 * 2 ^ 59
def prefixEnd_827596 : Nat := 4983230072969 + 3 ^ 40 * 827596 * 2
def baseEnd_827596 : Nat := 94434341275210946787547

theorem tailTrace_827596 : CollatzResearch.WordTrace tailWord_827596 prefixEnd_827596 94434341275210946787547 := by
  unfold tailWord_827596
  simp only [CollatzResearch.WordTrace]
  refine ⟨15092452954884254494543321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20123270606512339326057761 15092452954884254494543321)
  ·
    refine ⟨11319339716163190870907491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15092452954884254494543321 11319339716163190870907491)
    ·
      refine ⟨16979009574244786306361237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11319339716163190870907491 16979009574244786306361237)
      ·
        refine ⟨795891073792724358110683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 16979009574244786306361237 795891073792724358110683)
        ·
          refine ⟨1193836610689086537166025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795891073792724358110683 1193836610689086537166025)
          ·
            refine ⟨895377458016814902874519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1193836610689086537166025 895377458016814902874519)
            ·
              refine ⟨1343066187025222354311779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 895377458016814902874519 1343066187025222354311779)
              ·
                refine ⟨2014599280537833531467669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1343066187025222354311779 2014599280537833531467669)
                ·
                  refine ⟨94434341275210946787547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2014599280537833531467669 94434341275210946787547)
                  ·
                    rfl

theorem cell22_827596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 1, 6].length) (baseStart_827596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827596 prefixEnd_827596 := by exact prefixLift 827596
  have htrace : WordTrace (prefixWord ++ tailWord_827596) baseStart_827596 baseEnd_827596 := by
    simpa [prefixWord, tailWord_827596, baseEnd_827596] using wordTrace_append hprefix tailTrace_827596
  have hstable : (prefixWord ++ tailWord_827596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827596).length < 2 ^ (prefixWord ++ tailWord_827596).sum := by decide
  have hdescent : baseEnd_827596 < baseStart_827596 := by decide
  rcases family_descends (prefixWord ++ tailWord_827596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827690 : List Nat := [3, 1, 4, 2, 2, 1, 2, 3, 1, 3]
def baseStart_827690 : Nat := 118140960795 + 827690 * 2 ^ 59
def prefixEnd_827690 : Nat := 4983230072969 + 3 ^ 40 * 827690 * 2
def baseEnd_827690 : Nat := 283335201946647928512353

theorem tailTrace_827690 : CollatzResearch.WordTrace tailWord_827690 prefixEnd_827690 283335201946647928512353 := by
  unfold tailWord_827690
  simp only [CollatzResearch.WordTrace]
  refine ⟨7547083592856990760752131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20125556247618642028672349 7547083592856990760752131)
  ·
    refine ⟨11320625389285486141128197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7547083592856990760752131 11320625389285486141128197)
    ·
      refine ⟨2122617260491028651461537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11320625389285486141128197 2122617260491028651461537)
      ·
        refine ⟨1591962945368271488596153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2122617260491028651461537 1591962945368271488596153)
        ·
          refine ⟨1193972209026203616447115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1591962945368271488596153 1193972209026203616447115)
          ·
            refine ⟨1790958313539305424670673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1193972209026203616447115 1790958313539305424670673)
            ·
              refine ⟨1343218735154479068503005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1790958313539305424670673 1343218735154479068503005)
              ·
                refine ⟨503707025682929650688627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1343218735154479068503005 503707025682929650688627)
                ·
                  refine ⟨755560538524394476032941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 503707025682929650688627 755560538524394476032941)
                  ·
                    refine ⟨283335201946647928512353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 755560538524394476032941 283335201946647928512353)
                    ·
                      rfl

theorem cell22_827690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 2, 3, 1, 3].length) (baseStart_827690 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827690 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827690 prefixEnd_827690 := by exact prefixLift 827690
  have htrace : WordTrace (prefixWord ++ tailWord_827690) baseStart_827690 baseEnd_827690 := by
    simpa [prefixWord, tailWord_827690, baseEnd_827690] using wordTrace_append hprefix tailTrace_827690
  have hstable : (prefixWord ++ tailWord_827690).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827690).length < 2 ^ (prefixWord ++ tailWord_827690).sum := by decide
  have hdescent : baseEnd_827690 < baseStart_827690 := by decide
  rcases family_descends (prefixWord ++ tailWord_827690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827699 : List Nat := [1, 1, 1, 2, 5, 1, 3, 3, 1, 4]
def baseStart_827699 : Nat := 118140960795 + 827699 * 2 ^ 59
def prefixEnd_827699 : Nat := 4983230072969 + 3 ^ 40 * 827699 * 2
def baseEnd_827699 : Nat := 283338282830574905037325

theorem tailTrace_827699 : CollatzResearch.WordTrace tailWord_827699 prefixEnd_827699 283338282830574905037325 := by
  unfold tailWord_827699
  simp only [CollatzResearch.WordTrace]
  refine ⟨30188662628395357580086151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20125775085596905053390767 30188662628395357580086151)
  ·
    refine ⟨45282993942593036370129227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30188662628395357580086151 45282993942593036370129227)
    ·
      refine ⟨67924490913889554555193841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45282993942593036370129227 67924490913889554555193841)
      ·
        refine ⟨50943368185417165916395381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67924490913889554555193841 50943368185417165916395381)
        ·
          refine ⟨4775940767382859304662067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 50943368185417165916395381 4775940767382859304662067)
          ·
            refine ⟨7163911151074288956993101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4775940767382859304662067 7163911151074288956993101)
            ·
              refine ⟨2686466681652858358872413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7163911151074288956993101 2686466681652858358872413)
              ·
                refine ⟨1007425005619821884577155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2686466681652858358872413 1007425005619821884577155)
                ·
                  refine ⟨1511137508429732826865733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1007425005619821884577155 1511137508429732826865733)
                  ·
                    refine ⟨283338282830574905037325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1511137508429732826865733 283338282830574905037325)
                    ·
                      rfl

theorem cell22_827699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 1, 3, 3, 1, 4].length) (baseStart_827699 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827699 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827699 prefixEnd_827699 := by exact prefixLift 827699
  have htrace : WordTrace (prefixWord ++ tailWord_827699) baseStart_827699 baseEnd_827699 := by
    simpa [prefixWord, tailWord_827699, baseEnd_827699] using wordTrace_append hprefix tailTrace_827699
  have hstable : (prefixWord ++ tailWord_827699).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827699).length < 2 ^ (prefixWord ++ tailWord_827699).sum := by decide
  have hdescent : baseEnd_827699 < baseStart_827699 := by decide
  rcases family_descends (prefixWord ++ tailWord_827699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827727 : List Nat := [1, 1, 2, 1, 1, 2, 1, 3, 6, 4]
def baseStart_827727 : Nat := 118140960795 + 827727 * 2 ^ 59
def prefixEnd_827727 : Nat := 4983230072969 + 3 ^ 40 * 827727 * 2
def baseEnd_827727 : Nat := 283347867802792165337239

theorem tailTrace_827727 : CollatzResearch.WordTrace tailWord_827727 prefixEnd_827727 283347867802792165337239 := by
  unfold tailWord_827727
  simp only [CollatzResearch.WordTrace]
  refine ⟨30189683872293918362105435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20126455914862612241403623 30189683872293918362105435)
  ·
    refine ⟨45284525808440877543158153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30189683872293918362105435 45284525808440877543158153)
    ·
      refine ⟨33963394356330658157368615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45284525808440877543158153 33963394356330658157368615)
      ·
        refine ⟨50945091534495987236052923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33963394356330658157368615 50945091534495987236052923)
        ·
          refine ⟨76417637301743980854079385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50945091534495987236052923 76417637301743980854079385)
          ·
            refine ⟨57313227976307985640559539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76417637301743980854079385 57313227976307985640559539)
            ·
              refine ⟨85969841964461978460839309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57313227976307985640559539 85969841964461978460839309)
              ·
                refine ⟨32238690736673241922814741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 85969841964461978460839309 32238690736673241922814741)
                ·
                  refine ⟨1511188628281558215131941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 32238690736673241922814741 1511188628281558215131941)
                  ·
                    refine ⟨283347867802792165337239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1511188628281558215131941 283347867802792165337239)
                    ·
                      rfl

theorem cell22_827727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 1, 3, 6, 4].length) (baseStart_827727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827727 prefixEnd_827727 := by exact prefixLift 827727
  have htrace : WordTrace (prefixWord ++ tailWord_827727) baseStart_827727 baseEnd_827727 := by
    simpa [prefixWord, tailWord_827727, baseEnd_827727] using wordTrace_append hprefix tailTrace_827727
  have hstable : (prefixWord ++ tailWord_827727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827727).length < 2 ^ (prefixWord ++ tailWord_827727).sum := by decide
  have hdescent : baseEnd_827727 < baseStart_827727 := by decide
  rcases family_descends (prefixWord ++ tailWord_827727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827729 : List Nat := [1, 2, 2, 1, 4, 2, 3, 1, 1, 5]
def baseStart_827729 : Nat := 118140960795 + 827729 * 2 ^ 59
def prefixEnd_827729 : Nat := 4983230072969 + 3 ^ 40 * 827729 * 2
def baseEnd_827729 : Nat := 283348552443664826787233

theorem tailTrace_827729 : CollatzResearch.WordTrace tailWord_827729 prefixEnd_827729 283348552443664826787233 := by
  unfold tailWord_827729
  simp only [CollatzResearch.WordTrace]
  refine ⟨30189756818286672703678241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20126504545524448469118827 30189756818286672703678241)
  ·
    refine ⟨22642317613715004527758681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30189756818286672703678241 22642317613715004527758681)
    ·
      refine ⟨16981738210286253395819011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22642317613715004527758681 16981738210286253395819011)
      ·
        refine ⟨25472607315429380093728517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16981738210286253395819011 25472607315429380093728517)
        ·
          refine ⟨4776113871643008767574097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25472607315429380093728517 4776113871643008767574097)
          ·
            refine ⟨3582085403732256575680573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4776113871643008767574097 3582085403732256575680573)
            ·
              refine ⟨1343282026399596215880215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3582085403732256575680573 1343282026399596215880215)
              ·
                refine ⟨2014923039599394323820323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1343282026399596215880215 2014923039599394323820323)
                ·
                  refine ⟨3022384559399091485730485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2014923039599394323820323 3022384559399091485730485)
                  ·
                    refine ⟨283348552443664826787233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3022384559399091485730485 283348552443664826787233)
                    ·
                      rfl

theorem cell22_827729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 5].length) (baseStart_827729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827729 prefixEnd_827729 := by exact prefixLift 827729
  have htrace : WordTrace (prefixWord ++ tailWord_827729) baseStart_827729 baseEnd_827729 := by
    simpa [prefixWord, tailWord_827729, baseEnd_827729] using wordTrace_append hprefix tailTrace_827729
  have hstable : (prefixWord ++ tailWord_827729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827729).length < 2 ^ (prefixWord ++ tailWord_827729).sum := by decide
  have hdescent : baseEnd_827729 < baseStart_827729 := by decide
  rcases family_descends (prefixWord ++ tailWord_827729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827746 : List Nat := [3, 3, 2, 1, 1, 2, 1, 2, 4, 3]
def baseStart_827746 : Nat := 118140960795 + 827746 * 2 ^ 59
def prefixEnd_827746 : Nat := 4983230072969 + 3 ^ 40 * 827746 * 2
def baseEnd_827746 : Nat := 283354371891082449112181

theorem tailTrace_827746 : CollatzResearch.WordTrace tailWord_827746 prefixEnd_827746 283354371891082449112181 := by
  unfold tailWord_827746
  simp only [CollatzResearch.WordTrace]
  refine ⟨7547594214806271151761773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20126917906150056404698061 7547594214806271151761773)
  ·
    refine ⟨2830347830552351681910665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7547594214806271151761773 2830347830552351681910665)
    ·
      refine ⟨2122760872914263761432999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2830347830552351681910665 2122760872914263761432999)
      ·
        refine ⟨3184141309371395642149499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2122760872914263761432999 3184141309371395642149499)
        ·
          refine ⟨4776211964057093463224249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3184141309371395642149499 4776211964057093463224249)
          ·
            refine ⟨3582158973042820097418187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4776211964057093463224249 3582158973042820097418187)
            ·
              refine ⟨5373238459564230146127281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3582158973042820097418187 5373238459564230146127281)
              ·
                refine ⟨4029928844673172609595461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5373238459564230146127281 4029928844673172609595461)
                ·
                  refine ⟨755611658376219864299149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4029928844673172609595461 755611658376219864299149)
                  ·
                    refine ⟨283354371891082449112181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 755611658376219864299149 283354371891082449112181)
                    ·
                      rfl

theorem cell22_827746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 2, 1, 2, 4, 3].length) (baseStart_827746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827746 prefixEnd_827746 := by exact prefixLift 827746
  have htrace : WordTrace (prefixWord ++ tailWord_827746) baseStart_827746 baseEnd_827746 := by
    simpa [prefixWord, tailWord_827746, baseEnd_827746] using wordTrace_append hprefix tailTrace_827746
  have hstable : (prefixWord ++ tailWord_827746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827746).length < 2 ^ (prefixWord ++ tailWord_827746).sum := by decide
  have hdescent : baseEnd_827746 < baseStart_827746 := by decide
  rcases family_descends (prefixWord ++ tailWord_827746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827825 : List Nat := [1, 2, 2, 4, 1, 2, 4, 2, 1, 3]
def baseStart_827825 : Nat := 118140960795 + 827825 * 2 ^ 59
def prefixEnd_827825 : Nat := 4983230072969 + 3 ^ 40 * 827825 * 2
def baseEnd_827825 : Nat := 283381415205552576386939

theorem tailTrace_827825 : CollatzResearch.WordTrace tailWord_827825 prefixEnd_827825 283381415205552576386939 := by
  unfold tailWord_827825
  simp only [CollatzResearch.WordTrace]
  refine ⟨30193258225938881099172929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20128838817292587399448619 30193258225938881099172929)
  ·
    refine ⟨22644943669454160824379697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30193258225938881099172929 22644943669454160824379697)
    ·
      refine ⟨16983707752090620618284773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22644943669454160824379697 16983707752090620618284773)
      ·
        refine ⟨3184445203516991365928395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16983707752090620618284773 3184445203516991365928395)
        ·
          refine ⟨4776667805275487048892593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3184445203516991365928395 4776667805275487048892593)
          ·
            refine ⟨3582500853956615286669445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4776667805275487048892593 3582500853956615286669445)
            ·
              refine ⟨671718910116865366250521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3582500853956615286669445 671718910116865366250521)
              ·
                refine ⟨503789182587649024687891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 671718910116865366250521 503789182587649024687891)
                ·
                  refine ⟨755683773881473537031837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 503789182587649024687891 755683773881473537031837)
                  ·
                    refine ⟨283381415205552576386939, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 755683773881473537031837 283381415205552576386939)
                    ·
                      rfl

theorem cell22_827825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 4, 2, 1, 3].length) (baseStart_827825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827825 prefixEnd_827825 := by exact prefixLift 827825
  have htrace : WordTrace (prefixWord ++ tailWord_827825) baseStart_827825 baseEnd_827825 := by
    simpa [prefixWord, tailWord_827825, baseEnd_827825] using wordTrace_append hprefix tailTrace_827825
  have hstable : (prefixWord ++ tailWord_827825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827825).length < 2 ^ (prefixWord ++ tailWord_827825).sum := by decide
  have hdescent : baseEnd_827825 < baseStart_827825 := by decide
  rcases family_descends (prefixWord ++ tailWord_827825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827836 : List Nat := [2, 2, 2, 4, 1, 2, 1, 1, 2, 5]
def baseStart_827836 : Nat := 118140960795 + 827836 * 2 ^ 59
def prefixEnd_827836 : Nat := 4983230072969 + 3 ^ 40 * 827836 * 2
def baseEnd_827836 : Nat := 283385180730352214361905

theorem tailTrace_827836 : CollatzResearch.WordTrace tailWord_827836 prefixEnd_827836 283385180730352214361905 := by
  unfold tailWord_827836
  simp only [CollatzResearch.WordTrace]
  refine ⟨15096829714449514988911681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20129106285932686651882241 15096829714449514988911681)
  ·
    refine ⟨11322622285837136241683761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15096829714449514988911681 11322622285837136241683761)
    ·
      refine ⟨8491966714377852181262821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11322622285837136241683761 8491966714377852181262821)
      ·
        refine ⟨1592243758945847283986779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8491966714377852181262821 1592243758945847283986779)
        ·
          refine ⟨2388365638418770925980169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1592243758945847283986779 2388365638418770925980169)
          ·
            refine ⟨1791274228814078194485127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2388365638418770925980169 1791274228814078194485127)
            ·
              refine ⟨2686911343221117291727691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1791274228814078194485127 2686911343221117291727691)
              ·
                refine ⟨4030367014831675937591537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2686911343221117291727691 4030367014831675937591537)
                ·
                  refine ⟨3022775261123756953193653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4030367014831675937591537 3022775261123756953193653)
                  ·
                    refine ⟨283385180730352214361905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3022775261123756953193653 283385180730352214361905)
                    ·
                      rfl

theorem cell22_827836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 2, 1, 1, 2, 5].length) (baseStart_827836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827836 prefixEnd_827836 := by exact prefixLift 827836
  have htrace : WordTrace (prefixWord ++ tailWord_827836) baseStart_827836 baseEnd_827836 := by
    simpa [prefixWord, tailWord_827836, baseEnd_827836] using wordTrace_append hprefix tailTrace_827836
  have hstable : (prefixWord ++ tailWord_827836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827836).length < 2 ^ (prefixWord ++ tailWord_827836).sum := by decide
  have hdescent : baseEnd_827836 < baseStart_827836 := by decide
  rcases family_descends (prefixWord ++ tailWord_827836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827881 : List Nat := [1, 2, 1, 1, 1, 2, 1, 8, 2, 3]
def baseStart_827881 : Nat := 118140960795 + 827881 * 2 ^ 59
def prefixEnd_827881 : Nat := 4983230072969 + 3 ^ 40 * 827881 * 2
def baseEnd_827881 : Nat := 283400585149987096986767

theorem tailTrace_827881 : CollatzResearch.WordTrace tailWord_827881 prefixEnd_827881 283400585149987096986767 := by
  unfold tailWord_827881
  simp only [CollatzResearch.WordTrace]
  refine ⟨30195300713736002663211497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20130200475824001775474331 30195300713736002663211497)
  ·
    refine ⟨22646475535302001997408623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30195300713736002663211497 22646475535302001997408623)
    ·
      refine ⟨33969713302953002996112935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22646475535302001997408623 33969713302953002996112935)
      ·
        refine ⟨50954569954429504494169403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33969713302953002996112935 50954569954429504494169403)
        ·
          refine ⟨76431854931644256741254105, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50954569954429504494169403 76431854931644256741254105)
          ·
            refine ⟨57323891198733192555940579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76431854931644256741254105 57323891198733192555940579)
            ·
              refine ⟨85985836798099788833910869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57323891198733192555940579 85985836798099788833910869)
              ·
                refine ⟨1007646524977731900397393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 85985836798099788833910869 1007646524977731900397393)
                ·
                  refine ⟨755734893733298925298045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1007646524977731900397393 755734893733298925298045)
                  ·
                    refine ⟨283400585149987096986767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 755734893733298925298045 283400585149987096986767)
                    ·
                      rfl

theorem cell22_827881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 8, 2, 3].length) (baseStart_827881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827881 prefixEnd_827881 := by exact prefixLift 827881
  have htrace : WordTrace (prefixWord ++ tailWord_827881) baseStart_827881 baseEnd_827881 := by
    simpa [prefixWord, tailWord_827881, baseEnd_827881] using wordTrace_append hprefix tailTrace_827881
  have hstable : (prefixWord ++ tailWord_827881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827881).length < 2 ^ (prefixWord ++ tailWord_827881).sum := by decide
  have hdescent : baseEnd_827881 < baseStart_827881 := by decide
  rcases family_descends (prefixWord ++ tailWord_827881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827911 : List Nat := [1, 1, 4, 3, 3, 1, 1, 8]
def baseStart_827911 : Nat := 118140960795 + 827911 * 2 ^ 59
def prefixEnd_827911 : Nat := 4983230072969 + 3 ^ 40 * 827911 * 2
def baseEnd_827911 : Nat := 31490094973675224304075

theorem tailTrace_827911 : CollatzResearch.WordTrace tailWord_827911 prefixEnd_827911 31490094973675224304075 := by
  unfold tailWord_827911
  simp only [CollatzResearch.WordTrace]
  refine ⟨30196394903627317786803587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20130929935751545191202391 30196394903627317786803587)
  ·
    refine ⟨45294592355440976680205381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30196394903627317786803587 45294592355440976680205381)
    ·
      refine ⟨8492736066645183127538509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45294592355440976680205381 8492736066645183127538509)
      ·
        refine ⟨3184776024991943672826941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8492736066645183127538509 3184776024991943672826941)
        ·
          refine ⟨1194291009371978877310103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3184776024991943672826941 1194291009371978877310103)
          ·
            refine ⟨1791436514057968315965155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1194291009371978877310103 1791436514057968315965155)
            ·
              refine ⟨2687154771086952473947733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1791436514057968315965155 2687154771086952473947733)
              ·
                refine ⟨31490094973675224304075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2687154771086952473947733 31490094973675224304075)
                ·
                  rfl

theorem cell22_827911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 1, 1, 8].length) (baseStart_827911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827911 prefixEnd_827911 := by exact prefixLift 827911
  have htrace : WordTrace (prefixWord ++ tailWord_827911) baseStart_827911 baseEnd_827911 := by
    simpa [prefixWord, tailWord_827911, baseEnd_827911] using wordTrace_append hprefix tailTrace_827911
  have hstable : (prefixWord ++ tailWord_827911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827911).length < 2 ^ (prefixWord ++ tailWord_827911).sum := by decide
  have hdescent : baseEnd_827911 < baseStart_827911 := by decide
  rcases family_descends (prefixWord ++ tailWord_827911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827917 : List Nat := [1, 7, 1, 1, 1, 1, 3, 3, 4]
def baseStart_827917 : Nat := 118140960795 + 827917 * 2 ^ 59
def prefixEnd_827917 : Nat := 4983230072969 + 3 ^ 40 * 827917 * 2
def baseEnd_827917 : Nat := 94470969561898334362219

theorem tailTrace_827917 : CollatzResearch.WordTrace tailWord_827917 prefixEnd_827917 94470969561898334362219 := by
  unfold tailWord_827917
  simp only [CollatzResearch.WordTrace]
  refine ⟨30196613741605580811522005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20131075827737053874348003 30196613741605580811522005)
  ·
    refine ⟨707733134568880800270047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 30196613741605580811522005 707733134568880800270047)
    ·
      refine ⟨1061599701853321200405071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 707733134568880800270047 1061599701853321200405071)
      ·
        refine ⟨1592399552779981800607607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1061599701853321200405071 1592399552779981800607607)
        ·
          refine ⟨2388599329169972700911411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1592399552779981800607607 2388599329169972700911411)
          ·
            refine ⟨3582898993754959051367117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2388599329169972700911411 3582898993754959051367117)
            ·
              refine ⟨1343587122658109644262669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3582898993754959051367117 1343587122658109644262669)
              ·
                refine ⟨503845170996791116598501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1343587122658109644262669 503845170996791116598501)
                ·
                  refine ⟨94470969561898334362219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 503845170996791116598501 94470969561898334362219)
                  ·
                    rfl

theorem cell22_827917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 3, 3, 4].length) (baseStart_827917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827917 prefixEnd_827917 := by exact prefixLift 827917
  have htrace : WordTrace (prefixWord ++ tailWord_827917) baseStart_827917 baseEnd_827917 := by
    simpa [prefixWord, tailWord_827917, baseEnd_827917] using wordTrace_append hprefix tailTrace_827917
  have hstable : (prefixWord ++ tailWord_827917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827917).length < 2 ^ (prefixWord ++ tailWord_827917).sum := by decide
  have hdescent : baseEnd_827917 < baseStart_827917 := by decide
  rcases family_descends (prefixWord ++ tailWord_827917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827949 : List Nat := [1, 5, 4, 1, 1, 1, 1, 3, 2, 3]
def baseStart_827949 : Nat := 118140960795 + 827949 * 2 ^ 59
def prefixEnd_827949 : Nat := 4983230072969 + 3 ^ 40 * 827949 * 2
def baseEnd_827949 : Nat := 283423862939657586286559

theorem tailTrace_827949 : CollatzResearch.WordTrace tailWord_827949 prefixEnd_827949 283423862939657586286559 := by
  unfold tailWord_827949
  simp only [CollatzResearch.WordTrace]
  refine ⟨30197780877489650276686901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20131853918326433517791267 30197780877489650276686901)
  ·
    refine ⟨2831041957264654713439397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30197780877489650276686901 2831041957264654713439397)
    ·
      refine ⟨530820366987122758769887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2831041957264654713439397 530820366987122758769887)
      ·
        refine ⟨796230550480684138154831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530820366987122758769887 796230550480684138154831)
        ·
          refine ⟨1194345825721026207232247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 796230550480684138154831 1194345825721026207232247)
          ·
            refine ⟨1791518738581539310848371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1194345825721026207232247 1791518738581539310848371)
            ·
              refine ⟨2687278107872308966272557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1791518738581539310848371 2687278107872308966272557)
              ·
                refine ⟨1007729290452115862352209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2687278107872308966272557 1007729290452115862352209)
                ·
                  refine ⟨755796967839086896764157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1007729290452115862352209 755796967839086896764157)
                  ·
                    refine ⟨283423862939657586286559, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 755796967839086896764157 283423862939657586286559)
                    ·
                      rfl

theorem cell22_827949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 1, 1, 1, 3, 2, 3].length) (baseStart_827949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827949 prefixEnd_827949 := by exact prefixLift 827949
  have htrace : WordTrace (prefixWord ++ tailWord_827949) baseStart_827949 baseEnd_827949 := by
    simpa [prefixWord, tailWord_827949, baseEnd_827949] using wordTrace_append hprefix tailTrace_827949
  have hstable : (prefixWord ++ tailWord_827949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827949).length < 2 ^ (prefixWord ++ tailWord_827949).sum := by decide
  have hdescent : baseEnd_827949 < baseStart_827949 := by decide
  rcases family_descends (prefixWord ++ tailWord_827949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_827984 : List Nat := [2, 1, 1, 1, 1, 3, 2, 1, 10]
def baseStart_827984 : Nat := 118140960795 + 827984 * 2 ^ 59
def prefixEnd_827984 : Nat := 4983230072969 + 3 ^ 40 * 827984 * 2
def baseEnd_827984 : Nat := 94478614718309720553817

theorem tailTrace_827984 : CollatzResearch.WordTrace tailWord_827984 prefixEnd_827984 94478614718309720553817 := by
  unfold tailWord_827984
  simp only [CollatzResearch.WordTrace]
  refine ⟨15099528716181425627105503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20132704954908567502807337 15099528716181425627105503)
  ·
    refine ⟨22649293074272138440658255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15099528716181425627105503 22649293074272138440658255)
    ·
      refine ⟨33973939611408207660987383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22649293074272138440658255 33973939611408207660987383)
      ·
        refine ⟨50960909417112311491481075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33973939611408207660987383 50960909417112311491481075)
        ·
          refine ⟨76441364125668467237221613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50960909417112311491481075 76441364125668467237221613)
          ·
            refine ⟨28665511547125675213958105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 76441364125668467237221613 28665511547125675213958105)
            ·
              refine ⟨21499133660344256410468579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28665511547125675213958105 21499133660344256410468579)
              ·
                refine ⟨32248700490516384615702869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21499133660344256410468579 32248700490516384615702869)
                ·
                  refine ⟨94478614718309720553817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 32248700490516384615702869 94478614718309720553817)
                  ·
                    rfl

theorem cell22_827984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 1, 10].length) (baseStart_827984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_827984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_827984 prefixEnd_827984 := by exact prefixLift 827984
  have htrace : WordTrace (prefixWord ++ tailWord_827984) baseStart_827984 baseEnd_827984 := by
    simpa [prefixWord, tailWord_827984, baseEnd_827984] using wordTrace_append hprefix tailTrace_827984
  have hstable : (prefixWord ++ tailWord_827984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_827984).length < 2 ^ (prefixWord ++ tailWord_827984).sum := by decide
  have hdescent : baseEnd_827984 < baseStart_827984 := by decide
  rcases family_descends (prefixWord ++ tailWord_827984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828018 : List Nat := [3, 2, 1, 2, 4, 1, 1, 2, 6]
def baseStart_828018 : Nat := 118140960795 + 828018 * 2 ^ 59
def prefixEnd_828018 : Nat := 4983230072969 + 3 ^ 40 * 828018 * 2
def baseEnd_828018 : Nat := 94482494349921468770449

theorem tailTrace_828018 : CollatzResearch.WordTrace tailWord_828018 prefixEnd_828018 94482494349921468770449 := by
  unfold tailWord_828018
  simp only [CollatzResearch.WordTrace]
  refine ⟨7550074378559918765237177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20133531676159783373965805 7550074378559918765237177)
  ·
    refine ⟨5662555783919939073927883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7550074378559918765237177 5662555783919939073927883)
    ·
      refine ⟨8493833675879908610891825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5662555783919939073927883 8493833675879908610891825)
      ·
        refine ⟨6370375256909931458168869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8493833675879908610891825 6370375256909931458168869)
        ·
          refine ⟨1194445360670612148406663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6370375256909931458168869 1194445360670612148406663)
          ·
            refine ⟨1791668041005918222609995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1194445360670612148406663 1791668041005918222609995)
            ·
              refine ⟨2687502061508877333914993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1791668041005918222609995 2687502061508877333914993)
              ·
                refine ⟨2015626546131658000436245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2687502061508877333914993 2015626546131658000436245)
                ·
                  refine ⟨94482494349921468770449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2015626546131658000436245 94482494349921468770449)
                  ·
                    rfl

theorem cell22_828018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 4, 1, 1, 2, 6].length) (baseStart_828018 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_828018 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_828018 prefixEnd_828018 := by exact prefixLift 828018
  have htrace : WordTrace (prefixWord ++ tailWord_828018) baseStart_828018 baseEnd_828018 := by
    simpa [prefixWord, tailWord_828018, baseEnd_828018] using wordTrace_append hprefix tailTrace_828018
  have hstable : (prefixWord ++ tailWord_828018).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828018).length < 2 ^ (prefixWord ++ tailWord_828018).sum := by decide
  have hdescent : baseEnd_828018 < baseStart_828018 := by decide
  rcases family_descends (prefixWord ++ tailWord_828018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828031 : List Nat := [1, 1, 2, 2, 1, 1, 1, 7, 2, 4]
def baseStart_828031 : Nat := 118140960795 + 828031 * 2 ^ 59
def prefixEnd_828031 : Nat := 4983230072969 + 3 ^ 40 * 828031 * 2
def baseEnd_828031 : Nat := 283451933215436705736307

theorem tailTrace_828031 : CollatzResearch.WordTrace tailWord_828031 prefixEnd_828031 283451933215436705736307 := by
  unfold tailWord_828031
  simp only [CollatzResearch.WordTrace]
  refine ⟨30200771663192578281171947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20133847775461718854114631 30200771663192578281171947)
  ·
    refine ⟨45301157494788867421757921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30200771663192578281171947 45301157494788867421757921)
    ·
      refine ⟨33975868121091650566318441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45301157494788867421757921 33975868121091650566318441)
      ·
        refine ⟨25481901090818737924738831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33975868121091650566318441 25481901090818737924738831)
        ·
          refine ⟨38222851636228106887108247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25481901090818737924738831 38222851636228106887108247)
          ·
            refine ⟨57334277454342160330662371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38222851636228106887108247 57334277454342160330662371)
            ·
              refine ⟨86001416181513240495993557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57334277454342160330662371 86001416181513240495993557)
              ·
                refine ⟨2015658191754216574124849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 86001416181513240495993557 2015658191754216574124849)
                ·
                  refine ⟨1511743643815662430593637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2015658191754216574124849 1511743643815662430593637)
                  ·
                    refine ⟨283451933215436705736307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1511743643815662430593637 283451933215436705736307)
                    ·
                      rfl

theorem cell22_828031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 7, 2, 4].length) (baseStart_828031 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_828031 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_828031 prefixEnd_828031 := by exact prefixLift 828031
  have htrace : WordTrace (prefixWord ++ tailWord_828031) baseStart_828031 baseEnd_828031 := by
    simpa [prefixWord, tailWord_828031, baseEnd_828031] using wordTrace_append hprefix tailTrace_828031
  have hstable : (prefixWord ++ tailWord_828031).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828031).length < 2 ^ (prefixWord ++ tailWord_828031).sum := by decide
  have hdescent : baseEnd_828031 < baseStart_828031 := by decide
  rcases family_descends (prefixWord ++ tailWord_828031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828033 : List Nat := [1, 2, 4, 2, 1, 1, 2, 2, 4, 3]
def baseStart_828033 : Nat := 118140960795 + 828033 * 2 ^ 59
def prefixEnd_828033 : Nat := 4983230072969 + 3 ^ 40 * 828033 * 2
def baseEnd_828033 : Nat := 283452617856309367186301

theorem tailTrace_828033 : CollatzResearch.WordTrace tailWord_828033 prefixEnd_828033 283452617856309367186301 := by
  unfold tailWord_828033
  simp only [CollatzResearch.WordTrace]
  refine ⟨30200844609185332622744753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20133896406123555081829835 30200844609185332622744753)
  ·
    refine ⟨22650633456888999467058565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30200844609185332622744753 22650633456888999467058565)
    ·
      refine ⟨4246993773166687400073481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22650633456888999467058565 4246993773166687400073481)
      ·
        refine ⟨3185245329875015550055111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4246993773166687400073481 3185245329875015550055111)
        ·
          refine ⟨4777867994812523325082667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3185245329875015550055111 4777867994812523325082667)
          ·
            refine ⟨7166801992218784987624001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4777867994812523325082667 7166801992218784987624001)
            ·
              refine ⟨5375101494164088740718001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7166801992218784987624001 5375101494164088740718001)
              ·
                refine ⟨4031326120623066555538501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5375101494164088740718001 4031326120623066555538501)
                ·
                  refine ⟨755873647616824979163469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4031326120623066555538501 755873647616824979163469)
                  ·
                    refine ⟨283452617856309367186301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 755873647616824979163469 283452617856309367186301)
                    ·
                      rfl

theorem cell22_828033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_828033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_828033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_828033 prefixEnd_828033 := by exact prefixLift 828033
  have htrace : WordTrace (prefixWord ++ tailWord_828033) baseStart_828033 baseEnd_828033 := by
    simpa [prefixWord, tailWord_828033, baseEnd_828033] using wordTrace_append hprefix tailTrace_828033
  have hstable : (prefixWord ++ tailWord_828033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828033).length < 2 ^ (prefixWord ++ tailWord_828033).sum := by decide
  have hdescent : baseEnd_828033 < baseStart_828033 := by decide
  rcases family_descends (prefixWord ++ tailWord_828033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828046 : List Nat := [4, 1, 1, 3, 1, 1, 11]
def baseStart_828046 : Nat := 118140960795 + 828046 * 2 ^ 59
def prefixEnd_828046 : Nat := 4983230072969 + 3 ^ 40 * 828046 * 2
def baseEnd_828046 : Nat := 10498409926740061726343

theorem tailTrace_828046 : CollatzResearch.WordTrace tailWord_828046 prefixEnd_828046 10498409926740061726343 := by
  unfold tailWord_828046
  simp only [CollatzResearch.WordTrace]
  refine ⟨3775164844767279480370999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20134212505425490561978661 3775164844767279480370999)
  ·
    refine ⟨5662747267150919220556499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3775164844767279480370999 5662747267150919220556499)
    ·
      refine ⟨8494120900726378830834749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5662747267150919220556499 8494120900726378830834749)
      ·
        refine ⟨3185295337772392061563031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8494120900726378830834749 3185295337772392061563031)
        ·
          refine ⟨4777943006658588092344547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3185295337772392061563031 4777943006658588092344547)
          ·
            refine ⟨7166914509987882138516821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4777943006658588092344547 7166914509987882138516821)
            ·
              refine ⟨10498409926740061726343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7166914509987882138516821 10498409926740061726343)
              ·
                rfl

theorem cell22_828046_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 11].length) (baseStart_828046 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_828046 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_828046 prefixEnd_828046 := by exact prefixLift 828046
  have htrace : WordTrace (prefixWord ++ tailWord_828046) baseStart_828046 baseEnd_828046 := by
    simpa [prefixWord, tailWord_828046, baseEnd_828046] using wordTrace_append hprefix tailTrace_828046
  have hstable : (prefixWord ++ tailWord_828046).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828046).length < 2 ^ (prefixWord ++ tailWord_828046).sum := by decide
  have hdescent : baseEnd_828046 < baseStart_828046 := by decide
  rcases family_descends (prefixWord ++ tailWord_828046) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828050 : List Nat := [3, 2, 3, 1, 2, 2, 1, 1, 4, 3]
def baseStart_828050 : Nat := 118140960795 + 828050 * 2 ^ 59
def prefixEnd_828050 : Nat := 4983230072969 + 3 ^ 40 * 828050 * 2
def baseEnd_828050 : Nat := 283458437303726989511249

theorem tailTrace_828050 : CollatzResearch.WordTrace tailWord_828050 prefixEnd_828050 283458437303726989511249 := by
  unfold tailWord_828050
  simp only [CollatzResearch.WordTrace]
  refine ⟨7550366162530936131528401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20134309766749163017409069 7550366162530936131528401)
  ·
    refine ⟨5662774621898202098646301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7550366162530936131528401 5662774621898202098646301)
    ·
      refine ⟨2123540483211825786992363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5662774621898202098646301 2123540483211825786992363)
      ·
        refine ⟨3185310724817738680488545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2123540483211825786992363 3185310724817738680488545)
        ·
          refine ⟨2388983043613304010366409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3185310724817738680488545 2388983043613304010366409)
          ·
            refine ⟨1791737282709978007774807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2388983043613304010366409 1791737282709978007774807)
            ·
              refine ⟨2687605924064967011662211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1791737282709978007774807 2687605924064967011662211)
              ·
                refine ⟨4031408886097450517493317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2687605924064967011662211 4031408886097450517493317)
                ·
                  refine ⟨755889166143271972029997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4031408886097450517493317 755889166143271972029997)
                  ·
                    refine ⟨283458437303726989511249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 755889166143271972029997 283458437303726989511249)
                    ·
                      rfl

theorem cell22_828050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 2, 1, 1, 4, 3].length) (baseStart_828050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_828050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_828050 prefixEnd_828050 := by exact prefixLift 828050
  have htrace : WordTrace (prefixWord ++ tailWord_828050) baseStart_828050 baseEnd_828050 := by
    simpa [prefixWord, tailWord_828050, baseEnd_828050] using wordTrace_append hprefix tailTrace_828050
  have hstable : (prefixWord ++ tailWord_828050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828050).length < 2 ^ (prefixWord ++ tailWord_828050).sum := by decide
  have hdescent : baseEnd_828050 < baseStart_828050 := by decide
  rcases family_descends (prefixWord ++ tailWord_828050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828086 : List Nat := [5, 1, 3, 1, 3, 1, 1, 3, 4]
def baseStart_828086 : Nat := 118140960795 + 828086 * 2 ^ 59
def prefixEnd_828086 : Nat := 4983230072969 + 3 ^ 40 * 828086 * 2
def baseEnd_828086 : Nat := 94490253613144965203713

theorem tailTrace_828086 : CollatzResearch.WordTrace tailWord_828086 prefixEnd_828086 94490253613144965203713 := by
  unfold tailWord_828086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1887673604874582667151507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20135185118662215116282741 1887673604874582667151507)
  ·
    refine ⟨2831510407311874000727261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1887673604874582667151507 2831510407311874000727261)
    ·
      refine ⟨1061816402741952750272723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2831510407311874000727261 1061816402741952750272723)
      ·
        refine ⟨1592724604112929125409085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1061816402741952750272723 1592724604112929125409085)
        ·
          refine ⟨597271726542348422028407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1592724604112929125409085 597271726542348422028407)
          ·
            refine ⟨895907589813522633042611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597271726542348422028407 895907589813522633042611)
            ·
              refine ⟨1343861384720283949563917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 895907589813522633042611 1343861384720283949563917)
              ·
                refine ⟨503948019270106481086469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1343861384720283949563917 503948019270106481086469)
                ·
                  refine ⟨94490253613144965203713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 503948019270106481086469 94490253613144965203713)
                  ·
                    rfl

theorem cell22_828086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 3, 1, 1, 3, 4].length) (baseStart_828086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_828086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_828086 prefixEnd_828086 := by exact prefixLift 828086
  have htrace : WordTrace (prefixWord ++ tailWord_828086) baseStart_828086 baseEnd_828086 := by
    simpa [prefixWord, tailWord_828086, baseEnd_828086] using wordTrace_append hprefix tailTrace_828086
  have hstable : (prefixWord ++ tailWord_828086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828086).length < 2 ^ (prefixWord ++ tailWord_828086).sum := by decide
  have hdescent : baseEnd_828086 < baseStart_828086 := by decide
  rcases family_descends (prefixWord ++ tailWord_828086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828097 : List Nat := [1, 2, 6, 2, 2, 1, 8]
def baseStart_828097 : Nat := 118140960795 + 828097 * 2 ^ 59
def prefixEnd_828097 : Nat := 4983230072969 + 3 ^ 40 * 828097 * 2
def baseEnd_828097 : Nat := 10499056532008686429115

theorem tailTrace_828097 : CollatzResearch.WordTrace tailWord_828097 prefixEnd_828097 10499056532008686429115 := by
  unfold tailWord_828097
  simp only [CollatzResearch.WordTrace]
  refine ⟨30203178880953471553074545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20135452587302314368716363 30203178880953471553074545)
  ·
    refine ⟨22652384160715103664805909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30203178880953471553074545 22652384160715103664805909)
    ·
      refine ⟨1061830507533520484287777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22652384160715103664805909 1061830507533520484287777)
      ·
        refine ⟨796372880650140363215833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1061830507533520484287777 796372880650140363215833)
        ·
          refine ⟨597279660487605272411875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 796372880650140363215833 597279660487605272411875)
          ·
            refine ⟨895919490731407908617813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597279660487605272411875 895919490731407908617813)
            ·
              refine ⟨10499056532008686429115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 895919490731407908617813 10499056532008686429115)
              ·
                rfl

theorem cell22_828097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 8].length) (baseStart_828097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_828097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_828097 prefixEnd_828097 := by exact prefixLift 828097
  have htrace : WordTrace (prefixWord ++ tailWord_828097) baseStart_828097 baseEnd_828097 := by
    simpa [prefixWord, tailWord_828097, baseEnd_828097] using wordTrace_append hprefix tailTrace_828097
  have hstable : (prefixWord ++ tailWord_828097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828097).length < 2 ^ (prefixWord ++ tailWord_828097).sum := by decide
  have hdescent : baseEnd_828097 < baseStart_828097 := by decide
  rcases family_descends (prefixWord ++ tailWord_828097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828108 : List Nat := [2, 2, 1, 5, 1, 1, 2, 1, 7]
def baseStart_828108 : Nat := 118140960795 + 828108 * 2 ^ 59
def prefixEnd_828108 : Nat := 4983230072969 + 3 ^ 40 * 828108 * 2
def baseEnd_828108 : Nat := 94492763963011390520357

theorem tailTrace_828108 : CollatzResearch.WordTrace tailWord_828108 prefixEnd_828108 94492763963011390520357 := by
  unfold tailWord_828108
  simp only [CollatzResearch.WordTrace]
  refine ⟨15101790041956810215862489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20135720055942413621149985 15101790041956810215862489)
  ·
    refine ⟨11326342531467607661896867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15101790041956810215862489 11326342531467607661896867)
    ·
      refine ⟨16989513797201411492845301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11326342531467607661896867 16989513797201411492845301)
      ·
        refine ⟨1592766918487632327454247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 16989513797201411492845301 1592766918487632327454247)
        ·
          refine ⟨2389150377731448491181371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1592766918487632327454247 2389150377731448491181371)
          ·
            refine ⟨3583725566597172736772057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2389150377731448491181371 3583725566597172736772057)
            ·
              refine ⟨2687794174947879552579043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3583725566597172736772057 2687794174947879552579043)
              ·
                refine ⟨4031691262421819328868565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2687794174947879552579043 4031691262421819328868565)
                ·
                  refine ⟨94492763963011390520357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4031691262421819328868565 94492763963011390520357)
                  ·
                    rfl

theorem cell22_828108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 2, 1, 7].length) (baseStart_828108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_828108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_828108 prefixEnd_828108 := by exact prefixLift 828108
  have htrace : WordTrace (prefixWord ++ tailWord_828108) baseStart_828108 baseEnd_828108 := by
    simpa [prefixWord, tailWord_828108, baseEnd_828108] using wordTrace_append hprefix tailTrace_828108
  have hstable : (prefixWord ++ tailWord_828108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828108).length < 2 ^ (prefixWord ++ tailWord_828108).sum := by decide
  have hdescent : baseEnd_828108 < baseStart_828108 := by decide
  rcases family_descends (prefixWord ++ tailWord_828108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828170 : List Nat := [3, 1, 2, 2, 1, 2, 3, 4, 4]
def baseStart_828170 : Nat := 118140960795 + 828170 * 2 ^ 59
def prefixEnd_828170 : Nat := 4983230072969 + 3 ^ 40 * 828170 * 2
def baseEnd_828170 : Nat := 94499838585362225503627

theorem tailTrace_828170 : CollatzResearch.WordTrace tailWord_828170 prefixEnd_828170 94499838585362225503627 := by
  unfold tailWord_828170
  simp only [CollatzResearch.WordTrace]
  refine ⟨7551460352422251255120491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20137227606459336680321309 7551460352422251255120491)
  ·
    refine ⟨11327190528633376882680737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7551460352422251255120491 11327190528633376882680737)
    ·
      refine ⟨8495392896475032662010553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11327190528633376882680737 8495392896475032662010553)
      ·
        refine ⟨6371544672356274496507915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8495392896475032662010553 6371544672356274496507915)
        ·
          refine ⟨9557317008534411744761873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6371544672356274496507915 9557317008534411744761873)
          ·
            refine ⟨7167987756400808808571405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9557317008534411744761873 7167987756400808808571405)
            ·
              refine ⟨2687995408650303303214277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7167987756400808808571405 2687995408650303303214277)
              ·
                refine ⟨503999139121931869352677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2687995408650303303214277 503999139121931869352677)
                ·
                  refine ⟨94499838585362225503627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 503999139121931869352677 94499838585362225503627)
                  ·
                    rfl

theorem cell22_828170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 3, 4, 4].length) (baseStart_828170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_828170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_828170 prefixEnd_828170 := by exact prefixLift 828170
  have htrace : WordTrace (prefixWord ++ tailWord_828170) baseStart_828170 baseEnd_828170 := by
    simpa [prefixWord, tailWord_828170, baseEnd_828170] using wordTrace_append hprefix tailTrace_828170
  have hstable : (prefixWord ++ tailWord_828170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828170).length < 2 ^ (prefixWord ++ tailWord_828170).sum := by decide
  have hdescent : baseEnd_828170 < baseStart_828170 := by decide
  rcases family_descends (prefixWord ++ tailWord_828170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828243 : List Nat := [1, 1, 1, 2, 1, 1, 3, 7, 5]
def baseStart_828243 : Nat := 118140960795 + 828243 * 2 ^ 59
def prefixEnd_828243 : Nat := 4983230072969 + 3 ^ 40 * 828243 * 2
def baseEnd_828243 : Nat := 94508168382646273145219

theorem tailTrace_828243 : CollatzResearch.WordTrace tailWord_828243 prefixEnd_828243 94508168382646273145219 := by
  unfold tailWord_828243
  simp only [CollatzResearch.WordTrace]
  refine ⟨30208503938424538487889383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20139002625616358991926255 30208503938424538487889383)
  ·
    refine ⟨45312755907636807731834075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30208503938424538487889383 45312755907636807731834075)
    ·
      refine ⟨67969133861455211597751113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45312755907636807731834075 67969133861455211597751113)
      ·
        refine ⟨50976850396091408698313335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 67969133861455211597751113 50976850396091408698313335)
        ·
          refine ⟨76465275594137113047470003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50976850396091408698313335 76465275594137113047470003)
          ·
            refine ⟨114697913391205669571205005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76465275594137113047470003 114697913391205669571205005)
            ·
              refine ⟨43011717521702126089201877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 114697913391205669571205005 43011717521702126089201877)
              ·
                refine ⟨1008087129414893580215669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 43011717521702126089201877 1008087129414893580215669)
                ·
                  refine ⟨94508168382646273145219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1008087129414893580215669 94508168382646273145219)
                  ·
                    rfl

theorem cell22_828243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 7, 5].length) (baseStart_828243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_828243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_828243 prefixEnd_828243 := by exact prefixLift 828243
  have htrace : WordTrace (prefixWord ++ tailWord_828243) baseStart_828243 baseEnd_828243 := by
    simpa [prefixWord, tailWord_828243, baseEnd_828243] using wordTrace_append hprefix tailTrace_828243
  have hstable : (prefixWord ++ tailWord_828243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828243).length < 2 ^ (prefixWord ++ tailWord_828243).sum := by decide
  have hdescent : baseEnd_828243 < baseStart_828243 := by decide
  rcases family_descends (prefixWord ++ tailWord_828243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828264 : List Nat := [2, 1, 4, 2, 1, 2, 3, 3, 1, 3]
def baseStart_828264 : Nat := 118140960795 + 828264 * 2 ^ 59
def prefixEnd_828264 : Nat := 4983230072969 + 3 ^ 40 * 828264 * 2
def baseEnd_828264 : Nat := 283531693877101764660593

theorem tailTrace_828264 : CollatzResearch.WordTrace tailWord_828264 prefixEnd_828264 283531693877101764660593 := by
  unfold tailWord_828264
  simp only [CollatzResearch.WordTrace]
  refine ⟨15104634935674229537201923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20139513247565639382935897 15104634935674229537201923)
  ·
    refine ⟨22656952403511344305802885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15104634935674229537201923 22656952403511344305802885)
    ·
      refine ⟨4248178575658377057338041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22656952403511344305802885 4248178575658377057338041)
      ·
        refine ⟨3186133931743782793003531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4248178575658377057338041 3186133931743782793003531)
        ·
          refine ⟨4779200897615674189505297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3186133931743782793003531 4779200897615674189505297)
          ·
            refine ⟨3584400673211755642128973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4779200897615674189505297 3584400673211755642128973)
            ·
              refine ⟨1344150252454408365798365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3584400673211755642128973 1344150252454408365798365)
              ·
                refine ⟨504056344670403137174387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1344150252454408365798365 504056344670403137174387)
                ·
                  refine ⟨756084517005604705761581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 504056344670403137174387 756084517005604705761581)
                  ·
                    refine ⟨283531693877101764660593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 756084517005604705761581 283531693877101764660593)
                    ·
                      rfl

theorem cell22_828264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_828264 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_828264 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_828264 prefixEnd_828264 := by exact prefixLift 828264
  have htrace : WordTrace (prefixWord ++ tailWord_828264) baseStart_828264 baseEnd_828264 := by
    simpa [prefixWord, tailWord_828264, baseEnd_828264] using wordTrace_append hprefix tailTrace_828264
  have hstable : (prefixWord ++ tailWord_828264).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828264).length < 2 ^ (prefixWord ++ tailWord_828264).sum := by decide
  have hdescent : baseEnd_828264 < baseStart_828264 := by decide
  rcases family_descends (prefixWord ++ tailWord_828264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828288 : List Nat := [2, 1, 1, 2, 1, 2, 2, 5, 6]
def baseStart_828288 : Nat := 118140960795 + 828288 * 2 ^ 59
def prefixEnd_828288 : Nat := 4983230072969 + 3 ^ 40 * 828288 * 2
def baseEnd_828288 : Nat := 94513303189191234020173

theorem tailTrace_828288 : CollatzResearch.WordTrace tailWord_828288 prefixEnd_828288 94513303189191234020173 := by
  unfold tailWord_828288
  simp only [CollatzResearch.WordTrace]
  refine ⟨15105072611630755586638759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20140096815507674115518345 15105072611630755586638759)
  ·
    refine ⟨22657608917446133379958139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15105072611630755586638759 22657608917446133379958139)
    ·
      refine ⟨33986413376169200069937209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22657608917446133379958139 33986413376169200069937209)
      ·
        refine ⟨25489810032126900052452907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33986413376169200069937209 25489810032126900052452907)
        ·
          refine ⟨38234715048190350078679361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25489810032126900052452907 38234715048190350078679361)
          ·
            refine ⟨28676036286142762559009521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38234715048190350078679361 28676036286142762559009521)
            ·
              refine ⟨21507027214607071919257141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28676036286142762559009521 21507027214607071919257141)
              ·
                refine ⟨2016283801369412992430357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21507027214607071919257141 2016283801369412992430357)
                ·
                  refine ⟨94513303189191234020173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2016283801369412992430357 94513303189191234020173)
                  ·
                    rfl

theorem cell22_828288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 2, 5, 6].length) (baseStart_828288 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_828288 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_828288 prefixEnd_828288 := by exact prefixLift 828288
  have htrace : WordTrace (prefixWord ++ tailWord_828288) baseStart_828288 baseEnd_828288 := by
    simpa [prefixWord, tailWord_828288, baseEnd_828288] using wordTrace_append hprefix tailTrace_828288
  have hstable : (prefixWord ++ tailWord_828288).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828288).length < 2 ^ (prefixWord ++ tailWord_828288).sum := by decide
  have hdescent : baseEnd_828288 < baseStart_828288 := by decide
  rcases family_descends (prefixWord ++ tailWord_828288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828320 : List Nat := [2, 1, 1, 4, 1, 1, 2, 1, 6, 3]
def baseStart_828320 : Nat := 118140960795 + 828320 * 2 ^ 59
def prefixEnd_828320 : Nat := 4983230072969 + 3 ^ 40 * 828320 * 2
def baseEnd_828320 : Nat := 283550863821536285260421

theorem tailTrace_828320 : CollatzResearch.WordTrace tailWord_828320 prefixEnd_828320 283550863821536285260421 := by
  unfold tailWord_828320
  simp only [CollatzResearch.WordTrace]
  refine ⟨15105656179572790319221207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20140874906097053758961609 15105656179572790319221207)
  ·
    refine ⟨22658484269359185478831811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15105656179572790319221207 22658484269359185478831811)
    ·
      refine ⟨33987726404038778218247717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22658484269359185478831811 33987726404038778218247717)
      ·
        refine ⟨6372698700757270915921447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 33987726404038778218247717 6372698700757270915921447)
        ·
          refine ⟨9559048051135906373882171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6372698700757270915921447 9559048051135906373882171)
          ·
            refine ⟨14338572076703859560823257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9559048051135906373882171 14338572076703859560823257)
            ·
              refine ⟨10753929057527894670617443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14338572076703859560823257 10753929057527894670617443)
              ·
                refine ⟨16130893586291842005926165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10753929057527894670617443 16130893586291842005926165)
                ·
                  refine ⟨756135636857430094027789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16130893586291842005926165 756135636857430094027789)
                  ·
                    refine ⟨283550863821536285260421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 756135636857430094027789 283550863821536285260421)
                    ·
                      rfl

theorem cell22_828320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 2, 1, 6, 3].length) (baseStart_828320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_828320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_828320 prefixEnd_828320 := by exact prefixLift 828320
  have htrace : WordTrace (prefixWord ++ tailWord_828320) baseStart_828320 baseEnd_828320 := by
    simpa [prefixWord, tailWord_828320, baseEnd_828320] using wordTrace_append hprefix tailTrace_828320
  have hstable : (prefixWord ++ tailWord_828320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828320).length < 2 ^ (prefixWord ++ tailWord_828320).sum := by decide
  have hdescent : baseEnd_828320 < baseStart_828320 := by decide
  rcases family_descends (prefixWord ++ tailWord_828320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828399 : List Nat := [1, 1, 2, 1, 4, 3, 2, 4, 1, 3]
def baseStart_828399 : Nat := 118140960795 + 828399 * 2 ^ 59
def prefixEnd_828399 : Nat := 4983230072969 + 3 ^ 40 * 828399 * 2
def baseEnd_828399 : Nat := 283577907136006412535179

theorem tailTrace_828399 : CollatzResearch.WordTrace tailWord_828399 prefixEnd_828399 283577907136006412535179 := by
  unfold tailWord_828399
  simp only [CollatzResearch.WordTrace]
  refine ⟨30214193725859377130568251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20142795817239584753712167 30214193725859377130568251)
  ·
    refine ⟨45321290588789065695852377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30214193725859377130568251 45321290588789065695852377)
    ·
      refine ⟨33990967941591799271889283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45321290588789065695852377 33990967941591799271889283)
      ·
        refine ⟨50986451912387698907833925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33990967941591799271889283 50986451912387698907833925)
        ·
          refine ⟨9559959733572693545218861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 50986451912387698907833925 9559959733572693545218861)
          ·
            refine ⟨3584984900089760079457073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9559959733572693545218861 3584984900089760079457073)
            ·
              refine ⟨2688738675067320059592805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3584984900089760079457073 2688738675067320059592805)
              ·
                refine ⟨504138501575122511173651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2688738675067320059592805 504138501575122511173651)
                ·
                  refine ⟨756207752362683766760477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 504138501575122511173651 756207752362683766760477)
                  ·
                    refine ⟨283577907136006412535179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 756207752362683766760477 283577907136006412535179)
                    ·
                      rfl

theorem cell22_828399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 4, 1, 3].length) (baseStart_828399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_828399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_828399 prefixEnd_828399 := by exact prefixLift 828399
  have htrace : WordTrace (prefixWord ++ tailWord_828399) baseStart_828399 baseEnd_828399 := by
    simpa [prefixWord, tailWord_828399, baseEnd_828399] using wordTrace_append hprefix tailTrace_828399
  have hstable : (prefixWord ++ tailWord_828399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828399).length < 2 ^ (prefixWord ++ tailWord_828399).sum := by decide
  have hdescent : baseEnd_828399 < baseStart_828399 := by decide
  rcases family_descends (prefixWord ++ tailWord_828399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828418 : List Nat := [3, 4, 1, 3, 2, 1, 2, 6]
def baseStart_828418 : Nat := 118140960795 + 828418 * 2 ^ 59
def prefixEnd_828418 : Nat := 4983230072969 + 3 ^ 40 * 828418 * 2
def baseEnd_828418 : Nat := 31509379024921855145569

theorem tailTrace_828418 : CollatzResearch.WordTrace tailWord_828418 prefixEnd_828418 31509379024921855145569 := by
  unfold tailWord_828418
  simp only [CollatzResearch.WordTrace]
  refine ⟨7553721678197635843877477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20143257808527028917006605 7553721678197635843877477)
  ·
    refine ⟨1416322814662056720727027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7553721678197635843877477 1416322814662056720727027)
    ·
      refine ⟨2124484221993085081090541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1416322814662056720727027 2124484221993085081090541)
      ·
        refine ⟨796681583247406905408953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2124484221993085081090541 796681583247406905408953)
        ·
          refine ⟨597511187435555179056715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 796681583247406905408953 597511187435555179056715)
          ·
            refine ⟨896266781153332768585073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597511187435555179056715 896266781153332768585073)
            ·
              refine ⟨672200085864999576438805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 896266781153332768585073 672200085864999576438805)
              ·
                refine ⟨31509379024921855145569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 672200085864999576438805 31509379024921855145569)
                ·
                  rfl

theorem cell22_828418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 2, 6].length) (baseStart_828418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_828418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_828418 prefixEnd_828418 := by exact prefixLift 828418
  have htrace : WordTrace (prefixWord ++ tailWord_828418) baseStart_828418 baseEnd_828418 := by
    simpa [prefixWord, tailWord_828418, baseEnd_828418] using wordTrace_append hprefix tailTrace_828418
  have hstable : (prefixWord ++ tailWord_828418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828418).length < 2 ^ (prefixWord ++ tailWord_828418).sum := by decide
  have hdescent : baseEnd_828418 < baseStart_828418 := by decide
  rcases family_descends (prefixWord ++ tailWord_828418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828425 : List Nat := [1, 2, 1, 1, 3, 1, 1, 5, 3, 4]
def baseStart_828425 : Nat := 118140960795 + 828425 * 2 ^ 59
def prefixEnd_828425 : Nat := 4983230072969 + 3 ^ 40 * 828425 * 2
def baseEnd_828425 : Nat := 283586807467351011385099

theorem tailTrace_828425 : CollatzResearch.WordTrace tailWord_828425 prefixEnd_828425 283586807467351011385099 := by
  unfold tailWord_828425
  simp only [CollatzResearch.WordTrace]
  refine ⟨30215142023765183571014729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20143428015843455714009819 30215142023765183571014729)
  ·
    refine ⟨22661356517823887678261047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30215142023765183571014729 22661356517823887678261047)
    ·
      refine ⟨33992034776735831517391571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22661356517823887678261047 33992034776735831517391571)
      ·
        refine ⟨50988052165103747276087357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33992034776735831517391571 50988052165103747276087357)
        ·
          refine ⟨19120519561913905228532759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 50988052165103747276087357 19120519561913905228532759)
          ·
            refine ⟨28680779342870857842799139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19120519561913905228532759 28680779342870857842799139)
            ·
              refine ⟨43021169014306286764198709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28680779342870857842799139 43021169014306286764198709)
              ·
                refine ⟨4033234595091214384143629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43021169014306286764198709 4033234595091214384143629)
                ·
                  refine ⟨1512462973159205394053861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4033234595091214384143629 1512462973159205394053861)
                  ·
                    refine ⟨283586807467351011385099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1512462973159205394053861 283586807467351011385099)
                    ·
                      rfl

theorem cell22_828425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 5, 3, 4].length) (baseStart_828425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_828425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_828425 prefixEnd_828425 := by exact prefixLift 828425
  have htrace : WordTrace (prefixWord ++ tailWord_828425) baseStart_828425 baseEnd_828425 := by
    simpa [prefixWord, tailWord_828425, baseEnd_828425] using wordTrace_append hprefix tailTrace_828425
  have hstable : (prefixWord ++ tailWord_828425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828425).length < 2 ^ (prefixWord ++ tailWord_828425).sum := by decide
  have hdescent : baseEnd_828425 < baseStart_828425 := by decide
  rcases family_descends (prefixWord ++ tailWord_828425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828442 : List Nat := [3, 1, 1, 3, 1, 2, 1, 5, 1, 4]
def baseStart_828442 : Nat := 118140960795 + 828442 * 2 ^ 59
def prefixEnd_828442 : Nat := 4983230072969 + 3 ^ 40 * 828442 * 2
def baseEnd_828442 : Nat := 283592626914768633710047

theorem tailTrace_828442 : CollatzResearch.WordTrace tailWord_828442 prefixEnd_828442 283592626914768633710047 := by
  unfold tailWord_828442
  simp only [CollatzResearch.WordTrace]
  refine ⟨7553940516175898868595895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20143841376469063649589053 7553940516175898868595895)
  ·
    refine ⟨11330910774263848302893843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7553940516175898868595895 11330910774263848302893843)
    ·
      refine ⟨16996366161395772454340765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11330910774263848302893843 16996366161395772454340765)
      ·
        refine ⟨6373637310523414670377787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16996366161395772454340765 6373637310523414670377787)
        ·
          refine ⟨9560455965785122005566681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6373637310523414670377787 9560455965785122005566681)
          ·
            refine ⟨7170341974338841504175011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9560455965785122005566681 7170341974338841504175011)
            ·
              refine ⟨10755512961508262256262517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7170341974338841504175011 10755512961508262256262517)
              ·
                refine ⟨1008329340141399586524611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10755512961508262256262517 1008329340141399586524611)
                ·
                  refine ⟨1512494010212099379786917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1008329340141399586524611 1512494010212099379786917)
                  ·
                    refine ⟨283592626914768633710047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1512494010212099379786917 283592626914768633710047)
                    ·
                      rfl

theorem cell22_828442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 1, 5, 1, 4].length) (baseStart_828442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_828442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_828442 prefixEnd_828442 := by exact prefixLift 828442
  have htrace : WordTrace (prefixWord ++ tailWord_828442) baseStart_828442 baseEnd_828442 := by
    simpa [prefixWord, tailWord_828442, baseEnd_828442] using wordTrace_append hprefix tailTrace_828442
  have hstable : (prefixWord ++ tailWord_828442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828442).length < 2 ^ (prefixWord ++ tailWord_828442).sum := by decide
  have hdescent : baseEnd_828442 < baseStart_828442 := by decide
  rcases family_descends (prefixWord ++ tailWord_828442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828485 : List Nat := [1, 3, 1, 1, 1, 3, 4, 8]
def baseStart_828485 : Nat := 118140960795 + 828485 * 2 ^ 59
def prefixEnd_828485 : Nat := 4983230072969 + 3 ^ 40 * 828485 * 2
def baseEnd_828485 : Nat := 31511927410392317209435

theorem tailTrace_828485 : CollatzResearch.WordTrace tailWord_828485 prefixEnd_828485 31511927410392317209435 := by
  unfold tailWord_828485
  simp only [CollatzResearch.WordTrace]
  refine ⟨30217330403547813818198909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20144886935698542545465939 30217330403547813818198909)
  ·
    refine ⟨11331498901330430181824591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30217330403547813818198909 11331498901330430181824591)
    ·
      refine ⟨16997248351995645272736887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11331498901330430181824591 16997248351995645272736887)
      ·
        refine ⟨25495872527993467909105331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16997248351995645272736887 25495872527993467909105331)
        ·
          refine ⟨38243808791990201863657997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25495872527993467909105331 38243808791990201863657997)
          ·
            refine ⟨14341428296996325698871749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38243808791990201863657997 14341428296996325698871749)
            ·
              refine ⟨2689017805686811068538453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14341428296996325698871749 2689017805686811068538453)
              ·
                refine ⟨31511927410392317209435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2689017805686811068538453 31511927410392317209435)
                ·
                  rfl

theorem cell22_828485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 4, 8].length) (baseStart_828485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_828485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_828485 prefixEnd_828485 := by exact prefixLift 828485
  have htrace : WordTrace (prefixWord ++ tailWord_828485) baseStart_828485 baseEnd_828485 := by
    simpa [prefixWord, tailWord_828485, baseEnd_828485] using wordTrace_append hprefix tailTrace_828485
  have hstable : (prefixWord ++ tailWord_828485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828485).length < 2 ^ (prefixWord ++ tailWord_828485).sum := by decide
  have hdescent : baseEnd_828485 < baseStart_828485 := by decide
  rcases family_descends (prefixWord ++ tailWord_828485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828487 : List Nat := [1, 1, 4, 1, 3, 2, 1, 3, 2, 4]
def baseStart_828487 : Nat := 118140960795 + 828487 * 2 ^ 59
def prefixEnd_828487 : Nat := 4983230072969 + 3 ^ 40 * 828487 * 2
def baseEnd_828487 : Nat := 283608031334403516334909

theorem tailTrace_828487 : CollatzResearch.WordTrace tailWord_828487 prefixEnd_828487 283608031334403516334909 := by
  unfold tailWord_828487
  simp only [CollatzResearch.WordTrace]
  refine ⟨30217403349540568159771715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20144935566360378773181143 30217403349540568159771715)
  ·
    refine ⟨45326105024310852239657573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30217403349540568159771715 45326105024310852239657573)
    ·
      refine ⟨8498644692058284794935795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45326105024310852239657573 8498644692058284794935795)
      ·
        refine ⟨12747967038087427192403693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8498644692058284794935795 12747967038087427192403693)
        ·
          refine ⟨4780487639282785197151385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12747967038087427192403693 4780487639282785197151385)
          ·
            refine ⟨3585365729462088897863539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4780487639282785197151385 3585365729462088897863539)
            ·
              refine ⟨5378048594193133346795309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3585365729462088897863539 5378048594193133346795309)
              ·
                refine ⟨2016768222822425005048241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5378048594193133346795309 2016768222822425005048241)
                ·
                  refine ⟨1512576167116818753786181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2016768222822425005048241 1512576167116818753786181)
                  ·
                    refine ⟨283608031334403516334909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1512576167116818753786181 283608031334403516334909)
                    ·
                      rfl

theorem cell22_828487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_828487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_828487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_828487 prefixEnd_828487 := by exact prefixLift 828487
  have htrace : WordTrace (prefixWord ++ tailWord_828487) baseStart_828487 baseEnd_828487 := by
    simpa [prefixWord, tailWord_828487, baseEnd_828487] using wordTrace_append hprefix tailTrace_828487
  have hstable : (prefixWord ++ tailWord_828487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828487).length < 2 ^ (prefixWord ++ tailWord_828487).sum := by decide
  have hdescent : baseEnd_828487 < baseStart_828487 := by decide
  rcases family_descends (prefixWord ++ tailWord_828487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828594 : List Nat := [3, 2, 1, 1, 1, 4, 1, 4, 1, 4]
def baseStart_828594 : Nat := 118140960795 + 828594 * 2 ^ 59
def prefixEnd_828594 : Nat := 4983230072969 + 3 ^ 40 * 828594 * 2
def baseEnd_828594 : Nat := 283644659621090903909581

theorem tailTrace_828594 : CollatzResearch.WordTrace tailWord_828594 prefixEnd_828594 283644659621090903909581 := by
  unfold tailWord_828594
  simp only [CollatzResearch.WordTrace]
  refine ⟨7555326490038231358479209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20147537306768616955944557 7555326490038231358479209)
  ·
    refine ⟨5666494867528673518859407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7555326490038231358479209 5666494867528673518859407)
    ·
      refine ⟨8499742301293010278289111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5666494867528673518859407 8499742301293010278289111)
      ·
        refine ⟨12749613451939515417433667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8499742301293010278289111 12749613451939515417433667)
        ·
          refine ⟨19124420177909273126150501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12749613451939515417433667 19124420177909273126150501)
          ·
            refine ⟨3585828783357988711153219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19124420177909273126150501 3585828783357988711153219)
            ·
              refine ⟨5378743175036983066729829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3585828783357988711153219 5378743175036983066729829)
              ·
                refine ⟨1008514345319434325011843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5378743175036983066729829 1008514345319434325011843)
                ·
                  refine ⟨1512771517979151487517765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1008514345319434325011843 1512771517979151487517765)
                  ·
                    refine ⟨283644659621090903909581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1512771517979151487517765 283644659621090903909581)
                    ·
                      rfl

theorem cell22_828594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 1, 4, 1, 4].length) (baseStart_828594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_828594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_828594 prefixEnd_828594 := by exact prefixLift 828594
  have htrace : WordTrace (prefixWord ++ tailWord_828594) baseStart_828594 baseEnd_828594 := by
    simpa [prefixWord, tailWord_828594, baseEnd_828594] using wordTrace_append hprefix tailTrace_828594
  have hstable : (prefixWord ++ tailWord_828594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828594).length < 2 ^ (prefixWord ++ tailWord_828594).sum := by decide
  have hdescent : baseEnd_828594 < baseStart_828594 := by decide
  rcases family_descends (prefixWord ++ tailWord_828594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828607 : List Nat := [1, 1, 2, 2, 2, 2, 2, 4, 1, 5]
def baseStart_828607 : Nat := 118140960795 + 828607 * 2 ^ 59
def prefixEnd_828607 : Nat := 4983230072969 + 3 ^ 40 * 828607 * 2
def baseEnd_828607 : Nat := 283649109786763203334541

theorem tailTrace_828607 : CollatzResearch.WordTrace tailWord_828607 prefixEnd_828607 283649109786763203334541 := by
  unfold tailWord_828607
  simp only [CollatzResearch.WordTrace]
  refine ⟨30221780109105828654140075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20147853406070552436093383 30221780109105828654140075)
  ·
    refine ⟨45332670163658742981210113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30221780109105828654140075 45332670163658742981210113)
    ·
      refine ⟨33999502622744057235907585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45332670163658742981210113 33999502622744057235907585)
      ·
        refine ⟨25499626967058042926930689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33999502622744057235907585 25499626967058042926930689)
        ·
          refine ⟨19124720225293532195198017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25499626967058042926930689 19124720225293532195198017)
          ·
            refine ⟨14343540168970149146398513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19124720225293532195198017 14343540168970149146398513)
            ·
              refine ⟨10757655126727611859798885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14343540168970149146398513 10757655126727611859798885)
              ·
                refine ⟨2017060336261427223712291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10757655126727611859798885 2017060336261427223712291)
                ·
                  refine ⟨3025590504392140835568437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2017060336261427223712291 3025590504392140835568437)
                  ·
                    refine ⟨283649109786763203334541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3025590504392140835568437 283649109786763203334541)
                    ·
                      rfl

theorem cell22_828607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 2, 4, 1, 5].length) (baseStart_828607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_828607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_828607 prefixEnd_828607 := by exact prefixLift 828607
  have htrace : WordTrace (prefixWord ++ tailWord_828607) baseStart_828607 baseEnd_828607 := by
    simpa [prefixWord, tailWord_828607, baseEnd_828607] using wordTrace_append hprefix tailTrace_828607
  have hstable : (prefixWord ++ tailWord_828607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828607).length < 2 ^ (prefixWord ++ tailWord_828607).sum := by decide
  have hdescent : baseEnd_828607 < baseStart_828607 := by decide
  rcases family_descends (prefixWord ++ tailWord_828607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828641 : List Nat := [1, 2, 3, 1, 3, 3, 1, 3, 2, 3]
def baseStart_828641 : Nat := 118140960795 + 828641 * 2 ^ 59
def prefixEnd_828641 : Nat := 4983230072969 + 3 ^ 40 * 828641 * 2
def baseEnd_828641 : Nat := 283660748681598447984437

theorem tailTrace_828641 : CollatzResearch.WordTrace tailWord_828641 prefixEnd_828641 283660748681598447984437 := by
  unfold tailWord_828641
  simp only [CollatzResearch.WordTrace]
  refine ⟨30223020190982652460877777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20148680127321768307251851 30223020190982652460877777)
  ·
    refine ⟨22667265143236989345658333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30223020190982652460877777 22667265143236989345658333)
    ·
      refine ⟨8500224428713871004621875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22667265143236989345658333 8500224428713871004621875)
      ·
        refine ⟨12750336643070806506932813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8500224428713871004621875 12750336643070806506932813)
        ·
          refine ⟨4781376241151552440099805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12750336643070806506932813 4781376241151552440099805)
          ·
            refine ⟨1793016090431832165037427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4781376241151552440099805 1793016090431832165037427)
            ·
              refine ⟨2689524135647748247556141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1793016090431832165037427 2689524135647748247556141)
              ·
                refine ⟨1008571550867905592833553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2689524135647748247556141 1008571550867905592833553)
                ·
                  refine ⟨756428663150929194625165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1008571550867905592833553 756428663150929194625165)
                  ·
                    refine ⟨283660748681598447984437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 756428663150929194625165 283660748681598447984437)
                    ·
                      rfl

theorem cell22_828641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 3, 1, 3, 2, 3].length) (baseStart_828641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_828641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_828641 prefixEnd_828641 := by exact prefixLift 828641
  have htrace : WordTrace (prefixWord ++ tailWord_828641) baseStart_828641 baseEnd_828641 := by
    simpa [prefixWord, tailWord_828641, baseEnd_828641] using wordTrace_append hprefix tailTrace_828641
  have hstable : (prefixWord ++ tailWord_828641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828641).length < 2 ^ (prefixWord ++ tailWord_828641).sum := by decide
  have hdescent : baseEnd_828641 < baseStart_828641 := by decide
  rcases family_descends (prefixWord ++ tailWord_828641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828821 : List Nat := [1, 3, 2, 1, 1, 2, 2, 4, 3, 3]
def baseStart_828821 : Nat := 118140960795 + 828821 * 2 ^ 59
def prefixEnd_828821 : Nat := 4983230072969 + 3 ^ 40 * 828821 * 2
def baseEnd_828821 : Nat := 283722366360137978483885

theorem tailTrace_828821 : CollatzResearch.WordTrace tailWord_828821 prefixEnd_828821 283722366360137978483885 := by
  unfold tailWord_828821
  simp only [CollatzResearch.WordTrace]
  refine ⟨30229585330330543202430317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20153056886887028801620211 30229585330330543202430317)
  ·
    refine ⟨11336094498873953700911369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30229585330330543202430317 11336094498873953700911369)
    ·
      refine ⟨8502070874155465275683527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11336094498873953700911369 8502070874155465275683527)
      ·
        refine ⟨12753106311233197913525291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8502070874155465275683527 12753106311233197913525291)
        ·
          refine ⟨19129659466849796870287937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12753106311233197913525291 19129659466849796870287937)
          ·
            refine ⟨14347244600137347652715953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19129659466849796870287937 14347244600137347652715953)
            ·
              refine ⟨10760433450103010739536965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14347244600137347652715953 10760433450103010739536965)
              ·
                refine ⟨2017581271894314513663181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10760433450103010739536965 2017581271894314513663181)
                ·
                  refine ⟨756592976960367942623693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2017581271894314513663181 756592976960367942623693)
                  ·
                    refine ⟨283722366360137978483885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 756592976960367942623693 283722366360137978483885)
                    ·
                      rfl

theorem cell22_828821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 2, 4, 3, 3].length) (baseStart_828821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_828821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_828821 prefixEnd_828821 := by exact prefixLift 828821
  have htrace : WordTrace (prefixWord ++ tailWord_828821) baseStart_828821 baseEnd_828821 := by
    simpa [prefixWord, tailWord_828821, baseEnd_828821] using wordTrace_append hprefix tailTrace_828821
  have hstable : (prefixWord ++ tailWord_828821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828821).length < 2 ^ (prefixWord ++ tailWord_828821).sum := by decide
  have hdescent : baseEnd_828821 < baseStart_828821 := by decide
  rcases family_descends (prefixWord ++ tailWord_828821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828868 : List Nat := [2, 3, 3, 2, 1, 1, 2, 3, 5]
def baseStart_828868 : Nat := 118140960795 + 828868 * 2 ^ 59
def prefixEnd_828868 : Nat := 4983230072969 + 3 ^ 40 * 828868 * 2
def baseEnd_828868 : Nat := 94579485140215174186247

theorem tailTrace_828868 : CollatzResearch.WordTrace tailWord_828868 prefixEnd_828868 94579485140215174186247 := by
  unfold tailWord_828868
  simp only [CollatzResearch.WordTrace]
  refine ⟨15115649780580135114695629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20154199707440180152927505 15115649780580135114695629)
  ·
    refine ⟨5668368667717550668010861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15115649780580135114695629 5668368667717550668010861)
    ·
      refine ⟨2125638250394081500504073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5668368667717550668010861 2125638250394081500504073)
      ·
        refine ⟨1594228687795561125378055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2125638250394081500504073 1594228687795561125378055)
        ·
          refine ⟨2391343031693341688067083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1594228687795561125378055 2391343031693341688067083)
          ·
            refine ⟨3587014547540012532100625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2391343031693341688067083 3587014547540012532100625)
            ·
              refine ⟨2690260910655009399075469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3587014547540012532100625 2690260910655009399075469)
              ·
                refine ⟨1008847841495628524653301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2690260910655009399075469 1008847841495628524653301)
                ·
                  refine ⟨94579485140215174186247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1008847841495628524653301 94579485140215174186247)
                  ·
                    rfl

theorem cell22_828868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 2, 3, 5].length) (baseStart_828868 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_828868 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_828868 prefixEnd_828868 := by exact prefixLift 828868
  have htrace : WordTrace (prefixWord ++ tailWord_828868) baseStart_828868 baseEnd_828868 := by
    simpa [prefixWord, tailWord_828868, baseEnd_828868] using wordTrace_append hprefix tailTrace_828868
  have hstable : (prefixWord ++ tailWord_828868).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828868).length < 2 ^ (prefixWord ++ tailWord_828868).sum := by decide
  have hdescent : baseEnd_828868 < baseStart_828868 := by decide
  rcases family_descends (prefixWord ++ tailWord_828868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828879 : List Nat := [1, 1, 2, 1, 1, 4, 3, 1, 8]
def baseStart_828879 : Nat := 118140960795 + 828879 * 2 ^ 59
def prefixEnd_828879 : Nat := 4983230072969 + 3 ^ 40 * 828879 * 2
def baseEnd_828879 : Nat := 94580740315148386844569

theorem tailTrace_828879 : CollatzResearch.WordTrace tailWord_828879 prefixEnd_828879 94580740315148386844569 := by
  unfold tailWord_828879
  simp only [CollatzResearch.WordTrace]
  refine ⟨30231700764120419108041691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20154467176080279405361127 30231700764120419108041691)
  ·
    refine ⟨45347551146180628662062537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30231700764120419108041691 45347551146180628662062537)
    ·
      refine ⟨34010663359635471496546903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45347551146180628662062537 34010663359635471496546903)
      ·
        refine ⟨51015995039453207244820355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34010663359635471496546903 51015995039453207244820355)
        ·
          refine ⟨76523992559179810867230533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51015995039453207244820355 76523992559179810867230533)
          ·
            refine ⟨14348248604846214537605725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 76523992559179810867230533 14348248604846214537605725)
            ·
              refine ⟨5380593226817330451602147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14348248604846214537605725 5380593226817330451602147)
              ·
                refine ⟨8070889840225995677403221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5380593226817330451602147 8070889840225995677403221)
                ·
                  refine ⟨94580740315148386844569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8070889840225995677403221 94580740315148386844569)
                  ·
                    rfl

theorem cell22_828879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 3, 1, 8].length) (baseStart_828879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_828879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_828879 prefixEnd_828879 := by exact prefixLift 828879
  have htrace : WordTrace (prefixWord ++ tailWord_828879) baseStart_828879 baseEnd_828879 := by
    simpa [prefixWord, tailWord_828879, baseEnd_828879] using wordTrace_append hprefix tailTrace_828879
  have hstable : (prefixWord ++ tailWord_828879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828879).length < 2 ^ (prefixWord ++ tailWord_828879).sum := by decide
  have hdescent : baseEnd_828879 < baseStart_828879 := by decide
  rcases family_descends (prefixWord ++ tailWord_828879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_828913 : List Nat := [1, 2, 2, 2, 3, 2, 2, 4, 4]
def baseStart_828913 : Nat := 118140960795 + 828913 * 2 ^ 59
def prefixEnd_828913 : Nat := 4983230072969 + 3 ^ 40 * 828913 * 2
def baseEnd_828913 : Nat := 94584619946760135061201

theorem tailTrace_828913 : CollatzResearch.WordTrace tailWord_828913 prefixEnd_828913 94584619946760135061201 := by
  unfold tailWord_828913
  simp only [CollatzResearch.WordTrace]
  refine ⟨30232940845997242914779393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20155293897331495276519595 30232940845997242914779393)
  ·
    refine ⟨22674705634497932186084545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30232940845997242914779393 22674705634497932186084545)
    ·
      refine ⟨17006029225873449139563409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22674705634497932186084545 17006029225873449139563409)
      ·
        refine ⟨12754521919405086854672557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17006029225873449139563409 12754521919405086854672557)
        ·
          refine ⟨4782945719776907570502209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12754521919405086854672557 4782945719776907570502209)
          ·
            refine ⟨3587209289832680677876657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4782945719776907570502209 3587209289832680677876657)
            ·
              refine ⟨2690406967374510508407493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3587209289832680677876657 2690406967374510508407493)
              ·
                refine ⟨504451306382720720326405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2690406967374510508407493 504451306382720720326405)
                ·
                  refine ⟨94584619946760135061201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 504451306382720720326405 94584619946760135061201)
                  ·
                    rfl

theorem cell22_828913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 2, 4, 4].length) (baseStart_828913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_828913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_828913 prefixEnd_828913 := by exact prefixLift 828913
  have htrace : WordTrace (prefixWord ++ tailWord_828913) baseStart_828913 baseEnd_828913 := by
    simpa [prefixWord, tailWord_828913, baseEnd_828913] using wordTrace_append hprefix tailTrace_828913
  have hstable : (prefixWord ++ tailWord_828913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_828913).length < 2 ^ (prefixWord ++ tailWord_828913).sum := by decide
  have hdescent : baseEnd_828913 < baseStart_828913 := by decide
  rcases family_descends (prefixWord ++ tailWord_828913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829020 : List Nat := [2, 2, 4, 1, 2, 2, 2, 2, 5]
def baseStart_829020 : Nat := 118140960795 + 829020 * 2 ^ 59
def prefixEnd_829020 : Nat := 4983230072969 + 3 ^ 40 * 829020 * 2
def baseEnd_829020 : Nat := 94596829375655930919425

theorem tailTrace_829020 : CollatzResearch.WordTrace tailWord_829020 prefixEnd_829020 94596829375655930919425 := by
  unfold tailWord_829020
  simp only [CollatzResearch.WordTrace]
  refine ⟨15118421728304800094462257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20157895637739733459283009 15118421728304800094462257)
  ·
    refine ⟨11338816296228600070846693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15118421728304800094462257 11338816296228600070846693)
    ·
      refine ⟨2126028055542862513283755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11338816296228600070846693 2126028055542862513283755)
      ·
        refine ⟨3189042083314293769925633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2126028055542862513283755 3189042083314293769925633)
        ·
          refine ⟨2391781562485720327444225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3189042083314293769925633 2391781562485720327444225)
          ·
            refine ⟨1793836171864290245583169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2391781562485720327444225 1793836171864290245583169)
            ·
              refine ⟨1345377128898217684187377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1793836171864290245583169 1345377128898217684187377)
              ·
                refine ⟨1009032846673663263140533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1345377128898217684187377 1009032846673663263140533)
                ·
                  refine ⟨94596829375655930919425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1009032846673663263140533 94596829375655930919425)
                  ·
                    rfl

theorem cell22_829020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 2, 2, 2, 2, 5].length) (baseStart_829020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829020 prefixEnd_829020 := by exact prefixLift 829020
  have htrace : WordTrace (prefixWord ++ tailWord_829020) baseStart_829020 baseEnd_829020 := by
    simpa [prefixWord, tailWord_829020, baseEnd_829020] using wordTrace_append hprefix tailTrace_829020
  have hstable : (prefixWord ++ tailWord_829020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829020).length < 2 ^ (prefixWord ++ tailWord_829020).sum := by decide
  have hdescent : baseEnd_829020 < baseStart_829020 := by decide
  rcases family_descends (prefixWord ++ tailWord_829020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829063 : List Nat := [1, 1, 4, 2, 1, 3, 2, 2, 1, 5]
def baseStart_829063 : Nat := 118140960795 + 829063 * 2 ^ 59
def prefixEnd_829063 : Nat := 4983230072969 + 3 ^ 40 * 829063 * 2
def baseEnd_829063 : Nat := 283805207905730013933143

theorem tailTrace_829063 : CollatzResearch.WordTrace tailWord_829063 prefixEnd_829063 283805207905730013933143 := by
  unfold tailWord_829063
  simp only [CollatzResearch.WordTrace]
  refine ⟨30238411795453818532739843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20158941196969212355159895 30238411795453818532739843)
  ·
    refine ⟨45357617693180727799109765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30238411795453818532739843 45357617693180727799109765)
    ·
      refine ⟨8504553317471386462333081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45357617693180727799109765 8504553317471386462333081)
      ·
        refine ⟨6378414988103539846749811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8504553317471386462333081 6378414988103539846749811)
        ·
          refine ⟨9567622482155309770124717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6378414988103539846749811 9567622482155309770124717)
          ·
            refine ⟨3587858430808241163796769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9567622482155309770124717 3587858430808241163796769)
            ·
              refine ⟨2690893823106180872847577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3587858430808241163796769 2690893823106180872847577)
              ·
                refine ⟨2018170367329635654635683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2690893823106180872847577 2018170367329635654635683)
                ·
                  refine ⟨3027255550994453481953525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2018170367329635654635683 3027255550994453481953525)
                  ·
                    refine ⟨283805207905730013933143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3027255550994453481953525 283805207905730013933143)
                    ·
                      rfl

theorem cell22_829063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_829063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829063 prefixEnd_829063 := by exact prefixLift 829063
  have htrace : WordTrace (prefixWord ++ tailWord_829063) baseStart_829063 baseEnd_829063 := by
    simpa [prefixWord, tailWord_829063, baseEnd_829063] using wordTrace_append hprefix tailTrace_829063
  have hstable : (prefixWord ++ tailWord_829063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829063).length < 2 ^ (prefixWord ++ tailWord_829063).sum := by decide
  have hdescent : baseEnd_829063 < baseStart_829063 := by decide
  rcases family_descends (prefixWord ++ tailWord_829063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829080 : List Nat := [2, 1, 2, 4, 1, 3, 1, 1, 4, 3]
def baseStart_829080 : Nat := 118140960795 + 829080 * 2 ^ 59
def prefixEnd_829080 : Nat := 4983230072969 + 3 ^ 40 * 829080 * 2
def baseEnd_829080 : Nat := 283811027353147636258091

theorem tailTrace_829080 : CollatzResearch.WordTrace tailWord_829080 prefixEnd_829080 283811027353147636258091 := by
  unfold tailWord_829080
  simp only [CollatzResearch.WordTrace]
  refine ⟨15119515918196115218054347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20159354557594820290739129 15119515918196115218054347)
  ·
    refine ⟨22679273877294172827081521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15119515918196115218054347 22679273877294172827081521)
    ·
      refine ⟨17009455407970629620311141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22679273877294172827081521 17009455407970629620311141)
      ·
        refine ⟨3189272888994493053808339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17009455407970629620311141 3189272888994493053808339)
        ·
          refine ⟨4783909333491739580712509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3189272888994493053808339 4783909333491739580712509)
          ·
            refine ⟨1793966000059402342767191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4783909333491739580712509 1793966000059402342767191)
            ·
              refine ⟨2690949000089103514150787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1793966000059402342767191 2690949000089103514150787)
              ·
                refine ⟨4036423500133655271226181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2690949000089103514150787 4036423500133655271226181)
                ·
                  refine ⟨756829406275060363354909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4036423500133655271226181 756829406275060363354909)
                  ·
                    refine ⟨283811027353147636258091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 756829406275060363354909 283811027353147636258091)
                    ·
                      rfl

theorem cell22_829080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 3, 1, 1, 4, 3].length) (baseStart_829080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829080 prefixEnd_829080 := by exact prefixLift 829080
  have htrace : WordTrace (prefixWord ++ tailWord_829080) baseStart_829080 baseEnd_829080 := by
    simpa [prefixWord, tailWord_829080, baseEnd_829080] using wordTrace_append hprefix tailTrace_829080
  have hstable : (prefixWord ++ tailWord_829080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829080).length < 2 ^ (prefixWord ++ tailWord_829080).sum := by decide
  have hdescent : baseEnd_829080 < baseStart_829080 := by decide
  rcases family_descends (prefixWord ++ tailWord_829080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829148 : List Nat := [2, 2, 5, 1, 3, 1, 2, 1, 2, 3]
def baseStart_829148 : Nat := 118140960795 + 829148 * 2 ^ 59
def prefixEnd_829148 : Nat := 4983230072969 + 3 ^ 40 * 829148 * 2
def baseEnd_829148 : Nat := 283834305142818125557883

theorem tailTrace_829148 : CollatzResearch.WordTrace tailWord_829148 prefixEnd_829148 283834305142818125557883 := by
  unfold tailWord_829148
  simp only [CollatzResearch.WordTrace]
  refine ⟨15120756000072939024792049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20161008000097252033056065 15120756000072939024792049)
  ·
    refine ⟨11340567000054704268594037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15120756000072939024792049 11340567000054704268594037)
    ·
      refine ⟨1063178156255128525180691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11340567000054704268594037 1063178156255128525180691)
      ·
        refine ⟨1594767234382692787771037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1063178156255128525180691 1594767234382692787771037)
        ·
          refine ⟨598037712893509795414139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1594767234382692787771037 598037712893509795414139)
          ·
            refine ⟨897056569340264693121209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598037712893509795414139 897056569340264693121209)
            ·
              refine ⟨672792427005198519840907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 897056569340264693121209 672792427005198519840907)
              ·
                refine ⟨1009188640507797779761361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672792427005198519840907 1009188640507797779761361)
                ·
                  refine ⟨756891480380848334821021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1009188640507797779761361 756891480380848334821021)
                  ·
                    refine ⟨283834305142818125557883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 756891480380848334821021 283834305142818125557883)
                    ·
                      rfl

theorem cell22_829148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 3, 1, 2, 1, 2, 3].length) (baseStart_829148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829148 prefixEnd_829148 := by exact prefixLift 829148
  have htrace : WordTrace (prefixWord ++ tailWord_829148) baseStart_829148 baseEnd_829148 := by
    simpa [prefixWord, tailWord_829148, baseEnd_829148] using wordTrace_append hprefix tailTrace_829148
  have hstable : (prefixWord ++ tailWord_829148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829148).length < 2 ^ (prefixWord ++ tailWord_829148).sum := by decide
  have hdescent : baseEnd_829148 < baseStart_829148 := by decide
  rcases family_descends (prefixWord ++ tailWord_829148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829185 : List Nat := [1, 2, 4, 1, 1, 1, 2, 5, 1, 4]
def baseStart_829185 : Nat := 118140960795 + 829185 * 2 ^ 59
def prefixEnd_829185 : Nat := 4983230072969 + 3 ^ 40 * 829185 * 2
def baseEnd_829185 : Nat := 283846970998962362382769

theorem tailTrace_829185 : CollatzResearch.WordTrace tailWord_829185 prefixEnd_829185 283846970998962362382769 := by
  unfold tailWord_829185
  simp only [CollatzResearch.WordTrace]
  refine ⟨30242861501011833368681009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20161907667341222245787339 30242861501011833368681009)
  ·
    refine ⟨22682146125758875026510757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30242861501011833368681009 22682146125758875026510757)
    ·
      refine ⟨4252902398579789067470767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22682146125758875026510757 4252902398579789067470767)
      ·
        refine ⟨6379353597869683601206151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4252902398579789067470767 6379353597869683601206151)
        ·
          refine ⟨9569030396804525401809227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6379353597869683601206151 9569030396804525401809227)
          ·
            refine ⟨14353545595206788102713841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9569030396804525401809227 14353545595206788102713841)
            ·
              refine ⟨10765159196405091077035381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14353545595206788102713841 10765159196405091077035381)
              ·
                refine ⟨1009233674662977288472067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10765159196405091077035381 1009233674662977288472067)
                ·
                  refine ⟨1513850511994465932708101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1009233674662977288472067 1513850511994465932708101)
                  ·
                    refine ⟨283846970998962362382769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1513850511994465932708101 283846970998962362382769)
                    ·
                      rfl

theorem cell22_829185_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_829185 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829185 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829185 prefixEnd_829185 := by exact prefixLift 829185
  have htrace : WordTrace (prefixWord ++ tailWord_829185) baseStart_829185 baseEnd_829185 := by
    simpa [prefixWord, tailWord_829185, baseEnd_829185] using wordTrace_append hprefix tailTrace_829185
  have hstable : (prefixWord ++ tailWord_829185).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829185).length < 2 ^ (prefixWord ++ tailWord_829185).sum := by decide
  have hdescent : baseEnd_829185 < baseStart_829185 := by decide
  rcases family_descends (prefixWord ++ tailWord_829185) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829202 : List Nat := [3, 2, 4, 1, 1, 1, 1, 2, 3, 4]
def baseStart_829202 : Nat := 118140960795 + 829202 * 2 ^ 59
def prefixEnd_829202 : Nat := 4983230072969 + 3 ^ 40 * 829202 * 2
def baseEnd_829202 : Nat := 283852790446379984707717

theorem tailTrace_829202 : CollatzResearch.WordTrace tailWord_829202 prefixEnd_829202 283852790446379984707717 := by
  unfold tailWord_829202
  simp only [CollatzResearch.WordTrace]
  refine ⟨7560870385487561318012465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20162321027966830181366573 7560870385487561318012465)
  ·
    refine ⟨5670652789115670988509349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7560870385487561318012465 5670652789115670988509349)
    ·
      refine ⟨1063247397959188310345503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5670652789115670988509349 1063247397959188310345503)
      ·
        refine ⟨1594871096938782465518255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1063247397959188310345503 1594871096938782465518255)
        ·
          refine ⟨2392306645408173698277383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1594871096938782465518255 2392306645408173698277383)
          ·
            refine ⟨3588459968112260547416075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2392306645408173698277383 3588459968112260547416075)
            ·
              refine ⟨5382689952168390821124113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3588459968112260547416075 5382689952168390821124113)
              ·
                refine ⟨4037017464126293115843085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5382689952168390821124113 4037017464126293115843085)
                ·
                  refine ⟨1513881549047359918441157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4037017464126293115843085 1513881549047359918441157)
                  ·
                    refine ⟨283852790446379984707717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1513881549047359918441157 283852790446379984707717)
                    ·
                      rfl

theorem cell22_829202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 1, 2, 3, 4].length) (baseStart_829202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829202 prefixEnd_829202 := by exact prefixLift 829202
  have htrace : WordTrace (prefixWord ++ tailWord_829202) baseStart_829202 baseEnd_829202 := by
    simpa [prefixWord, tailWord_829202, baseEnd_829202] using wordTrace_append hprefix tailTrace_829202
  have hstable : (prefixWord ++ tailWord_829202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829202).length < 2 ^ (prefixWord ++ tailWord_829202).sum := by decide
  have hdescent : baseEnd_829202 < baseStart_829202 := by decide
  rcases family_descends (prefixWord ++ tailWord_829202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829215 : List Nat := [1, 1, 2, 4, 2, 1, 4, 1, 1, 5]
def baseStart_829215 : Nat := 118140960795 + 829215 * 2 ^ 59
def prefixEnd_829215 : Nat := 4983230072969 + 3 ^ 40 * 829215 * 2
def baseEnd_829215 : Nat := 283857240612052284132677

theorem tailTrace_829215 : CollatzResearch.WordTrace tailWord_829215 prefixEnd_829215 283857240612052284132677 := by
  unfold tailWord_829215
  simp only [CollatzResearch.WordTrace]
  refine ⟨30243955690903148492273099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20162637127268765661515399 30243955690903148492273099)
  ·
    refine ⟨45365933536354722738409649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30243955690903148492273099 45365933536354722738409649)
    ·
      refine ⟨34024450152266042053807237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45365933536354722738409649 34024450152266042053807237)
      ·
        refine ⟨6379584403549882885088857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34024450152266042053807237 6379584403549882885088857)
        ·
          refine ⟨4784688302662412163816643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6379584403549882885088857 4784688302662412163816643)
          ·
            refine ⟨7177032453993618245724965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4784688302662412163816643 7177032453993618245724965)
            ·
              refine ⟨1345693585123803421073431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7177032453993618245724965 1345693585123803421073431)
              ·
                refine ⟨2018540377685705131610147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1345693585123803421073431 2018540377685705131610147)
                ·
                  refine ⟨3027810566528557697415221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2018540377685705131610147 3027810566528557697415221)
                  ·
                    refine ⟨283857240612052284132677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3027810566528557697415221 283857240612052284132677)
                    ·
                      rfl

theorem cell22_829215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 4, 1, 1, 5].length) (baseStart_829215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829215 prefixEnd_829215 := by exact prefixLift 829215
  have htrace : WordTrace (prefixWord ++ tailWord_829215) baseStart_829215 baseEnd_829215 := by
    simpa [prefixWord, tailWord_829215, baseEnd_829215] using wordTrace_append hprefix tailTrace_829215
  have hstable : (prefixWord ++ tailWord_829215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829215).length < 2 ^ (prefixWord ++ tailWord_829215).sum := by decide
  have hdescent : baseEnd_829215 < baseStart_829215 := by decide
  rcases family_descends (prefixWord ++ tailWord_829215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829236 : List Nat := [2, 5, 1, 1, 2, 3, 2, 1, 1, 4]
def baseStart_829236 : Nat := 118140960795 + 829236 * 2 ^ 59
def prefixEnd_829236 : Nat := 4983230072969 + 3 ^ 40 * 829236 * 2
def baseEnd_829236 : Nat := 283864429341215229357613

theorem tailTrace_829236 : CollatzResearch.WordTrace tailWord_829236 prefixEnd_829236 283864429341215229357613 := by
  unfold tailWord_829236
  simp only [CollatzResearch.WordTrace]
  refine ⟨15122360811913534539393781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20163147749218046052525041 15122360811913534539393781)
  ·
    refine ⟨1417721326116893863068167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15122360811913534539393781 1417721326116893863068167)
    ·
      refine ⟨2126581989175340794602251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1417721326116893863068167 2126581989175340794602251)
      ·
        refine ⟨3189872983763011191903377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2126581989175340794602251 3189872983763011191903377)
        ·
          refine ⟨2392404737822258393927533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3189872983763011191903377 2392404737822258393927533)
          ·
            refine ⟨897151776683346897722825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2392404737822258393927533 897151776683346897722825)
            ·
              refine ⟨672863832512510173292119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 897151776683346897722825 672863832512510173292119)
              ·
                refine ⟨1009295748768765259938179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672863832512510173292119 1009295748768765259938179)
                ·
                  refine ⟨1513943623153147889907269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1009295748768765259938179 1513943623153147889907269)
                  ·
                    refine ⟨283864429341215229357613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1513943623153147889907269 283864429341215229357613)
                    ·
                      rfl

theorem cell22_829236_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_829236 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829236 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829236 prefixEnd_829236 := by exact prefixLift 829236
  have htrace : WordTrace (prefixWord ++ tailWord_829236) baseStart_829236 baseEnd_829236 := by
    simpa [prefixWord, tailWord_829236, baseEnd_829236] using wordTrace_append hprefix tailTrace_829236
  have hstable : (prefixWord ++ tailWord_829236).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829236).length < 2 ^ (prefixWord ++ tailWord_829236).sum := by decide
  have hdescent : baseEnd_829236 < baseStart_829236 := by decide
  rcases family_descends (prefixWord ++ tailWord_829236) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829245 : List Nat := [1, 4, 1, 4, 1, 2, 9]
def baseStart_829245 : Nat := 118140960795 + 829245 * 2 ^ 59
def prefixEnd_829245 : Nat := 4983230072969 + 3 ^ 40 * 829245 * 2
def baseEnd_829245 : Nat := 10513611489820081699355

theorem tailTrace_829245 : CollatzResearch.WordTrace tailWord_829245 prefixEnd_829245 10513611489820081699355 := by
  unfold tailWord_829245
  simp only [CollatzResearch.WordTrace]
  refine ⟨30245049880794463615865189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20163366587196309077243459 30245049880794463615865189)
  ·
    refine ⟨5670946852648961927974723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30245049880794463615865189 5670946852648961927974723)
    ·
      refine ⟨8506420278973442891962085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5670946852648961927974723 8506420278973442891962085)
      ·
        refine ⟨1594953802307520542242891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8506420278973442891962085 1594953802307520542242891)
        ·
          refine ⟨2392430703461280813364337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1594953802307520542242891 2392430703461280813364337)
          ·
            refine ⟨1794323027595960610023253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2392430703461280813364337 1794323027595960610023253)
            ·
              refine ⟨10513611489820081699355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1794323027595960610023253 10513611489820081699355)
              ·
                rfl

theorem cell22_829245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 9].length) (baseStart_829245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829245 prefixEnd_829245 := by exact prefixLift 829245
  have htrace : WordTrace (prefixWord ++ tailWord_829245) baseStart_829245 baseEnd_829245 := by
    simpa [prefixWord, tailWord_829245, baseEnd_829245] using wordTrace_append hprefix tailTrace_829245
  have hstable : (prefixWord ++ tailWord_829245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829245).length < 2 ^ (prefixWord ++ tailWord_829245).sum := by decide
  have hdescent : baseEnd_829245 < baseStart_829245 := by decide
  rcases family_descends (prefixWord ++ tailWord_829245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829337 : List Nat := [1, 2, 1, 2, 1, 3, 5, 2, 1, 4]
def baseStart_829337 : Nat := 118140960795 + 829337 * 2 ^ 59
def prefixEnd_829337 : Nat := 4983230072969 + 3 ^ 40 * 829337 * 2
def baseEnd_829337 : Nat := 283899003705284632582303

theorem tailTrace_829337 : CollatzResearch.WordTrace tailWord_829337 prefixEnd_829337 283899003705284632582303 := by
  unfold tailWord_829337
  simp only [CollatzResearch.WordTrace]
  refine ⟨30248405396461163328214265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20165603597640775552142843 30248405396461163328214265)
  ·
    refine ⟨22686304047345872496160699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30248405396461163328214265 22686304047345872496160699)
    ·
      refine ⟨34029456071018808744241049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22686304047345872496160699 34029456071018808744241049)
      ·
        refine ⟨25522092053264106558180787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34029456071018808744241049 25522092053264106558180787)
        ·
          refine ⟨38283138079896159837271181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25522092053264106558180787 38283138079896159837271181)
          ·
            refine ⟨14356176779961059938976693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38283138079896159837271181 14356176779961059938976693)
            ·
              refine ⟨1345891573121349369279065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14356176779961059938976693 1345891573121349369279065)
              ·
                refine ⟨1009418679841012026959299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1345891573121349369279065 1009418679841012026959299)
                ·
                  refine ⟨1514128019761518040438949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1009418679841012026959299 1514128019761518040438949)
                  ·
                    refine ⟨283899003705284632582303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1514128019761518040438949 283899003705284632582303)
                    ·
                      rfl

theorem cell22_829337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 3, 5, 2, 1, 4].length) (baseStart_829337 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829337 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829337 prefixEnd_829337 := by exact prefixLift 829337
  have htrace : WordTrace (prefixWord ++ tailWord_829337) baseStart_829337 baseEnd_829337 := by
    simpa [prefixWord, tailWord_829337, baseEnd_829337] using wordTrace_append hprefix tailTrace_829337
  have hstable : (prefixWord ++ tailWord_829337).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829337).length < 2 ^ (prefixWord ++ tailWord_829337).sum := by decide
  have hdescent : baseEnd_829337 < baseStart_829337 := by decide
  rcases family_descends (prefixWord ++ tailWord_829337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829358 : List Nat := [4, 1, 5, 1, 1, 1, 2, 2, 5]
def baseStart_829358 : Nat := 118140960795 + 829358 * 2 ^ 59
def prefixEnd_829358 : Nat := 4983230072969 + 3 ^ 40 * 829358 * 2
def baseEnd_829358 : Nat := 94635397478149192602413

theorem tailTrace_829358 : CollatzResearch.WordTrace tailWord_829358 prefixEnd_829358 94635397478149192602413 := by
  unfold tailWord_829358
  simp only [CollatzResearch.WordTrace]
  refine ⟨3781146416173135489341091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20166114219590055943152485 3781146416173135489341091)
  ·
    refine ⟨5671719624259703234011637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3781146416173135489341091 5671719624259703234011637)
    ·
      refine ⟨531723714774347178188591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 5671719624259703234011637 531723714774347178188591)
      ·
        refine ⟨797585572161520767282887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531723714774347178188591 797585572161520767282887)
        ·
          refine ⟨1196378358242281150924331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 797585572161520767282887 1196378358242281150924331)
          ·
            refine ⟨1794567537363421726386497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1196378358242281150924331 1794567537363421726386497)
            ·
              refine ⟨1345925653022566294789873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1794567537363421726386497 1345925653022566294789873)
              ·
                refine ⟨1009444239766924721092405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1345925653022566294789873 1009444239766924721092405)
                ·
                  refine ⟨94635397478149192602413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1009444239766924721092405 94635397478149192602413)
                  ·
                    rfl

theorem cell22_829358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 5, 1, 1, 1, 2, 2, 5].length) (baseStart_829358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829358 prefixEnd_829358 := by exact prefixLift 829358
  have htrace : WordTrace (prefixWord ++ tailWord_829358) baseStart_829358 baseEnd_829358 := by
    simpa [prefixWord, tailWord_829358, baseEnd_829358] using wordTrace_append hprefix tailTrace_829358
  have hstable : (prefixWord ++ tailWord_829358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829358).length < 2 ^ (prefixWord ++ tailWord_829358).sum := by decide
  have hdescent : baseEnd_829358 < baseStart_829358 := by decide
  rcases family_descends (prefixWord ++ tailWord_829358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829384 : List Nat := [2, 1, 3, 1, 4, 1, 2, 3, 2, 3]
def baseStart_829384 : Nat := 118140960795 + 829384 * 2 ^ 59
def prefixEnd_829384 : Nat := 4983230072969 + 3 ^ 40 * 829384 * 2
def baseEnd_829384 : Nat := 283915092765792176657159

theorem tailTrace_829384 : CollatzResearch.WordTrace tailWord_829384 prefixEnd_829384 283915092765792176657159 := by
  unfold tailWord_829384
  simp only [CollatzResearch.WordTrace]
  refine ⟨15125059813645445177587603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20166746418193926903450137 15125059813645445177587603)
  ·
    refine ⟨22687589720468167766381405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15125059813645445177587603 22687589720468167766381405)
    ·
      refine ⟨8507846145175562912393027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22687589720468167766381405 8507846145175562912393027)
      ·
        refine ⟨12761769217763344368589541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8507846145175562912393027 12761769217763344368589541)
        ·
          refine ⟨2392831728330627069110539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12761769217763344368589541 2392831728330627069110539)
          ·
            refine ⟨3589247592495940603665809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2392831728330627069110539 3589247592495940603665809)
            ·
              refine ⟨2691935694371955452749357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3589247592495940603665809 2691935694371955452749357)
              ·
                refine ⟨1009475885389483294781009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2691935694371955452749357 1009475885389483294781009)
                ·
                  refine ⟨757106914042112471085757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1009475885389483294781009 757106914042112471085757)
                  ·
                    refine ⟨283915092765792176657159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 757106914042112471085757 283915092765792176657159)
                    ·
                      rfl

theorem cell22_829384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 1, 2, 3, 2, 3].length) (baseStart_829384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829384 prefixEnd_829384 := by exact prefixLift 829384
  have htrace : WordTrace (prefixWord ++ tailWord_829384) baseStart_829384 baseEnd_829384 := by
    simpa [prefixWord, tailWord_829384, baseEnd_829384] using wordTrace_append hprefix tailTrace_829384
  have hstable : (prefixWord ++ tailWord_829384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829384).length < 2 ^ (prefixWord ++ tailWord_829384).sum := by decide
  have hdescent : baseEnd_829384 < baseStart_829384 := by decide
  rcases family_descends (prefixWord ++ tailWord_829384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829412 : List Nat := [2, 3, 1, 1, 1, 1, 3, 2, 5, 3]
def baseStart_829412 : Nat := 118140960795 + 829412 * 2 ^ 59
def prefixEnd_829412 : Nat := 4983230072969 + 3 ^ 40 * 829412 * 2
def baseEnd_829412 : Nat := 283924677738009436957073

theorem tailTrace_829412 : CollatzResearch.WordTrace tailWord_829412 prefixEnd_829412 283924677738009436957073 := by
  unfold tailWord_829412
  simp only [CollatzResearch.WordTrace]
  refine ⟨15125570435594725568597245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20167427247459634091462993 15125570435594725568597245)
  ·
    refine ⟨5672088913348022088223967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15125570435594725568597245 5672088913348022088223967)
    ·
      refine ⟨8508133370022033132335951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5672088913348022088223967 8508133370022033132335951)
      ·
        refine ⟨12762200055033049698503927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8508133370022033132335951 12762200055033049698503927)
        ·
          refine ⟨19143300082549574547755891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12762200055033049698503927 19143300082549574547755891)
          ·
            refine ⟨28714950123824361821633837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19143300082549574547755891 28714950123824361821633837)
            ·
              refine ⟨10768106296434135683112689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28714950123824361821633837 10768106296434135683112689)
              ·
                refine ⟨8076079722325601762334517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10768106296434135683112689 8076079722325601762334517)
                ·
                  refine ⟨757132473968025165218861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8076079722325601762334517 757132473968025165218861)
                  ·
                    refine ⟨283924677738009436957073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 757132473968025165218861 283924677738009436957073)
                    ·
                      rfl

theorem cell22_829412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 3, 2, 5, 3].length) (baseStart_829412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829412 prefixEnd_829412 := by exact prefixLift 829412
  have htrace : WordTrace (prefixWord ++ tailWord_829412) baseStart_829412 baseEnd_829412 := by
    simpa [prefixWord, tailWord_829412, baseEnd_829412] using wordTrace_append hprefix tailTrace_829412
  have hstable : (prefixWord ++ tailWord_829412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829412).length < 2 ^ (prefixWord ++ tailWord_829412).sum := by decide
  have hdescent : baseEnd_829412 < baseStart_829412 := by decide
  rcases family_descends (prefixWord ++ tailWord_829412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829440 : List Nat := [2, 1, 1, 2, 1, 1, 1, 5, 1, 7]
def baseStart_829440 : Nat := 118140960795 + 829440 * 2 ^ 59
def prefixEnd_829440 : Nat := 4983230072969 + 3 ^ 40 * 829440 * 2
def baseEnd_829440 : Nat := 283934262710226697256987

theorem tailTrace_829440 : CollatzResearch.WordTrace tailWord_829440 prefixEnd_829440 283934262710226697256987 := by
  unfold tailWord_829440
  simp only [CollatzResearch.WordTrace]
  refine ⟨15126081057544005959606887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20168108076725341279475849 15126081057544005959606887)
  ·
    refine ⟨22689121586316008939410331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15126081057544005959606887 22689121586316008939410331)
    ·
      refine ⟨34033682379474013409115497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22689121586316008939410331 34033682379474013409115497)
      ·
        refine ⟨25525261784605510056836623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34033682379474013409115497 25525261784605510056836623)
        ·
          refine ⟨38287892676908265085254935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25525261784605510056836623 38287892676908265085254935)
          ·
            refine ⟨57431839015362397627882403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38287892676908265085254935 57431839015362397627882403)
            ·
              refine ⟨86147758523043596441823605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57431839015362397627882403 86147758523043596441823605)
              ·
                refine ⟨8076352361535337166420963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86147758523043596441823605 8076352361535337166420963)
                ·
                  refine ⟨12114528542303005749631445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8076352361535337166420963 12114528542303005749631445)
                  ·
                    refine ⟨283934262710226697256987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12114528542303005749631445 283934262710226697256987)
                    ·
                      rfl

theorem cell22_829440_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 5, 1, 7].length) (baseStart_829440 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829440 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829440 prefixEnd_829440 := by exact prefixLift 829440
  have htrace : WordTrace (prefixWord ++ tailWord_829440) baseStart_829440 baseEnd_829440 := by
    simpa [prefixWord, tailWord_829440, baseEnd_829440] using wordTrace_append hprefix tailTrace_829440
  have hstable : (prefixWord ++ tailWord_829440).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829440).length < 2 ^ (prefixWord ++ tailWord_829440).sum := by decide
  have hdescent : baseEnd_829440 < baseStart_829440 := by decide
  rcases family_descends (prefixWord ++ tailWord_829440) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829480 : List Nat := [2, 1, 5, 3, 2, 1, 1, 1, 3, 3]
def baseStart_829480 : Nat := 118140960795 + 829480 * 2 ^ 59
def prefixEnd_829480 : Nat := 4983230072969 + 3 ^ 40 * 829480 * 2
def baseEnd_829480 : Nat := 283947955527679926256865

theorem tailTrace_829480 : CollatzResearch.WordTrace tailWord_829480 prefixEnd_829480 283947955527679926256865 := by
  unfold tailWord_829480
  simp only [CollatzResearch.WordTrace]
  refine ⟨15126810517471549375334947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20169080689962065833779929 15126810517471549375334947)
  ·
    refine ⟨22690215776207324063002421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15126810517471549375334947 22690215776207324063002421)
    ·
      refine ⟨2127207729019436630906477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22690215776207324063002421 2127207729019436630906477)
      ·
        refine ⟨797702898382288736589929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2127207729019436630906477 797702898382288736589929)
        ·
          refine ⟨598277173786716552442447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 797702898382288736589929 598277173786716552442447)
          ·
            refine ⟨897415760680074828663671, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598277173786716552442447 897415760680074828663671)
            ·
              refine ⟨1346123641020112242995507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897415760680074828663671 1346123641020112242995507)
              ·
                refine ⟨2019185461530168364493261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1346123641020112242995507 2019185461530168364493261)
                ·
                  refine ⟨757194548073813136684973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2019185461530168364493261 757194548073813136684973)
                  ·
                    refine ⟨283947955527679926256865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 757194548073813136684973 283947955527679926256865)
                    ·
                      rfl

theorem cell22_829480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 2, 1, 1, 1, 3, 3].length) (baseStart_829480 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829480 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829480 prefixEnd_829480 := by exact prefixLift 829480
  have htrace : WordTrace (prefixWord ++ tailWord_829480) baseStart_829480 baseEnd_829480 := by
    simpa [prefixWord, tailWord_829480, baseEnd_829480] using wordTrace_append hprefix tailTrace_829480
  have hstable : (prefixWord ++ tailWord_829480).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829480).length < 2 ^ (prefixWord ++ tailWord_829480).sum := by decide
  have hdescent : baseEnd_829480 < baseStart_829480 := by decide
  rcases family_descends (prefixWord ++ tailWord_829480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829532 : List Nat := [2, 2, 4, 1, 1, 12]
def baseStart_829532 : Nat := 118140960795 + 829532 * 2 ^ 59
def prefixEnd_829532 : Nat := 4983230072969 + 3 ^ 40 * 829532 * 2
def baseEnd_829532 : Nat := 3505750076424310172305

theorem tailTrace_829532 : CollatzResearch.WordTrace tailWord_829532 prefixEnd_829532 3505750076424310172305 := by
  unfold tailWord_829532
  simp only [CollatzResearch.WordTrace]
  refine ⟨15127758815377355815781425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20170345087169807754375233 15127758815377355815781425)
  ·
    refine ⟨11345819111533016861836069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15127758815377355815781425 11345819111533016861836069)
    ·
      refine ⟨2127341083412440661594263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11345819111533016861836069 2127341083412440661594263)
      ·
        refine ⟨3191011625118660992391395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2127341083412440661594263 3191011625118660992391395)
        ·
          refine ⟨4786517437677991488587093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3191011625118660992391395 4786517437677991488587093)
          ·
            refine ⟨3505750076424310172305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 4786517437677991488587093 3505750076424310172305)
            ·
              rfl

theorem cell22_829532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 12].length) (baseStart_829532 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829532 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829532 prefixEnd_829532 := by exact prefixLift 829532
  have htrace : WordTrace (prefixWord ++ tailWord_829532) baseStart_829532 baseEnd_829532 := by
    simpa [prefixWord, tailWord_829532, baseEnd_829532] using wordTrace_append hprefix tailTrace_829532
  have hstable : (prefixWord ++ tailWord_829532).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829532).length < 2 ^ (prefixWord ++ tailWord_829532).sum := by decide
  have hdescent : baseEnd_829532 < baseStart_829532 := by decide
  rcases family_descends (prefixWord ++ tailWord_829532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829536 : List Nat := [2, 1, 1, 3, 2, 4, 2, 2, 2, 3]
def baseStart_829536 : Nat := 118140960795 + 829536 * 2 ^ 59
def prefixEnd_829536 : Nat := 4983230072969 + 3 ^ 40 * 829536 * 2
def baseEnd_829536 : Nat := 283967125472114446856693

theorem tailTrace_829536 : CollatzResearch.WordTrace tailWord_829536 prefixEnd_829536 283967125472114446856693 := by
  unfold tailWord_829536
  simp only [CollatzResearch.WordTrace]
  refine ⟨15127831761370110157354231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20170442348493480209805641 15127831761370110157354231)
  ·
    refine ⟨22691747642055165236031347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15127831761370110157354231 22691747642055165236031347)
    ·
      refine ⟨34037621463082747854047021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22691747642055165236031347 34037621463082747854047021)
      ·
        refine ⟨12764108048656030445267633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34037621463082747854047021 12764108048656030445267633)
        ·
          refine ⟨9573081036492022833950725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12764108048656030445267633 9573081036492022833950725)
          ·
            refine ⟨1794952694342254281365761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9573081036492022833950725 1794952694342254281365761)
            ·
              refine ⟨1346214520756690711024321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1794952694342254281365761 1346214520756690711024321)
              ·
                refine ⟨1009660890567518033268241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1346214520756690711024321 1009660890567518033268241)
                ·
                  refine ⟨757245667925638524951181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1009660890567518033268241 757245667925638524951181)
                  ·
                    refine ⟨283967125472114446856693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 757245667925638524951181 283967125472114446856693)
                    ·
                      rfl

theorem cell22_829536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 4, 2, 2, 2, 3].length) (baseStart_829536 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829536 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829536 prefixEnd_829536 := by exact prefixLift 829536
  have htrace : WordTrace (prefixWord ++ tailWord_829536) baseStart_829536 baseEnd_829536 := by
    simpa [prefixWord, tailWord_829536, baseEnd_829536] using wordTrace_append hprefix tailTrace_829536
  have hstable : (prefixWord ++ tailWord_829536).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829536).length < 2 ^ (prefixWord ++ tailWord_829536).sum := by decide
  have hdescent : baseEnd_829536 < baseStart_829536 := by decide
  rcases family_descends (prefixWord ++ tailWord_829536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829538 : List Nat := [3, 3, 2, 2, 2, 1, 1, 4, 4]
def baseStart_829538 : Nat := 118140960795 + 829538 * 2 ^ 59
def prefixEnd_829538 : Nat := 4983230072969 + 3 ^ 40 * 829538 * 2
def baseEnd_829538 : Nat := 94655936704329036102229

theorem tailTrace_829538 : CollatzResearch.WordTrace tailWord_829538 prefixEnd_829538 94655936704329036102229 := by
  unfold tailWord_829538
  simp only [CollatzResearch.WordTrace]
  refine ⟨7563934117183243664070317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20170490979155316437520845 7563934117183243664070317)
  ·
    refine ⟨2836475293943716374026369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7563934117183243664070317 2836475293943716374026369)
    ·
      refine ⟨2127356470457787280519777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2836475293943716374026369 2127356470457787280519777)
      ·
        refine ⟨1595517352843340460389833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2127356470457787280519777 1595517352843340460389833)
        ·
          refine ⟨1196638014632505345292375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1595517352843340460389833 1196638014632505345292375)
          ·
            refine ⟨1794957021948758017938563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1196638014632505345292375 1794957021948758017938563)
            ·
              refine ⟨2692435532923137026907845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1794957021948758017938563 2692435532923137026907845)
              ·
                refine ⟨504831662423088192545221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2692435532923137026907845 504831662423088192545221)
                ·
                  refine ⟨94655936704329036102229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 504831662423088192545221 94655936704329036102229)
                  ·
                    rfl

theorem cell22_829538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 1, 1, 4, 4].length) (baseStart_829538 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829538 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829538 prefixEnd_829538 := by exact prefixLift 829538
  have htrace : WordTrace (prefixWord ++ tailWord_829538) baseStart_829538 baseEnd_829538 := by
    simpa [prefixWord, tailWord_829538, baseEnd_829538] using wordTrace_append hprefix tailTrace_829538
  have hstable : (prefixWord ++ tailWord_829538).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829538).length < 2 ^ (prefixWord ++ tailWord_829538).sum := by decide
  have hdescent : baseEnd_829538 < baseStart_829538 := by decide
  rcases family_descends (prefixWord ++ tailWord_829538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829564 : List Nat := [2, 2, 2, 1, 1, 4, 1, 1, 5, 3]
def baseStart_829564 : Nat := 118140960795 + 829564 * 2 ^ 59
def prefixEnd_829564 : Nat := 4983230072969 + 3 ^ 40 * 829564 * 2
def baseEnd_829564 : Nat := 283976710444331707156607

theorem tailTrace_829564 : CollatzResearch.WordTrace tailWord_829564 prefixEnd_829564 283976710444331707156607 := by
  unfold tailWord_829564
  simp only [CollatzResearch.WordTrace]
  refine ⟨15128342383319390548363873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20171123177759187397818497 15128342383319390548363873)
  ·
    refine ⟨11346256787489542911272905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15128342383319390548363873 11346256787489542911272905)
    ·
      refine ⟨8509692590617157183454679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11346256787489542911272905 8509692590617157183454679)
      ·
        refine ⟨12764538885925735775182019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8509692590617157183454679 12764538885925735775182019)
        ·
          refine ⟨19146808328888603662773029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12764538885925735775182019 19146808328888603662773029)
          ·
            refine ⟨3590026561666613186769943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19146808328888603662773029 3590026561666613186769943)
            ·
              refine ⟨5385039842499919780154915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3590026561666613186769943 5385039842499919780154915)
              ·
                refine ⟨8077559763749879670232373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5385039842499919780154915 8077559763749879670232373)
                ·
                  refine ⟨757271227851551219084285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8077559763749879670232373 757271227851551219084285)
                  ·
                    refine ⟨283976710444331707156607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 757271227851551219084285 283976710444331707156607)
                    ·
                      rfl

theorem cell22_829564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 1, 1, 5, 3].length) (baseStart_829564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829564 prefixEnd_829564 := by exact prefixLift 829564
  have htrace : WordTrace (prefixWord ++ tailWord_829564) baseStart_829564 baseEnd_829564 := by
    simpa [prefixWord, tailWord_829564, baseEnd_829564] using wordTrace_append hprefix tailTrace_829564
  have hstable : (prefixWord ++ tailWord_829564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829564).length < 2 ^ (prefixWord ++ tailWord_829564).sum := by decide
  have hdescent : baseEnd_829564 < baseStart_829564 := by decide
  rcases family_descends (prefixWord ++ tailWord_829564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829577 : List Nat := [1, 2, 1, 1, 4, 2, 2, 2, 7]
def baseStart_829577 : Nat := 118140960795 + 829577 * 2 ^ 59
def prefixEnd_829577 : Nat := 4983230072969 + 3 ^ 40 * 829577 * 2
def baseEnd_829577 : Nat := 94660386870001335527189

theorem tailTrace_829577 : CollatzResearch.WordTrace tailWord_829577 prefixEnd_829577 94660386870001335527189 := by
  unfold tailWord_829577
  simp only [CollatzResearch.WordTrace]
  refine ⟨30257158915591684316950985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20171439277061122877967323 30257158915591684316950985)
  ·
    refine ⟨22692869186693763237713239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30257158915591684316950985 22692869186693763237713239)
    ·
      refine ⟨34039303780040644856569859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22692869186693763237713239 34039303780040644856569859)
      ·
        refine ⟨51058955670060967284854789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34039303780040644856569859 51058955670060967284854789)
        ·
          refine ⟨9573554188136431365910273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51058955670060967284854789 9573554188136431365910273)
          ·
            refine ⟨7180165641102323524432705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9573554188136431365910273 7180165641102323524432705)
            ·
              refine ⟨5385124230826742643324529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7180165641102323524432705 5385124230826742643324529)
              ·
                refine ⟨4038843173120056982493397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5385124230826742643324529 4038843173120056982493397)
                ·
                  refine ⟨94660386870001335527189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4038843173120056982493397 94660386870001335527189)
                  ·
                    rfl

theorem cell22_829577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 2, 2, 7].length) (baseStart_829577 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829577 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829577 prefixEnd_829577 := by exact prefixLift 829577
  have htrace : WordTrace (prefixWord ++ tailWord_829577) baseStart_829577 baseEnd_829577 := by
    simpa [prefixWord, tailWord_829577, baseEnd_829577] using wordTrace_append hprefix tailTrace_829577
  have hstable : (prefixWord ++ tailWord_829577).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829577).length < 2 ^ (prefixWord ++ tailWord_829577).sum := by decide
  have hdescent : baseEnd_829577 < baseStart_829577 := by decide
  rcases family_descends (prefixWord ++ tailWord_829577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829656 : List Nat := [2, 1, 2, 2, 4, 3, 1, 1, 6]
def baseStart_829656 : Nat := 118140960795 + 829656 * 2 ^ 59
def prefixEnd_829656 : Nat := 4983230072969 + 3 ^ 40 * 829656 * 2
def baseEnd_829656 : Nat := 94669401308158044618775

theorem tailTrace_829656 : CollatzResearch.WordTrace tailWord_829656 prefixEnd_829656 94669401308158044618775 := by
  unfold tailWord_829656
  simp only [CollatzResearch.WordTrace]
  refine ⟨15130020141152740404538411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20173360188203653872717881 15130020141152740404538411)
  ·
    refine ⟨22695030211729110606807617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15130020141152740404538411 22695030211729110606807617)
    ·
      refine ⟨17021272658796832955105713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22695030211729110606807617 17021272658796832955105713)
      ·
        refine ⟨12765954494097624716329285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17021272658796832955105713 12765954494097624716329285)
        ·
          refine ⟨2393616467643304634311741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12765954494097624716329285 2393616467643304634311741)
          ·
            refine ⟨897606175366239237866903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2393616467643304634311741 897606175366239237866903)
            ·
              refine ⟨1346409263049358856800355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897606175366239237866903 1346409263049358856800355)
              ·
                refine ⟨2019613894574038285200533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1346409263049358856800355 2019613894574038285200533)
                ·
                  refine ⟨94669401308158044618775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2019613894574038285200533 94669401308158044618775)
                  ·
                    rfl

theorem cell22_829656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 1, 1, 6].length) (baseStart_829656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829656 prefixEnd_829656 := by exact prefixLift 829656
  have htrace : WordTrace (prefixWord ++ tailWord_829656) baseStart_829656 baseEnd_829656 := by
    simpa [prefixWord, tailWord_829656, baseEnd_829656] using wordTrace_append hprefix tailTrace_829656
  have hstable : (prefixWord ++ tailWord_829656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829656).length < 2 ^ (prefixWord ++ tailWord_829656).sum := by decide
  have hdescent : baseEnd_829656 < baseStart_829656 := by decide
  rcases family_descends (prefixWord ++ tailWord_829656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829686 : List Nat := [5, 1, 1, 1, 1, 1, 3, 3, 2, 4]
def baseStart_829686 : Nat := 118140960795 + 829686 * 2 ^ 59
def prefixEnd_829686 : Nat := 4983230072969 + 3 ^ 40 * 829686 * 2
def baseEnd_829686 : Nat := 284018473537564055606233

theorem tailTrace_829686 : CollatzResearch.WordTrace tailWord_829686 prefixEnd_829686 284018473537564055606233 := by
  unfold tailWord_829686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1891320904512299745791807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20174089648131197288445941 1891320904512299745791807)
  ·
    refine ⟨2836981356768449618687711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1891320904512299745791807 2836981356768449618687711)
    ·
      refine ⟨4255472035152674428031567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2836981356768449618687711 4255472035152674428031567)
      ·
        refine ⟨6383208052729011642047351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4255472035152674428031567 6383208052729011642047351)
        ·
          refine ⟨9574812079093517463071027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6383208052729011642047351 9574812079093517463071027)
          ·
            refine ⟨14362218118640276194606541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9574812079093517463071027 14362218118640276194606541)
            ·
              refine ⟨5385831794490103572977453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14362218118640276194606541 5385831794490103572977453)
              ·
                refine ⟨2019686922933788839866545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5385831794490103572977453 2019686922933788839866545)
                ·
                  refine ⟨1514765192200341629899909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2019686922933788839866545 1514765192200341629899909)
                  ·
                    refine ⟨284018473537564055606233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1514765192200341629899909 284018473537564055606233)
                    ·
                      rfl

theorem cell22_829686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 3, 3, 2, 4].length) (baseStart_829686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829686 prefixEnd_829686 := by exact prefixLift 829686
  have htrace : WordTrace (prefixWord ++ tailWord_829686) baseStart_829686 baseEnd_829686 := by
    simpa [prefixWord, tailWord_829686, baseEnd_829686] using wordTrace_append hprefix tailTrace_829686
  have hstable : (prefixWord ++ tailWord_829686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829686).length < 2 ^ (prefixWord ++ tailWord_829686).sum := by decide
  have hdescent : baseEnd_829686 < baseStart_829686 := by decide
  rcases family_descends (prefixWord ++ tailWord_829686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829733 : List Nat := [1, 3, 1, 2, 5, 1, 1, 2, 3, 3]
def baseStart_829733 : Nat := 118140960795 + 829733 * 2 ^ 59
def prefixEnd_829733 : Nat := 4983230072969 + 3 ^ 40 * 829733 * 2
def baseEnd_829733 : Nat := 284034562598071599681089

theorem tailTrace_829733 : CollatzResearch.WordTrace tailWord_829733 prefixEnd_829733 284034562598071599681089 := by
  unfold tailWord_829733
  simp only [CollatzResearch.WordTrace]
  refine ⟨30262848703026522959629853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20175232468684348639753235 30262848703026522959629853)
  ·
    refine ⟨11348568263634946109861195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30262848703026522959629853 11348568263634946109861195)
    ·
      refine ⟨17022852395452419164791793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11348568263634946109861195 17022852395452419164791793)
      ·
        refine ⟨12767139296589314373593845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17022852395452419164791793 12767139296589314373593845)
        ·
          refine ⟨1196919309055248222524423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12767139296589314373593845 1196919309055248222524423)
          ·
            refine ⟨1795378963582872333786635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1196919309055248222524423 1795378963582872333786635)
            ·
              refine ⟨2693068445374308500679953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1795378963582872333786635 2693068445374308500679953)
              ·
                refine ⟨2019801334030731375509965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2693068445374308500679953 2019801334030731375509965)
                ·
                  refine ⟨757425500261524265816237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2019801334030731375509965 757425500261524265816237)
                  ·
                    refine ⟨284034562598071599681089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 757425500261524265816237 284034562598071599681089)
                    ·
                      rfl

theorem cell22_829733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 1, 1, 2, 3, 3].length) (baseStart_829733 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829733 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829733 prefixEnd_829733 := by exact prefixLift 829733
  have htrace : WordTrace (prefixWord ++ tailWord_829733) baseStart_829733 baseEnd_829733 := by
    simpa [prefixWord, tailWord_829733, baseEnd_829733] using wordTrace_append hprefix tailTrace_829733
  have hstable : (prefixWord ++ tailWord_829733).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829733).length < 2 ^ (prefixWord ++ tailWord_829733).sum := by decide
  have hdescent : baseEnd_829733 < baseStart_829733 := by decide
  rcases family_descends (prefixWord ++ tailWord_829733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829808 : List Nat := [2, 1, 1, 1, 4, 3, 3, 3, 4]
def baseStart_829808 : Nat := 118140960795 + 829808 * 2 ^ 59
def prefixEnd_829808 : Nat := 4983230072969 + 3 ^ 40 * 829808 * 2
def baseEnd_829808 : Nat := 94686745543598801351953

theorem tailTrace_829808 : CollatzResearch.WordTrace tailWord_829808 prefixEnd_829808 94686745543598801351953 := by
  unfold tailWord_829808
  simp only [CollatzResearch.WordTrace]
  refine ⟨15132792088877405384305039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20177056118503207179073385 15132792088877405384305039)
  ·
    refine ⟨22699188133316108076457559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15132792088877405384305039 22699188133316108076457559)
    ·
      refine ⟨34048782199974162114686339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22699188133316108076457559 34048782199974162114686339)
      ·
        refine ⟨51073173299961243172029509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34048782199974162114686339 51073173299961243172029509)
        ·
          refine ⟨9576219993742733094755533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51073173299961243172029509 9576219993742733094755533)
          ·
            refine ⟨3591082497653524910533325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9576219993742733094755533 3591082497653524910533325)
            ·
              refine ⟨1346655936620071841449997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3591082497653524910533325 1346655936620071841449997)
              ·
                refine ⟨504995976232526940543749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1346655936620071841449997 504995976232526940543749)
                ·
                  refine ⟨94686745543598801351953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 504995976232526940543749 94686745543598801351953)
                  ·
                    rfl

theorem cell22_829808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 3, 3, 4].length) (baseStart_829808 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829808 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829808 prefixEnd_829808 := by exact prefixLift 829808
  have htrace : WordTrace (prefixWord ++ tailWord_829808) baseStart_829808 baseEnd_829808 := by
    simpa [prefixWord, tailWord_829808, baseEnd_829808] using wordTrace_append hprefix tailTrace_829808
  have hstable : (prefixWord ++ tailWord_829808).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829808).length < 2 ^ (prefixWord ++ tailWord_829808).sum := by decide
  have hdescent : baseEnd_829808 < baseStart_829808 := by decide
  rcases family_descends (prefixWord ++ tailWord_829808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829819 : List Nat := [1, 1, 1, 1, 1, 7, 10]
def baseStart_829819 : Nat := 118140960795 + 829819 * 2 ^ 59
def prefixEnd_829819 : Nat := 4983230072969 + 3 ^ 40 * 829819 * 2
def baseEnd_829819 : Nat := 10520888968725779334475

theorem tailTrace_829819 : CollatzResearch.WordTrace tailWord_829819 prefixEnd_829819 10520888968725779334475 := by
  unfold tailWord_829819
  simp only [CollatzResearch.WordTrace]
  refine ⟨30265985380714959647260511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20177323587143306431507007 30265985380714959647260511)
  ·
    refine ⟨45398978071072439470890767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30265985380714959647260511 45398978071072439470890767)
    ·
      refine ⟨68098467106608659206336151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45398978071072439470890767 68098467106608659206336151)
      ·
        refine ⟨102147700659912988809504227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68098467106608659206336151 102147700659912988809504227)
        ·
          refine ⟨153221550989869483214256341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102147700659912988809504227 153221550989869483214256341)
          ·
            refine ⟨3591130101325066012834133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 153221550989869483214256341 3591130101325066012834133)
            ·
              refine ⟨10520888968725779334475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 3591130101325066012834133 10520888968725779334475)
              ·
                rfl

theorem cell22_829819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 10].length) (baseStart_829819 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829819 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829819 prefixEnd_829819 := by exact prefixLift 829819
  have htrace : WordTrace (prefixWord ++ tailWord_829819) baseStart_829819 baseEnd_829819 := by
    simpa [prefixWord, tailWord_829819, baseEnd_829819] using wordTrace_append hprefix tailTrace_829819
  have hstable : (prefixWord ++ tailWord_829819).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829819).length < 2 ^ (prefixWord ++ tailWord_829819).sum := by decide
  have hdescent : baseEnd_829819 < baseStart_829819 := by decide
  rcases family_descends (prefixWord ++ tailWord_829819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829821 : List Nat := [1, 4, 1, 1, 2, 3, 1, 1, 4, 4]
def baseStart_829821 : Nat := 118140960795 + 829821 * 2 ^ 59
def prefixEnd_829821 : Nat := 4983230072969 + 3 ^ 40 * 829821 * 2
def baseEnd_829821 : Nat := 284064686796468703480819

theorem tailTrace_829821 : CollatzResearch.WordTrace tailWord_829821 prefixEnd_829821 284064686796468703480819 := by
  unfold tailWord_829821
  simp only [CollatzResearch.WordTrace]
  refine ⟨30266058326707713988833317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20177372217805142659222211 30266058326707713988833317)
  ·
    refine ⟨5674885936257696372906247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30266058326707713988833317 5674885936257696372906247)
    ·
      refine ⟨8512328904386544559359371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5674885936257696372906247 8512328904386544559359371)
      ·
        refine ⟨12768493356579816839039057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8512328904386544559359371 12768493356579816839039057)
        ·
          refine ⟨9576370017434862629279293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12768493356579816839039057 9576370017434862629279293)
          ·
            refine ⟨3591138756538073485979735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9576370017434862629279293 3591138756538073485979735)
            ·
              refine ⟨5386708134807110228969603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3591138756538073485979735 5386708134807110228969603)
              ·
                refine ⟨8080062202210665343454405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5386708134807110228969603 8080062202210665343454405)
                ·
                  refine ⟨1515011662914499751897701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8080062202210665343454405 1515011662914499751897701)
                  ·
                    refine ⟨284064686796468703480819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1515011662914499751897701 284064686796468703480819)
                    ·
                      rfl

theorem cell22_829821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 1, 1, 4, 4].length) (baseStart_829821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829821 prefixEnd_829821 := by exact prefixLift 829821
  have htrace : WordTrace (prefixWord ++ tailWord_829821) baseStart_829821 baseEnd_829821 := by
    simpa [prefixWord, tailWord_829821, baseEnd_829821] using wordTrace_append hprefix tailTrace_829821
  have hstable : (prefixWord ++ tailWord_829821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829821).length < 2 ^ (prefixWord ++ tailWord_829821).sum := by decide
  have hdescent : baseEnd_829821 < baseStart_829821 := by decide
  rcases family_descends (prefixWord ++ tailWord_829821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829836 : List Nat := [2, 2, 1, 2, 1, 5, 2, 7]
def baseStart_829836 : Nat := 118140960795 + 829836 * 2 ^ 59
def prefixEnd_829836 : Nat := 4983230072969 + 3 ^ 40 * 829836 * 2
def baseEnd_829836 : Nat := 31563313511445962706197

theorem tailTrace_829836 : CollatzResearch.WordTrace tailWord_829836 prefixEnd_829836 31563313511445962706197 := by
  unfold tailWord_829836
  simp only [CollatzResearch.WordTrace]
  refine ⟨15133302710826685775314681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20177736947768914367086241 15133302710826685775314681)
  ·
    refine ⟨11349977033120014331486011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15133302710826685775314681 11349977033120014331486011)
    ·
      refine ⟨17024965549680021497229017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11349977033120014331486011 17024965549680021497229017)
      ·
        refine ⟨12768724162260016122921763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17024965549680021497229017 12768724162260016122921763)
        ·
          refine ⟨19153086243390024184382645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12768724162260016122921763 19153086243390024184382645)
          ·
            refine ⟨1795601835317814767285873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19153086243390024184382645 1795601835317814767285873)
            ·
              refine ⟨1346701376488361075464405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1795601835317814767285873 1346701376488361075464405)
              ·
                refine ⟨31563313511445962706197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1346701376488361075464405 31563313511445962706197)
                ·
                  rfl

theorem cell22_829836_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 5, 2, 7].length) (baseStart_829836 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829836 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829836 prefixEnd_829836 := by exact prefixLift 829836
  have htrace : WordTrace (prefixWord ++ tailWord_829836) baseStart_829836 baseEnd_829836 := by
    simpa [prefixWord, tailWord_829836, baseEnd_829836] using wordTrace_append hprefix tailTrace_829836
  have hstable : (prefixWord ++ tailWord_829836).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829836).length < 2 ^ (prefixWord ++ tailWord_829836).sum := by decide
  have hdescent : baseEnd_829836 < baseStart_829836 := by decide
  rcases family_descends (prefixWord ++ tailWord_829836) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829876 : List Nat := [2, 5, 2, 2, 1, 2, 2, 2, 4]
def baseStart_829876 : Nat := 118140960795 + 829876 * 2 ^ 59
def prefixEnd_829876 : Nat := 4983230072969 + 3 ^ 40 * 829876 * 2
def baseEnd_829876 : Nat := 94694504806822297785217

theorem tailTrace_829876 : CollatzResearch.WordTrace tailWord_829876 prefixEnd_829876 94694504806822297785217 := by
  unfold tailWord_829876
  simp only [CollatzResearch.WordTrace]
  refine ⟨15134032170754229191042741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20178709561005638921390321 15134032170754229191042741)
  ·
    refine ⟨1418815516008208986660257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15134032170754229191042741 1418815516008208986660257)
    ·
      refine ⟨1064111637006156739995193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1418815516008208986660257 1064111637006156739995193)
      ·
        refine ⟨798083727754617554996395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1064111637006156739995193 798083727754617554996395)
        ·
          refine ⟨1197125591631926332494593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798083727754617554996395 1197125591631926332494593)
          ·
            refine ⟨897844193723944749370945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1197125591631926332494593 897844193723944749370945)
            ·
              refine ⟨673383145292958562028209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 897844193723944749370945 673383145292958562028209)
              ·
                refine ⟨505037358969718921521157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 673383145292958562028209 505037358969718921521157)
                ·
                  refine ⟨94694504806822297785217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 505037358969718921521157 94694504806822297785217)
                  ·
                    rfl

theorem cell22_829876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 2, 2, 2, 4].length) (baseStart_829876 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829876 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829876 prefixEnd_829876 := by exact prefixLift 829876
  have htrace : WordTrace (prefixWord ++ tailWord_829876) baseStart_829876 baseEnd_829876 := by
    simpa [prefixWord, tailWord_829876, baseEnd_829876] using wordTrace_append hprefix tailTrace_829876
  have hstable : (prefixWord ++ tailWord_829876).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829876).length < 2 ^ (prefixWord ++ tailWord_829876).sum := by decide
  have hdescent : baseEnd_829876 < baseStart_829876 := by decide
  rcases family_descends (prefixWord ++ tailWord_829876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829896 : List Nat := [2, 1, 3, 1, 3, 2, 1, 1, 1, 7]
def baseStart_829896 : Nat := 118140960795 + 829896 * 2 ^ 59
def prefixEnd_829896 : Nat := 4983230072969 + 3 ^ 40 * 829896 * 2
def baseEnd_829896 : Nat := 284090360829193507855589

theorem tailTrace_829896 : CollatzResearch.WordTrace tailWord_829896 prefixEnd_829896 284090360829193507855589 := by
  unfold tailWord_829896
  simp only [CollatzResearch.WordTrace]
  refine ⟨15134396900718000898906771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20179195867624001198542361 15134396900718000898906771)
  ·
    refine ⟨22701595351077001348360157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15134396900718000898906771 22701595351077001348360157)
    ·
      refine ⟨8513098256653875505635059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22701595351077001348360157 8513098256653875505635059)
      ·
        refine ⟨12769647384980813258452589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8513098256653875505635059 12769647384980813258452589)
        ·
          refine ⟨4788617769367804971919721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12769647384980813258452589 4788617769367804971919721)
          ·
            refine ⟨3591463327025853728939791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4788617769367804971919721 3591463327025853728939791)
            ·
              refine ⟨5387194990538780593409687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3591463327025853728939791 5387194990538780593409687)
              ·
                refine ⟨8080792485808170890114531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5387194990538780593409687 8080792485808170890114531)
                ·
                  refine ⟨12121188728712256335171797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8080792485808170890114531 12121188728712256335171797)
                  ·
                    refine ⟨284090360829193507855589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12121188728712256335171797 284090360829193507855589)
                    ·
                      rfl

theorem cell22_829896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_829896 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829896 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829896 prefixEnd_829896 := by exact prefixLift 829896
  have htrace : WordTrace (prefixWord ++ tailWord_829896) baseStart_829896 baseEnd_829896 := by
    simpa [prefixWord, tailWord_829896, baseEnd_829896] using wordTrace_append hprefix tailTrace_829896
  have hstable : (prefixWord ++ tailWord_829896).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829896).length < 2 ^ (prefixWord ++ tailWord_829896).sum := by decide
  have hdescent : baseEnd_829896 < baseStart_829896 := by decide
  rcases family_descends (prefixWord ++ tailWord_829896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829971 : List Nat := [1, 1, 1, 2, 1, 5, 3, 8]
def baseStart_829971 : Nat := 118140960795 + 829971 * 2 ^ 59
def prefixEnd_829971 : Nat := 4983230072969 + 3 ^ 40 * 829971 * 2
def baseEnd_829971 : Nat := 31568448317990923581151

theorem tailTrace_829971 : CollatzResearch.WordTrace tailWord_829971 prefixEnd_829971 31568448317990923581151 := by
  unfold tailWord_829971
  simp only [CollatzResearch.WordTrace]
  refine ⟨30271529276164289606793767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20181019517442859737862511 30271529276164289606793767)
  ·
    refine ⟨45407293914246434410190651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30271529276164289606793767 45407293914246434410190651)
    ·
      refine ⟨68110940871369651615285977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45407293914246434410190651 68110940871369651615285977)
      ·
        refine ⟨51083205653527238711464483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68110940871369651615285977 51083205653527238711464483)
        ·
          refine ⟨76624808480290858067196725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51083205653527238711464483 76624808480290858067196725)
          ·
            refine ⟨7183575795027267943799693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 76624808480290858067196725 7183575795027267943799693)
            ·
              refine ⟨2693840923135225478924885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7183575795027267943799693 2693840923135225478924885)
              ·
                refine ⟨31568448317990923581151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2693840923135225478924885 31568448317990923581151)
                ·
                  rfl

theorem cell22_829971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 3, 8].length) (baseStart_829971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829971 prefixEnd_829971 := by exact prefixLift 829971
  have htrace : WordTrace (prefixWord ++ tailWord_829971) baseStart_829971 baseEnd_829971 := by
    simpa [prefixWord, tailWord_829971, baseEnd_829971] using wordTrace_append hprefix tailTrace_829971
  have hstable : (prefixWord ++ tailWord_829971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829971).length < 2 ^ (prefixWord ++ tailWord_829971).sum := by decide
  have hdescent : baseEnd_829971 < baseStart_829971 := by decide
  rcases family_descends (prefixWord ++ tailWord_829971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_829973 : List Nat := [1, 3, 2, 1, 3, 1, 2, 3, 2, 4]
def baseStart_829973 : Nat := 118140960795 + 829973 * 2 ^ 59
def prefixEnd_829973 : Nat := 4983230072969 + 3 ^ 40 * 829973 * 2
def baseEnd_829973 : Nat := 284116719502790973680353

theorem tailTrace_829973 : CollatzResearch.WordTrace tailWord_829973 prefixEnd_829973 284116719502790973680353 := by
  unfold tailWord_829973
  simp only [CollatzResearch.WordTrace]
  refine ⟨30271602222157043948366573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20181068148104695965577715 30271602222157043948366573)
  ·
    refine ⟨11351850833308891480637465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30271602222157043948366573 11351850833308891480637465)
    ·
      refine ⟨8513888124981668610478099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11351850833308891480637465 8513888124981668610478099)
      ·
        refine ⟨12770832187472502915717149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8513888124981668610478099 12770832187472502915717149)
        ·
          refine ⟨4789062070302188593393931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12770832187472502915717149 4789062070302188593393931)
          ·
            refine ⟨7183593105453282890090897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4789062070302188593393931 7183593105453282890090897)
            ·
              refine ⟨5387694829089962167568173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7183593105453282890090897 5387694829089962167568173)
              ·
                refine ⟨2020385560908735812838065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5387694829089962167568173 2020385560908735812838065)
                ·
                  refine ⟨1515289170681551859628549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2020385560908735812838065 1515289170681551859628549)
                  ·
                    refine ⟨284116719502790973680353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1515289170681551859628549 284116719502790973680353)
                    ·
                      rfl

theorem cell22_829973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 2, 3, 2, 4].length) (baseStart_829973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_829973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_829973 prefixEnd_829973 := by exact prefixLift 829973
  have htrace : WordTrace (prefixWord ++ tailWord_829973) baseStart_829973 baseEnd_829973 := by
    simpa [prefixWord, tailWord_829973, baseEnd_829973] using wordTrace_append hprefix tailTrace_829973
  have hstable : (prefixWord ++ tailWord_829973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_829973).length < 2 ^ (prefixWord ++ tailWord_829973).sum := by decide
  have hdescent : baseEnd_829973 < baseStart_829973 := by decide
  rcases family_descends (prefixWord ++ tailWord_829973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830063 : List Nat := [1, 1, 2, 1, 3, 2, 3, 2, 3, 4]
def baseStart_830063 : Nat := 118140960795 + 830063 * 2 ^ 59
def prefixEnd_830063 : Nat := 4983230072969 + 3 ^ 40 * 830063 * 2
def baseEnd_830063 : Nat := 284147528342060738930077

theorem tailTrace_830063 : CollatzResearch.WordTrace tailWord_830063 prefixEnd_830063 284147528342060738930077 := by
  unfold tailWord_830063
  simp only [CollatzResearch.WordTrace]
  refine ⟨30274884791830989319142843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20183256527887326212761895 30274884791830989319142843)
  ·
    refine ⟨45412327187746483978714265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30274884791830989319142843 45412327187746483978714265)
    ·
      refine ⟨34059245390809862984035699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45412327187746483978714265 34059245390809862984035699)
      ·
        refine ⟨51088868086214794476053549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34059245390809862984035699 51088868086214794476053549)
        ·
          refine ⟨19158325532330547928520081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51088868086214794476053549 19158325532330547928520081)
          ·
            refine ⟨14368744149247910946390061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19158325532330547928520081 14368744149247910946390061)
            ·
              refine ⟨5388279055967966604896273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14368744149247910946390061 5388279055967966604896273)
              ·
                refine ⟨4041209291975974953672205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5388279055967966604896273 4041209291975974953672205)
                ·
                  refine ⟨1515453484490990607627077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4041209291975974953672205 1515453484490990607627077)
                  ·
                    refine ⟨284147528342060738930077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1515453484490990607627077 284147528342060738930077)
                    ·
                      rfl

theorem cell22_830063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 2, 3, 4].length) (baseStart_830063 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830063 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830063 prefixEnd_830063 := by exact prefixLift 830063
  have htrace : WordTrace (prefixWord ++ tailWord_830063) baseStart_830063 baseEnd_830063 := by
    simpa [prefixWord, tailWord_830063, baseEnd_830063] using wordTrace_append hprefix tailTrace_830063
  have hstable : (prefixWord ++ tailWord_830063).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830063).length < 2 ^ (prefixWord ++ tailWord_830063).sum := by decide
  have hdescent : baseEnd_830063 < baseStart_830063 := by decide
  rcases family_descends (prefixWord ++ tailWord_830063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830125 : List Nat := [1, 5, 2, 1, 1, 2, 1, 2, 1, 6]
def baseStart_830125 : Nat := 118140960795 + 830125 * 2 ^ 59
def prefixEnd_830125 : Nat := 4983230072969 + 3 ^ 40 * 830125 * 2
def baseEnd_830125 : Nat := 284168752209113243879887

theorem tailTrace_830125 : CollatzResearch.WordTrace tailWord_830125 prefixEnd_830125 284168752209113243879887 := by
  unfold tailWord_830125
  simp only [CollatzResearch.WordTrace]
  refine ⟨30277146117606373907899829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20184764078404249271933219 30277146117606373907899829)
  ·
    refine ⟨2838482448525597553865609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30277146117606373907899829 2838482448525597553865609)
    ·
      refine ⟨2128861836394198165399207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2838482448525597553865609 2128861836394198165399207)
      ·
        refine ⟨3193292754591297248098811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2128861836394198165399207 3193292754591297248098811)
        ·
          refine ⟨4789939131886945872148217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3193292754591297248098811 4789939131886945872148217)
          ·
            refine ⟨3592454348915209404111163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4789939131886945872148217 3592454348915209404111163)
            ·
              refine ⟨5388681523372814106166745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3592454348915209404111163 5388681523372814106166745)
              ·
                refine ⟨4041511142529610579625059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5388681523372814106166745 4041511142529610579625059)
                ·
                  refine ⟨6062266713794415869437589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4041511142529610579625059 6062266713794415869437589)
                  ·
                    refine ⟨284168752209113243879887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6062266713794415869437589 284168752209113243879887)
                    ·
                      rfl

theorem cell22_830125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 1, 2, 1, 6].length) (baseStart_830125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830125 prefixEnd_830125 := by exact prefixLift 830125
  have htrace : WordTrace (prefixWord ++ tailWord_830125) baseStart_830125 baseEnd_830125 := by
    simpa [prefixWord, tailWord_830125, baseEnd_830125] using wordTrace_append hprefix tailTrace_830125
  have hstable : (prefixWord ++ tailWord_830125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830125).length < 2 ^ (prefixWord ++ tailWord_830125).sum := by decide
  have hdescent : baseEnd_830125 < baseStart_830125 := by decide
  rcases family_descends (prefixWord ++ tailWord_830125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830138 : List Nat := [3, 1, 1, 1, 2, 3, 1, 1, 2, 7]
def baseStart_830138 : Nat := 118140960795 + 830138 * 2 ^ 59
def prefixEnd_830138 : Nat := 4983230072969 + 3 ^ 40 * 830138 * 2
def baseEnd_830138 : Nat := 284173202374785543304847

theorem tailTrace_830138 : CollatzResearch.WordTrace tailWord_830138 prefixEnd_830138 284173202374785543304847 := by
  unfold tailWord_830138
  simp only [CollatzResearch.WordTrace]
  refine ⟨7569405066639819282030767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20185080177706184752082045 7569405066639819282030767)
  ·
    refine ⟨11354107599959728923046151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7569405066639819282030767 11354107599959728923046151)
    ·
      refine ⟨17031161399939593384569227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11354107599959728923046151 17031161399939593384569227)
      ·
        refine ⟨25546742099909390076853841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17031161399939593384569227 25546742099909390076853841)
        ·
          refine ⟨19160056574932042557640381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25546742099909390076853841 19160056574932042557640381)
          ·
            refine ⟨7185021215599515959115143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19160056574932042557640381 7185021215599515959115143)
            ·
              refine ⟨10777531823399273938672715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7185021215599515959115143 10777531823399273938672715)
              ·
                refine ⟨16166297735098910908009073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10777531823399273938672715 16166297735098910908009073)
                ·
                  refine ⟨12124723301324183181006805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16166297735098910908009073 12124723301324183181006805)
                  ·
                    refine ⟨284173202374785543304847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 12124723301324183181006805 284173202374785543304847)
                    ·
                      rfl

theorem cell22_830138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 1, 2, 7].length) (baseStart_830138 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830138 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830138 prefixEnd_830138 := by exact prefixLift 830138
  have htrace : WordTrace (prefixWord ++ tailWord_830138) baseStart_830138 baseEnd_830138 := by
    simpa [prefixWord, tailWord_830138, baseEnd_830138] using wordTrace_append hprefix tailTrace_830138
  have hstable : (prefixWord ++ tailWord_830138).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830138).length < 2 ^ (prefixWord ++ tailWord_830138).sum := by decide
  have hdescent : baseEnd_830138 < baseStart_830138 := by decide
  rcases family_descends (prefixWord ++ tailWord_830138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830266 : List Nat := [3, 1, 1, 1, 6, 2, 2, 1, 1, 4]
def baseStart_830266 : Nat := 118140960795 + 830266 * 2 ^ 59
def prefixEnd_830266 : Nat := 4983230072969 + 3 ^ 40 * 830266 * 2
def baseEnd_830266 : Nat := 284217019390635876104455

theorem tailTrace_830266 : CollatzResearch.WordTrace tailWord_830266 prefixEnd_830266 284217019390635876104455 := by
  unfold tailWord_830266
  simp only [CollatzResearch.WordTrace]
  refine ⟨7570572202523888747195663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20188192540063703325855101 7570572202523888747195663)
  ·
    refine ⟨11355858303785833120793495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7570572202523888747195663 11355858303785833120793495)
    ·
      refine ⟨17033787455678749681190243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11355858303785833120793495 17033787455678749681190243)
      ·
        refine ⟨25550681183518124521785365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17033787455678749681190243 25550681183518124521785365)
        ·
          refine ⟨1197688180477412086958689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25550681183518124521785365 1197688180477412086958689)
          ·
            refine ⟨898266135358059065219017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1197688180477412086958689 898266135358059065219017)
            ·
              refine ⟨673699601518544298914263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 898266135358059065219017 673699601518544298914263)
              ·
                refine ⟨1010549402277816448371395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 673699601518544298914263 1010549402277816448371395)
                ·
                  refine ⟨1515824103416724672557093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1010549402277816448371395 1515824103416724672557093)
                  ·
                    refine ⟨284217019390635876104455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1515824103416724672557093 284217019390635876104455)
                    ·
                      rfl

theorem cell22_830266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 6, 2, 2, 1, 1, 4].length) (baseStart_830266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830266 prefixEnd_830266 := by exact prefixLift 830266
  have htrace : WordTrace (prefixWord ++ tailWord_830266) baseStart_830266 baseEnd_830266 := by
    simpa [prefixWord, tailWord_830266, baseEnd_830266] using wordTrace_append hprefix tailTrace_830266
  have hstable : (prefixWord ++ tailWord_830266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830266).length < 2 ^ (prefixWord ++ tailWord_830266).sum := by decide
  have hdescent : baseEnd_830266 < baseStart_830266 := by decide
  rcases family_descends (prefixWord ++ tailWord_830266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830320 : List Nat := [2, 1, 1, 1, 4, 1, 3, 2, 7]
def baseStart_830320 : Nat := 118140960795 + 830320 * 2 ^ 59
def prefixEnd_830320 : Nat := 4983230072969 + 3 ^ 40 * 830320 * 2
def baseEnd_830320 : Nat := 94745168231399245084763

theorem tailTrace_830320 : CollatzResearch.WordTrace tailWord_830320 prefixEnd_830320 94745168231399245084763 := by
  unfold tailWord_830320
  simp only [CollatzResearch.WordTrace]
  refine ⟨15142129175949961105624207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20189505567933281474165609 15142129175949961105624207)
  ·
    refine ⟨22713193763924941658436311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15142129175949961105624207 22713193763924941658436311)
    ·
      refine ⟨34069790645887412487654467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22713193763924941658436311 34069790645887412487654467)
      ·
        refine ⟨51104685968831118731481701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34069790645887412487654467 51104685968831118731481701)
        ·
          refine ⟨9582128619155834762152819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51104685968831118731481701 9582128619155834762152819)
          ·
            refine ⟨14373192928733752143229229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9582128619155834762152819 14373192928733752143229229)
            ·
              refine ⟨5389947348275157053710961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14373192928733752143229229 5389947348275157053710961)
              ·
                refine ⟨4042460511206367790283221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5389947348275157053710961 4042460511206367790283221)
                ·
                  refine ⟨94745168231399245084763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4042460511206367790283221 94745168231399245084763)
                  ·
                    rfl

theorem cell22_830320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 3, 2, 7].length) (baseStart_830320 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830320 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830320 prefixEnd_830320 := by exact prefixLift 830320
  have htrace : WordTrace (prefixWord ++ tailWord_830320) baseStart_830320 baseEnd_830320 := by
    simpa [prefixWord, tailWord_830320, baseEnd_830320] using wordTrace_append hprefix tailTrace_830320
  have hstable : (prefixWord ++ tailWord_830320).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830320).length < 2 ^ (prefixWord ++ tailWord_830320).sum := by decide
  have hdescent : baseEnd_830320 < baseStart_830320 := by decide
  rcases family_descends (prefixWord ++ tailWord_830320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830335 : List Nat := [1, 1, 2, 2, 1, 1, 4, 1, 4, 5]
def baseStart_830335 : Nat := 118140960795 + 830335 * 2 ^ 59
def prefixEnd_830335 : Nat := 4983230072969 + 3 ^ 40 * 830335 * 2
def baseEnd_830335 : Nat := 284240639500742696129243

theorem tailTrace_830335 : CollatzResearch.WordTrace tailWord_830335 prefixEnd_830335 284240639500742696129243 := by
  unfold tailWord_830335
  simp only [CollatzResearch.WordTrace]
  refine ⟨30284805446845579773044459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20189870297897053182029639 30284805446845579773044459)
  ·
    refine ⟨45427208170268369659566689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30284805446845579773044459 45427208170268369659566689)
    ·
      refine ⟨34070406127701277244675017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45427208170268369659566689 34070406127701277244675017)
      ·
        refine ⟨25552804595775957933506263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34070406127701277244675017 25552804595775957933506263)
        ·
          refine ⟨38329206893663936900259395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25552804595775957933506263 38329206893663936900259395)
          ·
            refine ⟨57493810340495905350389093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38329206893663936900259395 57493810340495905350389093)
            ·
              refine ⟨10780089438842982253197955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57493810340495905350389093 10780089438842982253197955)
              ·
                refine ⟨16170134158264473379796933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10780089438842982253197955 16170134158264473379796933)
                ·
                  refine ⟨3031900154674588758711925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16170134158264473379796933 3031900154674588758711925)
                  ·
                    refine ⟨284240639500742696129243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3031900154674588758711925 284240639500742696129243)
                    ·
                      rfl

theorem cell22_830335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 1, 4, 5].length) (baseStart_830335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830335 prefixEnd_830335 := by exact prefixLift 830335
  have htrace : WordTrace (prefixWord ++ tailWord_830335) baseStart_830335 baseEnd_830335 := by
    simpa [prefixWord, tailWord_830335, baseEnd_830335] using wordTrace_append hprefix tailTrace_830335
  have hstable : (prefixWord ++ tailWord_830335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830335).length < 2 ^ (prefixWord ++ tailWord_830335).sum := by decide
  have hdescent : baseEnd_830335 < baseStart_830335 := by decide
  rcases family_descends (prefixWord ++ tailWord_830335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830412 : List Nat := [2, 2, 1, 4, 1, 1, 2, 2, 1, 6]
def baseStart_830412 : Nat := 118140960795 + 830412 * 2 ^ 59
def prefixEnd_830412 : Nat := 4983230072969 + 3 ^ 40 * 830412 * 2
def baseEnd_830412 : Nat := 284266998174340161954007

theorem tailTrace_830412 : CollatzResearch.WordTrace tailWord_830412 prefixEnd_830412 284266998174340161954007 := by
  unfold tailWord_830412
  simp only [CollatzResearch.WordTrace]
  refine ⟨15143806933783310961798745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20191742578377747949064993 15143806933783310961798745)
  ·
    refine ⟨11357855200337483221349059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15143806933783310961798745 11357855200337483221349059)
    ·
      refine ⟨17036782800506224832023589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11357855200337483221349059 17036782800506224832023589)
      ·
        refine ⟨3194396775094917156004423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17036782800506224832023589 3194396775094917156004423)
        ·
          refine ⟨4791595162642375734006635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3194396775094917156004423 4791595162642375734006635)
          ·
            refine ⟨7187392743963563601009953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4791595162642375734006635 7187392743963563601009953)
            ·
              refine ⟨5390544557972672700757465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7187392743963563601009953 5390544557972672700757465)
              ·
                refine ⟨4042908418479504525568099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5390544557972672700757465 4042908418479504525568099)
                ·
                  refine ⟨6064362627719256788352149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4042908418479504525568099 6064362627719256788352149)
                  ·
                    refine ⟨284266998174340161954007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6064362627719256788352149 284266998174340161954007)
                    ·
                      rfl

theorem cell22_830412_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 2, 2, 1, 6].length) (baseStart_830412 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830412 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830412 prefixEnd_830412 := by exact prefixLift 830412
  have htrace : WordTrace (prefixWord ++ tailWord_830412) baseStart_830412 baseEnd_830412 := by
    simpa [prefixWord, tailWord_830412, baseEnd_830412] using wordTrace_append hprefix tailTrace_830412
  have hstable : (prefixWord ++ tailWord_830412).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830412).length < 2 ^ (prefixWord ++ tailWord_830412).sum := by decide
  have hdescent : baseEnd_830412 < baseStart_830412 := by decide
  rcases family_descends (prefixWord ++ tailWord_830412) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830414 : List Nat := [4, 1, 1, 1, 2, 4, 2, 1, 1, 5]
def baseStart_830414 : Nat := 118140960795 + 830414 * 2 ^ 59
def prefixEnd_830414 : Nat := 4983230072969 + 3 ^ 40 * 830414 * 2
def baseEnd_830414 : Nat := 284267682815212823404001

theorem tailTrace_830414 : CollatzResearch.WordTrace tailWord_830414 prefixEnd_830414 284267682815212823404001 := by
  unfold tailWord_830414
  simp only [CollatzResearch.WordTrace]
  refine ⟨3785960851694922033146287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20191791209039584176780197 3785960851694922033146287)
  ·
    refine ⟨5678941277542383049719431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3785960851694922033146287 5678941277542383049719431)
    ·
      refine ⟨8518411916313574574579147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5678941277542383049719431 8518411916313574574579147)
      ·
        refine ⟨12777617874470361861868721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8518411916313574574579147 12777617874470361861868721)
        ·
          refine ⟨9583213405852771396401541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12777617874470361861868721 9583213405852771396401541)
          ·
            refine ⟨1796852513597394636825289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9583213405852771396401541 1796852513597394636825289)
            ·
              refine ⟨1347639385198045977618967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1796852513597394636825289 1347639385198045977618967)
              ·
                refine ⟨2021459077797068966428451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1347639385198045977618967 2021459077797068966428451)
                ·
                  refine ⟨3032188616695603449642677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2021459077797068966428451 3032188616695603449642677)
                  ·
                    refine ⟨284267682815212823404001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3032188616695603449642677 284267682815212823404001)
                    ·
                      rfl

theorem cell22_830414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 4, 2, 1, 1, 5].length) (baseStart_830414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830414 prefixEnd_830414 := by exact prefixLift 830414
  have htrace : WordTrace (prefixWord ++ tailWord_830414) baseStart_830414 baseEnd_830414 := by
    simpa [prefixWord, tailWord_830414, baseEnd_830414] using wordTrace_append hprefix tailTrace_830414
  have hstable : (prefixWord ++ tailWord_830414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830414).length < 2 ^ (prefixWord ++ tailWord_830414).sum := by decide
  have hdescent : baseEnd_830414 < baseStart_830414 := by decide
  rcases family_descends (prefixWord ++ tailWord_830414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830429 : List Nat := [1, 4, 3, 1, 2, 2, 1, 1, 1, 6]
def baseStart_830429 : Nat := 118140960795 + 830429 * 2 ^ 59
def prefixEnd_830429 : Nat := 4983230072969 + 3 ^ 40 * 830429 * 2
def baseEnd_830429 : Nat := 284272817621757784278955

theorem tailTrace_830429 : CollatzResearch.WordTrace tailWord_830429 prefixEnd_830429 284272817621757784278955 := by
  unfold tailWord_830429
  simp only [CollatzResearch.WordTrace]
  refine ⟨30288233908505033826966341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20192155939003355884644227 30288233908505033826966341)
  ·
    refine ⟨5679043857844693842556189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30288233908505033826966341 5679043857844693842556189)
    ·
      refine ⟨2129641446691760190958571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5679043857844693842556189 2129641446691760190958571)
      ·
        refine ⟨3194462170037640286437857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2129641446691760190958571 3194462170037640286437857)
        ·
          refine ⟨2395846627528230214828393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3194462170037640286437857 2395846627528230214828393)
          ·
            refine ⟨1796884970646172661121295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2395846627528230214828393 1796884970646172661121295)
            ·
              refine ⟨2695327455969258991681943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1796884970646172661121295 2695327455969258991681943)
              ·
                refine ⟨4042991183953888487522915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2695327455969258991681943 4042991183953888487522915)
                ·
                  refine ⟨6064486775930832731284373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4042991183953888487522915 6064486775930832731284373)
                  ·
                    refine ⟨284272817621757784278955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6064486775930832731284373 284272817621757784278955)
                    ·
                      rfl

theorem cell22_830429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 2, 1, 1, 1, 6].length) (baseStart_830429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830429 prefixEnd_830429 := by exact prefixLift 830429
  have htrace : WordTrace (prefixWord ++ tailWord_830429) baseStart_830429 baseEnd_830429 := by
    simpa [prefixWord, tailWord_830429, baseEnd_830429] using wordTrace_append hprefix tailTrace_830429
  have hstable : (prefixWord ++ tailWord_830429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830429).length < 2 ^ (prefixWord ++ tailWord_830429).sum := by decide
  have hdescent : baseEnd_830429 < baseStart_830429 := by decide
  rcases family_descends (prefixWord ++ tailWord_830429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830510 : List Nat := [4, 1, 3, 1, 1, 1, 5, 2, 1, 3]
def baseStart_830510 : Nat := 118140960795 + 830510 * 2 ^ 59
def prefixEnd_830510 : Nat := 4983230072969 + 3 ^ 40 * 830510 * 2
def baseEnd_830510 : Nat := 284300545577100573003707

theorem tailTrace_830510 : CollatzResearch.WordTrace tailWord_830510 prefixEnd_830510 284300545577100573003707 := by
  unfold tailWord_830510
  simp only [CollatzResearch.WordTrace]
  refine ⟨3786398527651448082583123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20194125480807723107109989 3786398527651448082583123)
  ·
    refine ⟨5679597791477172123874685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3786398527651448082583123 5679597791477172123874685)
    ·
      refine ⟨2129849171803939546453007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5679597791477172123874685 2129849171803939546453007)
      ·
        refine ⟨3194773757705909319679511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2129849171803939546453007 3194773757705909319679511)
        ·
          refine ⟨4792160636558863979519267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3194773757705909319679511 4792160636558863979519267)
          ·
            refine ⟨7188240954838295969278901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4792160636558863979519267 7188240954838295969278901)
            ·
              refine ⟨673897589516090247119897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7188240954838295969278901 673897589516090247119897)
              ·
                refine ⟨505423192137067685339923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 673897589516090247119897 505423192137067685339923)
                ·
                  refine ⟨758134788205601528009885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 505423192137067685339923 758134788205601528009885)
                  ·
                    refine ⟨284300545577100573003707, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 758134788205601528009885 284300545577100573003707)
                    ·
                      rfl

theorem cell22_830510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 5, 2, 1, 3].length) (baseStart_830510 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830510 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830510 prefixEnd_830510 := by exact prefixLift 830510
  have htrace : WordTrace (prefixWord ++ tailWord_830510) baseStart_830510 baseEnd_830510 := by
    simpa [prefixWord, tailWord_830510, baseEnd_830510] using wordTrace_append hprefix tailTrace_830510
  have hstable : (prefixWord ++ tailWord_830510).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830510).length < 2 ^ (prefixWord ++ tailWord_830510).sum := by decide
  have hdescent : baseEnd_830510 < baseStart_830510 := by decide
  rcases family_descends (prefixWord ++ tailWord_830510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830549 : List Nat := [1, 3, 2, 2, 1, 2, 3, 2, 1, 5]
def baseStart_830549 : Nat := 118140960795 + 830549 * 2 ^ 59
def prefixEnd_830549 : Nat := 4983230072969 + 3 ^ 40 * 830549 * 2
def baseEnd_830549 : Nat := 284313896074117471278587

theorem tailTrace_830549 : CollatzResearch.WordTrace tailWord_830549 prefixEnd_830549 284313896074117471278587 := by
  unfold tailWord_830549
  simp only [CollatzResearch.WordTrace]
  refine ⟨30292610668070294321334701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20195073778713529547556467 30292610668070294321334701)
  ·
    refine ⟨11359729000526360370500513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30292610668070294321334701 11359729000526360370500513)
    ·
      refine ⟨8519796750394770277875385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11359729000526360370500513 8519796750394770277875385)
      ·
        refine ⟨6389847562796077708406539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8519796750394770277875385 6389847562796077708406539)
        ·
          refine ⟨9584771344194116562609809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6389847562796077708406539 9584771344194116562609809)
          ·
            refine ⟨7188578508145587421957357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9584771344194116562609809 7188578508145587421957357)
            ·
              refine ⟨2695716940554595283234009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7188578508145587421957357 2695716940554595283234009)
              ·
                refine ⟨2021787705415946462425507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2695716940554595283234009 2021787705415946462425507)
                ·
                  refine ⟨3032681558123919693638261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2021787705415946462425507 3032681558123919693638261)
                  ·
                    refine ⟨284313896074117471278587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3032681558123919693638261 284313896074117471278587)
                    ·
                      rfl

theorem cell22_830549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 3, 2, 1, 5].length) (baseStart_830549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830549 prefixEnd_830549 := by exact prefixLift 830549
  have htrace : WordTrace (prefixWord ++ tailWord_830549) baseStart_830549 baseEnd_830549 := by
    simpa [prefixWord, tailWord_830549, baseEnd_830549] using wordTrace_append hprefix tailTrace_830549
  have hstable : (prefixWord ++ tailWord_830549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830549).length < 2 ^ (prefixWord ++ tailWord_830549).sum := by decide
  have hdescent : baseEnd_830549 < baseStart_830549 := by decide
  rcases family_descends (prefixWord ++ tailWord_830549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830596 : List Nat := [2, 3, 2, 1, 2, 3, 3, 6]
def baseStart_830596 : Nat := 118140960795 + 830596 * 2 ^ 59
def prefixEnd_830596 : Nat := 4983230072969 + 3 ^ 40 * 830596 * 2
def baseEnd_830596 : Nat := 31592220570513890594827

theorem tailTrace_830596 : CollatzResearch.WordTrace tailWord_830596 prefixEnd_830596 31592220570513890594827 := by
  unfold tailWord_830596
  simp only [CollatzResearch.WordTrace]
  refine ⟨15147162449450010674147821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20196216599266680898863761 15147162449450010674147821)
  ·
    refine ⟨5680185918543754002805433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15147162449450010674147821 5680185918543754002805433)
    ·
      refine ⟨4260139438907815502104075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5680185918543754002805433 4260139438907815502104075)
      ·
        refine ⟨6390209158361723253156113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4260139438907815502104075 6390209158361723253156113)
        ·
          refine ⟨4792656868771292439867085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6390209158361723253156113 4792656868771292439867085)
          ·
            refine ⟨1797246325789234664950157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4792656868771292439867085 1797246325789234664950157)
            ·
              refine ⟨673967372170962999356309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1797246325789234664950157 673967372170962999356309)
              ·
                refine ⟨31592220570513890594827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 673967372170962999356309 31592220570513890594827)
                ·
                  rfl

theorem cell22_830596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 3, 6].length) (baseStart_830596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830596 prefixEnd_830596 := by exact prefixLift 830596
  have htrace : WordTrace (prefixWord ++ tailWord_830596) baseStart_830596 baseEnd_830596 := by
    simpa [prefixWord, tailWord_830596, baseEnd_830596] using wordTrace_append hprefix tailTrace_830596
  have hstable : (prefixWord ++ tailWord_830596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830596).length < 2 ^ (prefixWord ++ tailWord_830596).sum := by decide
  have hdescent : baseEnd_830596 < baseStart_830596 := by decide
  rcases family_descends (prefixWord ++ tailWord_830596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830624 : List Nat := [2, 1, 1, 4, 2, 1, 3, 1, 7]
def baseStart_830624 : Nat := 118140960795 + 830624 * 2 ^ 59
def prefixEnd_830624 : Nat := 4983230072969 + 3 ^ 40 * 830624 * 2
def baseEnd_830624 : Nat := 94779856702280758551119

theorem tailTrace_830624 : CollatzResearch.WordTrace tailWord_830624 prefixEnd_830624 94779856702280758551119 := by
  unfold tailWord_830624
  simp only [CollatzResearch.WordTrace]
  refine ⟨15147673071399291065157463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20196897428532388086876617 15147673071399291065157463)
  ·
    refine ⟨22721509607098936597736195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15147673071399291065157463 22721509607098936597736195)
    ·
      refine ⟨34082264410648404896604293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22721509607098936597736195 34082264410648404896604293)
      ·
        refine ⟨6390424576996575918113305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34082264410648404896604293 6390424576996575918113305)
        ·
          refine ⟨4792818432747431938584979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6390424576996575918113305 4792818432747431938584979)
          ·
            refine ⟨7189227649121147907877469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4792818432747431938584979 7189227649121147907877469)
            ·
              refine ⟨2695960368420430465454051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7189227649121147907877469 2695960368420430465454051)
              ·
                refine ⟨4043940552630645698181077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2695960368420430465454051 4043940552630645698181077)
                ·
                  refine ⟨94779856702280758551119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4043940552630645698181077 94779856702280758551119)
                  ·
                    rfl

theorem cell22_830624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 3, 1, 7].length) (baseStart_830624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830624 prefixEnd_830624 := by exact prefixLift 830624
  have htrace : WordTrace (prefixWord ++ tailWord_830624) baseStart_830624 baseEnd_830624 := by
    simpa [prefixWord, tailWord_830624, baseEnd_830624] using wordTrace_append hprefix tailTrace_830624
  have hstable : (prefixWord ++ tailWord_830624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830624).length < 2 ^ (prefixWord ++ tailWord_830624).sum := by decide
  have hdescent : baseEnd_830624 < baseStart_830624 := by decide
  rcases family_descends (prefixWord ++ tailWord_830624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830628 : List Nat := [2, 3, 1, 2, 3, 2, 2, 1, 3, 3]
def baseStart_830628 : Nat := 118140960795 + 830628 * 2 ^ 59
def prefixEnd_830628 : Nat := 4983230072969 + 3 ^ 40 * 830628 * 2
def baseEnd_830628 : Nat := 284340939388587598553345

theorem tailTrace_830628 : CollatzResearch.WordTrace tailWord_830628 prefixEnd_830628 284340939388587598553345 := by
  unfold tailWord_830628
  simp only [CollatzResearch.WordTrace]
  refine ⟨15147746017392045406730269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20196994689856060542307025 15147746017392045406730269)
  ·
    refine ⟨5680404756522017027523851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15147746017392045406730269 5680404756522017027523851)
    ·
      refine ⟨8520607134783025541285777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5680404756522017027523851 8520607134783025541285777)
      ·
        refine ⟨6390455351087269155964333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8520607134783025541285777 6390455351087269155964333)
        ·
          refine ⟨2396420756657725933486625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6390455351087269155964333 2396420756657725933486625)
          ·
            refine ⟨1797315567493294450114969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2396420756657725933486625 1797315567493294450114969)
            ·
              refine ⟨1347986675619970837586227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1797315567493294450114969 1347986675619970837586227)
              ·
                refine ⟨2021980013429956256379341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1347986675619970837586227 2021980013429956256379341)
                ·
                  refine ⟨758242505036233596142253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2021980013429956256379341 758242505036233596142253)
                  ·
                    refine ⟨284340939388587598553345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 758242505036233596142253 284340939388587598553345)
                    ·
                      rfl

theorem cell22_830628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 2, 2, 1, 3, 3].length) (baseStart_830628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830628 prefixEnd_830628 := by exact prefixLift 830628
  have htrace : WordTrace (prefixWord ++ tailWord_830628) baseStart_830628 baseEnd_830628 := by
    simpa [prefixWord, tailWord_830628, baseEnd_830628] using wordTrace_append hprefix tailTrace_830628
  have hstable : (prefixWord ++ tailWord_830628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830628).length < 2 ^ (prefixWord ++ tailWord_830628).sum := by decide
  have hdescent : baseEnd_830628 < baseStart_830628 := by decide
  rcases family_descends (prefixWord ++ tailWord_830628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830639 : List Nat := [1, 1, 2, 1, 2, 3, 4, 1, 2, 5]
def baseStart_830639 : Nat := 118140960795 + 830639 * 2 ^ 59
def prefixEnd_830639 : Nat := 4983230072969 + 3 ^ 40 * 830639 * 2
def baseEnd_830639 : Nat := 284344704913387236528311

theorem tailTrace_830639 : CollatzResearch.WordTrace tailWord_830639 prefixEnd_830639 284344704913387236528311 := by
  unfold tailWord_830639
  simp only [CollatzResearch.WordTrace]
  refine ⟨30295893237744239692110971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20197262158496159794740647 30295893237744239692110971)
  ·
    refine ⟨45443839856616359538166457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30295893237744239692110971 45443839856616359538166457)
    ·
      refine ⟨34082879892462269653624843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45443839856616359538166457 34082879892462269653624843)
      ·
        refine ⟨51124319838693404480437265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34082879892462269653624843 51124319838693404480437265)
        ·
          refine ⟨38343239879020053360327949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51124319838693404480437265 38343239879020053360327949)
          ·
            refine ⟨14378714954632520010122981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38343239879020053360327949 14378714954632520010122981)
            ·
              refine ⟨2696009053993597501898059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14378714954632520010122981 2696009053993597501898059)
              ·
                refine ⟨4044013580990396252847089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2696009053993597501898059 4044013580990396252847089)
                ·
                  refine ⟨3033010185742797189635317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4044013580990396252847089 3033010185742797189635317)
                  ·
                    refine ⟨284344704913387236528311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3033010185742797189635317 284344704913387236528311)
                    ·
                      rfl

theorem cell22_830639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 4, 1, 2, 5].length) (baseStart_830639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830639 prefixEnd_830639 := by exact prefixLift 830639
  have htrace : WordTrace (prefixWord ++ tailWord_830639) baseStart_830639 baseEnd_830639 := by
    simpa [prefixWord, tailWord_830639, baseEnd_830639] using wordTrace_append hprefix tailTrace_830639
  have hstable : (prefixWord ++ tailWord_830639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830639).length < 2 ^ (prefixWord ++ tailWord_830639).sum := by decide
  have hdescent : baseEnd_830639 < baseStart_830639 := by decide
  rcases family_descends (prefixWord ++ tailWord_830639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830714 : List Nat := [3, 1, 1, 1, 1, 4, 1, 10]
def baseStart_830714 : Nat := 118140960795 + 830714 * 2 ^ 59
def prefixEnd_830714 : Nat := 4983230072969 + 3 ^ 40 * 830714 * 2
def baseEnd_830714 : Nat := 31596708771790226767009

theorem tailTrace_830714 : CollatzResearch.WordTrace tailWord_830714 prefixEnd_830714 31596708771790226767009 := by
  unfold tailWord_830714
  simp only [CollatzResearch.WordTrace]
  refine ⟨7574657178118131875272799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20199085808315018334060797 7574657178118131875272799)
  ·
    refine ⟨11361985767177197812909199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7574657178118131875272799 11361985767177197812909199)
    ·
      refine ⟨17042978650765796719363799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11361985767177197812909199 17042978650765796719363799)
      ·
        refine ⟨25564467976148695079045699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17042978650765796719363799 25564467976148695079045699)
        ·
          refine ⟨38346701964223042618568549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25564467976148695079045699 38346701964223042618568549)
          ·
            refine ⟨7190006618291820490981603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38346701964223042618568549 7190006618291820490981603)
            ·
              refine ⟨10785009927437730736472405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7190006618291820490981603 10785009927437730736472405)
              ·
                refine ⟨31596708771790226767009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10785009927437730736472405 31596708771790226767009)
                ·
                  rfl

theorem cell22_830714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 1, 10].length) (baseStart_830714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830714 prefixEnd_830714 := by exact prefixLift 830714
  have htrace : WordTrace (prefixWord ++ tailWord_830714) baseStart_830714 baseEnd_830714 := by
    simpa [prefixWord, tailWord_830714, baseEnd_830714] using wordTrace_append hprefix tailTrace_830714
  have hstable : (prefixWord ++ tailWord_830714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830714).length < 2 ^ (prefixWord ++ tailWord_830714).sum := by decide
  have hdescent : baseEnd_830714 < baseStart_830714 := by decide
  rcases family_descends (prefixWord ++ tailWord_830714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830718 : List Nat := [4, 2, 2, 1, 1, 3, 1, 2, 1, 5]
def baseStart_830718 : Nat := 118140960795 + 830718 * 2 ^ 59
def prefixEnd_830718 : Nat := 4983230072969 + 3 ^ 40 * 830718 * 2
def baseEnd_830718 : Nat := 284371748227857363803069

theorem tailTrace_830718 : CollatzResearch.WordTrace tailWord_830718 prefixEnd_830718 284371748227857363803069 := by
  unfold tailWord_830718
  simp only [CollatzResearch.WordTrace]
  refine ⟨3787346825557254523029601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20199183069638690789491205 3787346825557254523029601)
  ·
    refine ⟨2840510119167940892272201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3787346825557254523029601 2840510119167940892272201)
    ·
      refine ⟨2130382589375955669204151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2840510119167940892272201 2130382589375955669204151)
      ·
        refine ⟨3195573884063933503806227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2130382589375955669204151 3195573884063933503806227)
        ·
          refine ⟨4793360826095900255709341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3195573884063933503806227 4793360826095900255709341)
          ·
            refine ⟨1797510309785962595891003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4793360826095900255709341 1797510309785962595891003)
            ·
              refine ⟨2696265464678943893836505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1797510309785962595891003 2696265464678943893836505)
              ·
                refine ⟨2022199098509207920377379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2696265464678943893836505 2022199098509207920377379)
                ·
                  refine ⟨3033298647763811880566069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2022199098509207920377379 3033298647763811880566069)
                  ·
                    refine ⟨284371748227857363803069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3033298647763811880566069 284371748227857363803069)
                    ·
                      rfl

theorem cell22_830718_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_830718 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830718 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830718 prefixEnd_830718 := by exact prefixLift 830718
  have htrace : WordTrace (prefixWord ++ tailWord_830718) baseStart_830718 baseEnd_830718 := by
    simpa [prefixWord, tailWord_830718, baseEnd_830718] using wordTrace_append hprefix tailTrace_830718
  have hstable : (prefixWord ++ tailWord_830718).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830718).length < 2 ^ (prefixWord ++ tailWord_830718).sum := by decide
  have hdescent : baseEnd_830718 < baseStart_830718 := by decide
  rcases family_descends (prefixWord ++ tailWord_830718) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830722 : List Nat := [3, 4, 1, 1, 3, 1, 3, 1, 1, 4]
def baseStart_830722 : Nat := 118140960795 + 830722 * 2 ^ 59
def prefixEnd_830722 : Nat := 4983230072969 + 3 ^ 40 * 830722 * 2
def baseEnd_830722 : Nat := 284373117509602686703057

theorem tailTrace_830722 : CollatzResearch.WordTrace tailWord_830722 prefixEnd_830722 284373117509602686703057 := by
  unfold tailWord_830722
  simp only [CollatzResearch.WordTrace]
  refine ⟨7574730124110886216845605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20199280330962363244921613 7574730124110886216845605)
  ·
    refine ⟨1420261898270791165658551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7574730124110886216845605 1420261898270791165658551)
    ·
      refine ⟨2130392847406186748487827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1420261898270791165658551 2130392847406186748487827)
      ·
        refine ⟨3195589271109280122731741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2130392847406186748487827 3195589271109280122731741)
        ·
          refine ⟨1198345976665980046024403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3195589271109280122731741 1198345976665980046024403)
          ·
            refine ⟨1797518964998970069036605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1198345976665980046024403 1797518964998970069036605)
            ·
              refine ⟨674069611874613775888727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1797518964998970069036605 674069611874613775888727)
              ·
                refine ⟨1011104417811920663833091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674069611874613775888727 1011104417811920663833091)
                ·
                  refine ⟨1516656626717880995749637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1011104417811920663833091 1516656626717880995749637)
                  ·
                    refine ⟨284373117509602686703057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1516656626717880995749637 284373117509602686703057)
                    ·
                      rfl

theorem cell22_830722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 3, 1, 1, 4].length) (baseStart_830722 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830722 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830722 prefixEnd_830722 := by exact prefixLift 830722
  have htrace : WordTrace (prefixWord ++ tailWord_830722) baseStart_830722 baseEnd_830722 := by
    simpa [prefixWord, tailWord_830722, baseEnd_830722] using wordTrace_append hprefix tailTrace_830722
  have hstable : (prefixWord ++ tailWord_830722).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830722).length < 2 ^ (prefixWord ++ tailWord_830722).sum := by decide
  have hdescent : baseEnd_830722 < baseStart_830722 := by decide
  rcases family_descends (prefixWord ++ tailWord_830722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830765 : List Nat := [1, 5, 3, 1, 1, 2, 3, 6]
def baseStart_830765 : Nat := 118140960795 + 830765 * 2 ^ 59
def prefixEnd_830765 : Nat := 4983230072969 + 3 ^ 40 * 830765 * 2
def baseEnd_830765 : Nat := 31598648587596100875325

theorem tailTrace_830765 : CollatzResearch.WordTrace tailWord_830765 prefixEnd_830765 31598648587596100875325 := by
  unfold tailWord_830765
  simp only [CollatzResearch.WordTrace]
  refine ⟨30300488835287763211197749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20200325890191842140798499 30300488835287763211197749)
  ·
    refine ⟨2840670828308227801049789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30300488835287763211197749 2840670828308227801049789)
    ·
      refine ⟨1065251560615585425393671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2840670828308227801049789 1065251560615585425393671)
      ·
        refine ⟨1597877340923378138090507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1065251560615585425393671 1597877340923378138090507)
        ·
          refine ⟨2396816011385067207135761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1597877340923378138090507 2396816011385067207135761)
          ·
            refine ⟨1797612008538800405351821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2396816011385067207135761 1797612008538800405351821)
            ·
              refine ⟨674104503202050152006933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1797612008538800405351821 674104503202050152006933)
              ·
                refine ⟨31598648587596100875325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 674104503202050152006933 31598648587596100875325)
                ·
                  rfl

theorem cell22_830765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 3, 6].length) (baseStart_830765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830765 prefixEnd_830765 := by exact prefixLift 830765
  have htrace : WordTrace (prefixWord ++ tailWord_830765) baseStart_830765 baseEnd_830765 := by
    simpa [prefixWord, tailWord_830765, baseEnd_830765] using wordTrace_append hprefix tailTrace_830765
  have hstable : (prefixWord ++ tailWord_830765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830765).length < 2 ^ (prefixWord ++ tailWord_830765).sum := by decide
  have hdescent : baseEnd_830765 < baseStart_830765 := by decide
  rcases family_descends (prefixWord ++ tailWord_830765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830780 : List Nat := [2, 2, 2, 2, 1, 3, 1, 5, 1, 3]
def baseStart_830780 : Nat := 118140960795 + 830780 * 2 ^ 59
def prefixEnd_830780 : Nat := 4983230072969 + 3 ^ 40 * 830780 * 2
def baseEnd_830780 : Nat := 284392972094909868752879

theorem tailTrace_830780 : CollatzResearch.WordTrace tailWord_830780 prefixEnd_830780 284392972094909868752879 := by
  unfold tailWord_830780
  simp only [CollatzResearch.WordTrace]
  refine ⟨15150517965116710386496897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20200690620155613848662529 15150517965116710386496897)
  ·
    refine ⟨11362888473837532789872673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15150517965116710386496897 11362888473837532789872673)
    ·
      refine ⟨8522166355378149592404505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11362888473837532789872673 8522166355378149592404505)
      ·
        refine ⟨6391624766533612194303379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8522166355378149592404505 6391624766533612194303379)
        ·
          refine ⟨9587437149800418291455069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6391624766533612194303379 9587437149800418291455069)
          ·
            refine ⟨3595288931175156859295651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9587437149800418291455069 3595288931175156859295651)
            ·
              refine ⟨5392933396762735288943477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3595288931175156859295651 5392933396762735288943477)
              ·
                refine ⟨505587505946506433338451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5392933396762735288943477 505587505946506433338451)
                ·
                  refine ⟨758381258919759650007677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 505587505946506433338451 758381258919759650007677)
                  ·
                    refine ⟨284392972094909868752879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 758381258919759650007677 284392972094909868752879)
                    ·
                      rfl

theorem cell22_830780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 3, 1, 5, 1, 3].length) (baseStart_830780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830780 prefixEnd_830780 := by exact prefixLift 830780
  have htrace : WordTrace (prefixWord ++ tailWord_830780) baseStart_830780 baseEnd_830780 := by
    simpa [prefixWord, tailWord_830780, baseEnd_830780] using wordTrace_append hprefix tailTrace_830780
  have hstable : (prefixWord ++ tailWord_830780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830780).length < 2 ^ (prefixWord ++ tailWord_830780).sum := by decide
  have hdescent : baseEnd_830780 < baseStart_830780 := by decide
  rcases family_descends (prefixWord ++ tailWord_830780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830791 : List Nat := [1, 1, 4, 1, 2, 3, 1, 2, 2, 5]
def baseStart_830791 : Nat := 118140960795 + 830791 * 2 ^ 59
def prefixEnd_830791 : Nat := 4983230072969 + 3 ^ 40 * 830791 * 2
def baseEnd_830791 : Nat := 284396737619709506727845

theorem tailTrace_830791 : CollatzResearch.WordTrace tailWord_830791 prefixEnd_830791 284396737619709506727845 := by
  unfold tailWord_830791
  simp only [CollatzResearch.WordTrace]
  refine ⟨30301437133193569651644227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20200958088795713101096151 30301437133193569651644227)
  ·
    refine ⟨45452155699790354477466341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30301437133193569651644227 45452155699790354477466341)
    ·
      refine ⟨8522279193710691464524939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45452155699790354477466341 8522279193710691464524939)
      ·
        refine ⟨12783418790566037196787409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8522279193710691464524939 12783418790566037196787409)
        ·
          refine ⟨9587564092924527897590557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12783418790566037196787409 9587564092924527897590557)
          ·
            refine ⟨3595336534846697961596459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9587564092924527897590557 3595336534846697961596459)
            ·
              refine ⟨5393004802270046942394689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3595336534846697961596459 5393004802270046942394689)
              ·
                refine ⟨4044753601702535206796017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5393004802270046942394689 4044753601702535206796017)
                ·
                  refine ⟨3033565201276901405097013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4044753601702535206796017 3033565201276901405097013)
                  ·
                    refine ⟨284396737619709506727845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3033565201276901405097013 284396737619709506727845)
                    ·
                      rfl

theorem cell22_830791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 2, 2, 5].length) (baseStart_830791 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830791 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830791 prefixEnd_830791 := by exact prefixLift 830791
  have htrace : WordTrace (prefixWord ++ tailWord_830791) baseStart_830791 baseEnd_830791 := by
    simpa [prefixWord, tailWord_830791, baseEnd_830791] using wordTrace_append hprefix tailTrace_830791
  have hstable : (prefixWord ++ tailWord_830791).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830791).length < 2 ^ (prefixWord ++ tailWord_830791).sum := by decide
  have hdescent : baseEnd_830791 < baseStart_830791 := by decide
  rcases family_descends (prefixWord ++ tailWord_830791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830821 : List Nat := [1, 3, 1, 3, 1, 2, 1, 4, 6]
def baseStart_830821 : Nat := 118140960795 + 830821 * 2 ^ 59
def prefixEnd_830821 : Nat := 4983230072969 + 3 ^ 40 * 830821 * 2
def baseEnd_830821 : Nat := 94802335744266476159251

theorem tailTrace_830821 : CollatzResearch.WordTrace tailWord_830821 prefixEnd_830821 94802335744266476159251 := by
  unfold tailWord_830821
  simp only [CollatzResearch.WordTrace]
  refine ⟨30302531323084884775236317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20201687548723256516824211 30302531323084884775236317)
  ·
    refine ⟨11363449246156831790713619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30302531323084884775236317 11363449246156831790713619)
    ·
      refine ⟨17045173869235247686070429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11363449246156831790713619 17045173869235247686070429)
      ·
        refine ⟨6391940200963217882276411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17045173869235247686070429 6391940200963217882276411)
        ·
          refine ⟨9587910301444826823414617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6391940200963217882276411 9587910301444826823414617)
          ·
            refine ⟨7190932726083620117560963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9587910301444826823414617 7190932726083620117560963)
            ·
              refine ⟨10786399089125430176341445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7190932726083620117560963 10786399089125430176341445)
              ·
                refine ⟨2022449829211018158064021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10786399089125430176341445 2022449829211018158064021)
                ·
                  refine ⟨94802335744266476159251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2022449829211018158064021 94802335744266476159251)
                  ·
                    rfl

theorem cell22_830821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 1, 4, 6].length) (baseStart_830821 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830821 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830821 prefixEnd_830821 := by exact prefixLift 830821
  have htrace : WordTrace (prefixWord ++ tailWord_830821) baseStart_830821 baseEnd_830821 := by
    simpa [prefixWord, tailWord_830821, baseEnd_830821] using wordTrace_append hprefix tailTrace_830821
  have hstable : (prefixWord ++ tailWord_830821).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830821).length < 2 ^ (prefixWord ++ tailWord_830821).sum := by decide
  have hdescent : baseEnd_830821 < baseStart_830821 := by decide
  rcases family_descends (prefixWord ++ tailWord_830821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830853 : List Nat := [1, 3, 1, 1, 3, 1, 4, 1, 4, 3]
def baseStart_830853 : Nat := 118140960795 + 830853 * 2 ^ 59
def prefixEnd_830853 : Nat := 4983230072969 + 3 ^ 40 * 830853 * 2
def baseEnd_830853 : Nat := 284417961486762011677655

theorem tailTrace_830853 : CollatzResearch.WordTrace tailWord_830853 prefixEnd_830853 284417961486762011677655 := by
  unfold tailWord_830853
  simp only [CollatzResearch.WordTrace]
  refine ⟨30303698458968954240401213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20202465639312636160267475 30303698458968954240401213)
  ·
    refine ⟨11363886922113357840150455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30303698458968954240401213 11363886922113357840150455)
    ·
      refine ⟨17045830383170036760225683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11363886922113357840150455 17045830383170036760225683)
      ·
        refine ⟨25568745574755055140338525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17045830383170036760225683 25568745574755055140338525)
        ·
          refine ⟨9588279590533145677626947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25568745574755055140338525 9588279590533145677626947)
          ·
            refine ⟨14382419385799718516440421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9588279590533145677626947 14382419385799718516440421)
            ·
              refine ⟨2696703634837447221832579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14382419385799718516440421 2696703634837447221832579)
              ·
                refine ⟨4045055452256170832748869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2696703634837447221832579 4045055452256170832748869)
                ·
                  refine ⟨758447897298032031140413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4045055452256170832748869 758447897298032031140413)
                  ·
                    refine ⟨284417961486762011677655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 758447897298032031140413 284417961486762011677655)
                    ·
                      rfl

theorem cell22_830853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 1, 4, 1, 4, 3].length) (baseStart_830853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830853 prefixEnd_830853 := by exact prefixLift 830853
  have htrace : WordTrace (prefixWord ++ tailWord_830853) baseStart_830853 baseEnd_830853 := by
    simpa [prefixWord, tailWord_830853, baseEnd_830853] using wordTrace_append hprefix tailTrace_830853
  have hstable : (prefixWord ++ tailWord_830853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830853).length < 2 ^ (prefixWord ++ tailWord_830853).sum := by decide
  have hdescent : baseEnd_830853 < baseStart_830853 := by decide
  rcases family_descends (prefixWord ++ tailWord_830853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830898 : List Nat := [3, 2, 1, 1, 1, 1, 2, 1, 7, 3]
def baseStart_830898 : Nat := 118140960795 + 830898 * 2 ^ 59
def prefixEnd_830898 : Nat := 4983230072969 + 3 ^ 40 * 830898 * 2
def baseEnd_830898 : Nat := 284433365906396894302517

theorem tailTrace_830898 : CollatzResearch.WordTrace tailWord_830898 prefixEnd_830898 284433365906396894302517 := by
  unfold tailWord_830898
  simp only [CollatzResearch.WordTrace]
  refine ⟨7576334935951481731447337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20203559829203951283859565 7576334935951481731447337)
  ·
    refine ⟨5682251201963611298585503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7576334935951481731447337 5682251201963611298585503)
    ·
      refine ⟨8523376802945416947878255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5682251201963611298585503 8523376802945416947878255)
      ·
        refine ⟨12785065204418125421817383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8523376802945416947878255 12785065204418125421817383)
        ·
          refine ⟨19177597806627188132726075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12785065204418125421817383 19177597806627188132726075)
          ·
            refine ⟨28766396709940782199089113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19177597806627188132726075 28766396709940782199089113)
            ·
              refine ⟨21574797532455586649316835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28766396709940782199089113 21574797532455586649316835)
              ·
                refine ⟨32362196298683379973975253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21574797532455586649316835 32362196298683379973975253)
                ·
                  refine ⟨758488975750391718140045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 32362196298683379973975253 758488975750391718140045)
                  ·
                    refine ⟨284433365906396894302517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 758488975750391718140045 284433365906396894302517)
                    ·
                      rfl

theorem cell22_830898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 1, 7, 3].length) (baseStart_830898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830898 prefixEnd_830898 := by exact prefixLift 830898
  have htrace : WordTrace (prefixWord ++ tailWord_830898) baseStart_830898 baseEnd_830898 := by
    simpa [prefixWord, tailWord_830898, baseEnd_830898] using wordTrace_append hprefix tailTrace_830898
  have hstable : (prefixWord ++ tailWord_830898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830898).length < 2 ^ (prefixWord ++ tailWord_830898).sum := by decide
  have hdescent : baseEnd_830898 < baseStart_830898 := by decide
  rcases family_descends (prefixWord ++ tailWord_830898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830911 : List Nat := [1, 1, 2, 2, 2, 1, 1, 5, 7]
def baseStart_830911 : Nat := 118140960795 + 830911 * 2 ^ 59
def prefixEnd_830911 : Nat := 4983230072969 + 3 ^ 40 * 830911 * 2
def baseEnd_830911 : Nat := 94812605357356397909159

theorem tailTrace_830911 : CollatzResearch.WordTrace tailWord_830911 prefixEnd_830911 94812605357356397909159 := by
  unfold tailWord_830911
  simp only [CollatzResearch.WordTrace]
  refine ⟨30305813892758830146012587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20203875928505886764008391 30305813892758830146012587)
  ·
    refine ⟨45458720839138245219018881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30305813892758830146012587 45458720839138245219018881)
    ·
      refine ⟨34094040629353683914264161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45458720839138245219018881 34094040629353683914264161)
      ·
        refine ⟨25570530472015262935698121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34094040629353683914264161 25570530472015262935698121)
        ·
          refine ⟨19177897854011447201773591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25570530472015262935698121 19177897854011447201773591)
          ·
            refine ⟨28766846781017170802660387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19177897854011447201773591 28766846781017170802660387)
            ·
              refine ⟨43150270171525756203990581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28766846781017170802660387 43150270171525756203990581)
              ·
                refine ⟨4045337828580539644124117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43150270171525756203990581 4045337828580539644124117)
                ·
                  refine ⟨94812605357356397909159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4045337828580539644124117 94812605357356397909159)
                  ·
                    rfl

theorem cell22_830911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 1, 5, 7].length) (baseStart_830911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830911 prefixEnd_830911 := by exact prefixLift 830911
  have htrace : WordTrace (prefixWord ++ tailWord_830911) baseStart_830911 baseEnd_830911 := by
    simpa [prefixWord, tailWord_830911, baseEnd_830911] using wordTrace_append hprefix tailTrace_830911
  have hstable : (prefixWord ++ tailWord_830911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830911).length < 2 ^ (prefixWord ++ tailWord_830911).sum := by decide
  have hdescent : baseEnd_830911 < baseStart_830911 := by decide
  rcases family_descends (prefixWord ++ tailWord_830911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830932 : List Nat := [2, 4, 1, 2, 3, 1, 1, 2, 3, 3]
def baseStart_830932 : Nat := 118140960795 + 830932 * 2 ^ 59
def prefixEnd_830932 : Nat := 4983230072969 + 3 ^ 40 * 830932 * 2
def baseEnd_830932 : Nat := 284445004801232138952413

theorem tailTrace_830932 : CollatzResearch.WordTrace tailWord_830932 prefixEnd_830932 284445004801232138952413 := by
  unfold tailWord_830932
  simp only [CollatzResearch.WordTrace]
  refine ⟨15153289912841375366263525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20204386550455167155018033 15153289912841375366263525)
  ·
    refine ⟨2841241858657757881174411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15153289912841375366263525 2841241858657757881174411)
    ·
      refine ⟨4261862787986636821761617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2841241858657757881174411 4261862787986636821761617)
      ·
        refine ⟨3196397090989977616321213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4261862787986636821761617 3196397090989977616321213)
        ·
          refine ⟨1198648909121241606120455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3196397090989977616321213 1198648909121241606120455)
          ·
            refine ⟨1797973363681862409180683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1198648909121241606120455 1797973363681862409180683)
            ·
              refine ⟨2696960045522793613771025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1797973363681862409180683 2696960045522793613771025)
              ·
                refine ⟨2022720034142095210328269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2696960045522793613771025 2022720034142095210328269)
                ·
                  refine ⟨758520012803285703873101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2022720034142095210328269 758520012803285703873101)
                  ·
                    refine ⟨284445004801232138952413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 758520012803285703873101 284445004801232138952413)
                    ·
                      rfl

theorem cell22_830932_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 1, 2, 3, 3].length) (baseStart_830932 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830932 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830932 prefixEnd_830932 := by exact prefixLift 830932
  have htrace : WordTrace (prefixWord ++ tailWord_830932) baseStart_830932 baseEnd_830932 := by
    simpa [prefixWord, tailWord_830932, baseEnd_830932] using wordTrace_append hprefix tailTrace_830932
  have hstable : (prefixWord ++ tailWord_830932).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830932).length < 2 ^ (prefixWord ++ tailWord_830932).sum := by decide
  have hdescent : baseEnd_830932 < baseStart_830932 := by decide
  rcases family_descends (prefixWord ++ tailWord_830932) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830949 : List Nat := [1, 3, 1, 5, 1, 2, 2, 3, 1, 3]
def baseStart_830949 : Nat := 118140960795 + 830949 * 2 ^ 59
def prefixEnd_830949 : Nat := 4983230072969 + 3 ^ 40 * 830949 * 2
def baseEnd_830949 : Nat := 284450824248649761277361

theorem tailTrace_830949 : CollatzResearch.WordTrace tailWord_830949 prefixEnd_830949 284450824248649761277361 := by
  unfold tailWord_830949
  simp only [CollatzResearch.WordTrace]
  refine ⟨30307199866621162635895901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20204799911080775090597267 30307199866621162635895901)
  ·
    refine ⟨11365199949982935988460963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30307199866621162635895901 11365199949982935988460963)
    ·
      refine ⟨17047799924974403982691445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11365199949982935988460963 17047799924974403982691445)
      ·
        refine ⟨1598231242966350373377323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17047799924974403982691445 1598231242966350373377323)
        ·
          refine ⟨2397346864449525560065985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1598231242966350373377323 2397346864449525560065985)
          ·
            refine ⟨1798010148337144170049489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2397346864449525560065985 1798010148337144170049489)
            ·
              refine ⟨1348507611252858127537117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1798010148337144170049489 1348507611252858127537117)
              ·
                refine ⟨505690354219821797826419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1348507611252858127537117 505690354219821797826419)
                ·
                  refine ⟨758535531329732696739629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 505690354219821797826419 758535531329732696739629)
                  ·
                    refine ⟨284450824248649761277361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 758535531329732696739629 284450824248649761277361)
                    ·
                      rfl

theorem cell22_830949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 1, 2, 2, 3, 1, 3].length) (baseStart_830949 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830949 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830949 prefixEnd_830949 := by exact prefixLift 830949
  have htrace : WordTrace (prefixWord ++ tailWord_830949) baseStart_830949 baseEnd_830949 := by
    simpa [prefixWord, tailWord_830949, baseEnd_830949] using wordTrace_append hprefix tailTrace_830949
  have hstable : (prefixWord ++ tailWord_830949).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830949).length < 2 ^ (prefixWord ++ tailWord_830949).sum := by decide
  have hdescent : baseEnd_830949 < baseStart_830949 := by decide
  rcases family_descends (prefixWord ++ tailWord_830949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830962 : List Nat := [3, 2, 1, 4, 1, 3, 1, 2, 5]
def baseStart_830962 : Nat := 118140960795 + 830962 * 2 ^ 59
def prefixEnd_830962 : Nat := 4983230072969 + 3 ^ 40 * 830962 * 2
def baseEnd_830962 : Nat := 94818424804774020234107

theorem tailTrace_830962 : CollatzResearch.WordTrace tailWord_830962 prefixEnd_830962 94818424804774020234107 := by
  unfold tailWord_830962
  simp only [CollatzResearch.WordTrace]
  refine ⟨7576918503893516464029785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20205116010382710570746093 7576918503893516464029785)
  ·
    refine ⟨5682688877920137348022339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7576918503893516464029785 5682688877920137348022339)
    ·
      refine ⟨8524033316880206022033509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5682688877920137348022339 8524033316880206022033509)
      ·
        refine ⟨1598256246915038629131283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8524033316880206022033509 1598256246915038629131283)
        ·
          refine ⟨2397384370372557943696925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1598256246915038629131283 2397384370372557943696925)
          ·
            refine ⟨899019138889709228886347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2397384370372557943696925 899019138889709228886347)
            ·
              refine ⟨1348528708334563843329521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 899019138889709228886347 1348528708334563843329521)
              ·
                refine ⟨1011396531250922882497141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1348528708334563843329521 1011396531250922882497141)
                ·
                  refine ⟨94818424804774020234107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1011396531250922882497141 94818424804774020234107)
                  ·
                    rfl

theorem cell22_830962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 1, 3, 1, 2, 5].length) (baseStart_830962 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830962 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830962 prefixEnd_830962 := by exact prefixLift 830962
  have htrace : WordTrace (prefixWord ++ tailWord_830962) baseStart_830962 baseEnd_830962 := by
    simpa [prefixWord, tailWord_830962, baseEnd_830962] using wordTrace_append hprefix tailTrace_830962
  have hstable : (prefixWord ++ tailWord_830962).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830962).length < 2 ^ (prefixWord ++ tailWord_830962).sum := by decide
  have hdescent : baseEnd_830962 < baseStart_830962 := by decide
  rcases family_descends (prefixWord ++ tailWord_830962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_830973 : List Nat := [1, 4, 1, 1, 1, 4, 1, 3, 6]
def baseStart_830973 : Nat := 118140960795 + 830973 * 2 ^ 59
def prefixEnd_830973 : Nat := 4983230072969 + 3 ^ 40 * 830973 * 2
def baseEnd_830973 : Nat := 94819679979707232892429

theorem tailTrace_830973 : CollatzResearch.WordTrace tailWord_830973 prefixEnd_830973 94819679979707232892429 := by
  unfold tailWord_830973
  simp only [CollatzResearch.WordTrace]
  refine ⟨30308075218534214734769573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20205383479022809823179715 30308075218534214734769573)
  ·
    refine ⟨5682764103475165262769295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30308075218534214734769573 5682764103475165262769295)
    ·
      refine ⟨8524146155212747894153943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5682764103475165262769295 8524146155212747894153943)
      ·
        refine ⟨12786219232819121841230915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8524146155212747894153943 12786219232819121841230915)
        ·
          refine ⟨19179328849228682761846373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12786219232819121841230915 19179328849228682761846373)
          ·
            refine ⟨3596124159230378017846195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19179328849228682761846373 3596124159230378017846195)
            ·
              refine ⟨5394186238845567026769293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3596124159230378017846195 5394186238845567026769293)
              ·
                refine ⟨2022819839567087635038485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5394186238845567026769293 2022819839567087635038485)
                ·
                  refine ⟨94819679979707232892429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2022819839567087635038485 94819679979707232892429)
                  ·
                    rfl

theorem cell22_830973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 1, 3, 6].length) (baseStart_830973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_830973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_830973 prefixEnd_830973 := by exact prefixLift 830973
  have htrace : WordTrace (prefixWord ++ tailWord_830973) baseStart_830973 baseEnd_830973 := by
    simpa [prefixWord, tailWord_830973, baseEnd_830973] using wordTrace_append hprefix tailTrace_830973
  have hstable : (prefixWord ++ tailWord_830973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_830973).length < 2 ^ (prefixWord ++ tailWord_830973).sum := by decide
  have hdescent : baseEnd_830973 < baseStart_830973 := by decide
  rcases family_descends (prefixWord ++ tailWord_830973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831005 : List Nat := [1, 4, 2, 2, 1, 1, 1, 1, 6, 3]
def baseStart_831005 : Nat := 118140960795 + 831005 * 2 ^ 59
def prefixEnd_831005 : Nat := 4983230072969 + 3 ^ 40 * 831005 * 2
def baseEnd_831005 : Nat := 284469994193084281877189

theorem tailTrace_831005 : CollatzResearch.WordTrace tailWord_831005 prefixEnd_831005 284469994193084281877189 := by
  unfold tailWord_831005
  simp only [CollatzResearch.WordTrace]
  refine ⟨30309242354418284199934469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20206161569612189466622979 30309242354418284199934469)
  ·
    refine ⟨5682982941453428287487713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30309242354418284199934469 5682982941453428287487713)
    ·
      refine ⟨4262237206090071215615785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5682982941453428287487713 4262237206090071215615785)
      ·
        refine ⟨3196677904567553411711839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4262237206090071215615785 3196677904567553411711839)
        ·
          refine ⟨4795016856851330117567759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3196677904567553411711839 4795016856851330117567759)
          ·
            refine ⟨7192525285276995176351639, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4795016856851330117567759 7192525285276995176351639)
            ·
              refine ⟨10788787927915492764527459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7192525285276995176351639 10788787927915492764527459)
              ·
                refine ⟨16183181891873239146791189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10788787927915492764527459 16183181891873239146791189)
                ·
                  refine ⟨758586651181558085005837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16183181891873239146791189 758586651181558085005837)
                  ·
                    refine ⟨284469994193084281877189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 758586651181558085005837 284469994193084281877189)
                    ·
                      rfl

theorem cell22_831005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 1, 1, 6, 3].length) (baseStart_831005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831005 prefixEnd_831005 := by exact prefixLift 831005
  have htrace : WordTrace (prefixWord ++ tailWord_831005) baseStart_831005 baseEnd_831005 := by
    simpa [prefixWord, tailWord_831005, baseEnd_831005] using wordTrace_append hprefix tailTrace_831005
  have hstable : (prefixWord ++ tailWord_831005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831005).length < 2 ^ (prefixWord ++ tailWord_831005).sum := by decide
  have hdescent : baseEnd_831005 < baseStart_831005 := by decide
  rcases family_descends (prefixWord ++ tailWord_831005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831022 : List Nat := [4, 1, 3, 1, 2, 1, 2, 1, 4, 3]
def baseStart_831022 : Nat := 118140960795 + 831022 * 2 ^ 59
def prefixEnd_831022 : Nat := 4983230072969 + 3 ^ 40 * 831022 * 2
def baseEnd_831022 : Nat := 284475813640501904202137

theorem tailTrace_831022 : CollatzResearch.WordTrace tailWord_831022 prefixEnd_831022 284475813640501904202137 := by
  unfold tailWord_831022
  simp only [CollatzResearch.WordTrace]
  refine ⟨3788732799419587012912915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20206574930237797402202213 3788732799419587012912915)
  ·
    refine ⟨5683099199129380519369373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3788732799419587012912915 5683099199129380519369373)
    ·
      refine ⟨2131162199673517694763515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5683099199129380519369373 2131162199673517694763515)
      ·
        refine ⟨3196743299510276542145273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2131162199673517694763515 3196743299510276542145273)
        ·
          refine ⟨2397557474632707406608955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3196743299510276542145273 2397557474632707406608955)
          ·
            refine ⟨3596336211949061109913433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2397557474632707406608955 3596336211949061109913433)
            ·
              refine ⟨2697252158961795832435075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3596336211949061109913433 2697252158961795832435075)
              ·
                refine ⟨4045878238442693748652613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2697252158961795832435075 4045878238442693748652613)
                ·
                  refine ⟨758602169708005077872365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4045878238442693748652613 758602169708005077872365)
                  ·
                    refine ⟨284475813640501904202137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 758602169708005077872365 284475813640501904202137)
                    ·
                      rfl

theorem cell22_831022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 2, 1, 4, 3].length) (baseStart_831022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831022 prefixEnd_831022 := by exact prefixLift 831022
  have htrace : WordTrace (prefixWord ++ tailWord_831022) baseStart_831022 baseEnd_831022 := by
    simpa [prefixWord, tailWord_831022, baseEnd_831022] using wordTrace_append hprefix tailTrace_831022
  have hstable : (prefixWord ++ tailWord_831022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831022).length < 2 ^ (prefixWord ++ tailWord_831022).sum := by decide
  have hdescent : baseEnd_831022 < baseStart_831022 := by decide
  rcases family_descends (prefixWord ++ tailWord_831022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831039 : List Nat := [1, 1, 2, 2, 3, 5, 2, 1, 2, 3]
def baseStart_831039 : Nat := 118140960795 + 831039 * 2 ^ 59
def prefixEnd_831039 : Nat := 4983230072969 + 3 ^ 40 * 831039 * 2
def baseEnd_831039 : Nat := 284481633087919526527085

theorem tailTrace_831039 : CollatzResearch.WordTrace tailWord_831039 prefixEnd_831039 284481633087919526527085 := by
  unfold tailWord_831039
  simp only [CollatzResearch.WordTrace]
  refine ⟨30310482436295108006672171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20206988290863405337781447 30310482436295108006672171)
  ·
    refine ⟨45465723654442662010008257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30310482436295108006672171 45465723654442662010008257)
    ·
      refine ⟨34099292740831996507506193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45465723654442662010008257 34099292740831996507506193)
      ·
        refine ⟨25574469555623997380629645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34099292740831996507506193 25574469555623997380629645)
        ·
          refine ⟨9590426083358999017736117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25574469555623997380629645 9590426083358999017736117)
          ·
            refine ⟨899102445314906157912761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9590426083358999017736117 899102445314906157912761)
            ·
              refine ⟨674326833986179618434571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899102445314906157912761 674326833986179618434571)
              ·
                refine ⟨1011490250979269427651857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674326833986179618434571 1011490250979269427651857)
                ·
                  refine ⟨758617688234452070738893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1011490250979269427651857 758617688234452070738893)
                  ·
                    refine ⟨284481633087919526527085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 758617688234452070738893 284481633087919526527085)
                    ·
                      rfl

theorem cell22_831039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 5, 2, 1, 2, 3].length) (baseStart_831039 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831039 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831039 prefixEnd_831039 := by exact prefixLift 831039
  have htrace : WordTrace (prefixWord ++ tailWord_831039) baseStart_831039 baseEnd_831039 := by
    simpa [prefixWord, tailWord_831039, baseEnd_831039] using wordTrace_append hprefix tailTrace_831039
  have hstable : (prefixWord ++ tailWord_831039).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831039).length < 2 ^ (prefixWord ++ tailWord_831039).sum := by decide
  have hdescent : baseEnd_831039 < baseStart_831039 := by decide
  rcases family_descends (prefixWord ++ tailWord_831039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831050 : List Nat := [3, 1, 2, 1, 1, 3, 2, 1, 5, 3]
def baseStart_831050 : Nat := 118140960795 + 831050 * 2 ^ 59
def prefixEnd_831050 : Nat := 4983230072969 + 3 ^ 40 * 831050 * 2
def baseEnd_831050 : Nat := 284485398612719164502051

theorem tailTrace_831050 : CollatzResearch.WordTrace tailWord_831050 prefixEnd_831050 284485398612719164502051 := by
  unfold tailWord_831050
  simp only [CollatzResearch.WordTrace]
  refine ⟨7577720909813814221330651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20207255759503504590215069 7577720909813814221330651)
  ·
    refine ⟨11366581364720721331995977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7577720909813814221330651 11366581364720721331995977)
    ·
      refine ⟨8524936023540540998996983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11366581364720721331995977 8524936023540540998996983)
      ·
        refine ⟨12787404035310811498495475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8524936023540540998996983 12787404035310811498495475)
        ·
          refine ⟨19181106052966217247743213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12787404035310811498495475 19181106052966217247743213)
          ·
            refine ⟨7192914769862331467903705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19181106052966217247743213 7192914769862331467903705)
            ·
              refine ⟨5394686077396748600927779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7192914769862331467903705 5394686077396748600927779)
              ·
                refine ⟨8092029116095122901391669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5394686077396748600927779 8092029116095122901391669)
                ·
                  refine ⟨758627729633917772005469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8092029116095122901391669 758627729633917772005469)
                  ·
                    refine ⟨284485398612719164502051, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 758627729633917772005469 284485398612719164502051)
                    ·
                      rfl

theorem cell22_831050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 2, 1, 5, 3].length) (baseStart_831050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831050 prefixEnd_831050 := by exact prefixLift 831050
  have htrace : WordTrace (prefixWord ++ tailWord_831050) baseStart_831050 baseEnd_831050 := by
    simpa [prefixWord, tailWord_831050, baseEnd_831050] using wordTrace_append hprefix tailTrace_831050
  have hstable : (prefixWord ++ tailWord_831050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831050).length < 2 ^ (prefixWord ++ tailWord_831050).sum := by decide
  have hdescent : baseEnd_831050 < baseStart_831050 := by decide
  rcases family_descends (prefixWord ++ tailWord_831050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831127 : List Nat := [1, 1, 3, 3, 2, 3, 1, 3, 1, 4]
def baseStart_831127 : Nat := 118140960795 + 831127 * 2 ^ 59
def prefixEnd_831127 : Nat := 4983230072969 + 3 ^ 40 * 831127 * 2
def baseEnd_831127 : Nat := 284511757286316630326815

theorem tailTrace_831127 : CollatzResearch.WordTrace tailWord_831127 prefixEnd_831127 284511757286316630326815 := by
  unfold tailWord_831127
  simp only [CollatzResearch.WordTrace]
  refine ⟨30313692059976299035875635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20209128039984199357250423 30313692059976299035875635)
  ·
    refine ⟨45470538089964448553813453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30313692059976299035875635 45470538089964448553813453)
    ·
      refine ⟨17051451783736668207680045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45470538089964448553813453 17051451783736668207680045)
      ·
        refine ⟨6394294418901250577880017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17051451783736668207680045 6394294418901250577880017)
        ·
          refine ⟨4795720814175937933410013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6394294418901250577880017 4795720814175937933410013)
          ·
            refine ⟨1798395305315976725028755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4795720814175937933410013 1798395305315976725028755)
            ·
              refine ⟨2697592957973965087543133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1798395305315976725028755 2697592957973965087543133)
              ·
                refine ⟨1011597359240236907828675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2697592957973965087543133 1011597359240236907828675)
                ·
                  refine ⟨1517396038860355361743013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1011597359240236907828675 1517396038860355361743013)
                  ·
                    refine ⟨284511757286316630326815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1517396038860355361743013 284511757286316630326815)
                    ·
                      rfl

theorem cell22_831127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 3, 1, 3, 1, 4].length) (baseStart_831127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831127 prefixEnd_831127 := by exact prefixLift 831127
  have htrace : WordTrace (prefixWord ++ tailWord_831127) baseStart_831127 baseEnd_831127 := by
    simpa [prefixWord, tailWord_831127, baseEnd_831127] using wordTrace_append hprefix tailTrace_831127
  have hstable : (prefixWord ++ tailWord_831127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831127).length < 2 ^ (prefixWord ++ tailWord_831127).sum := by decide
  have hdescent : baseEnd_831127 < baseStart_831127 := by decide
  rcases family_descends (prefixWord ++ tailWord_831127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831172 : List Nat := [2, 3, 3, 1, 1, 1, 2, 3, 2, 4]
def baseStart_831172 : Nat := 118140960795 + 831172 * 2 ^ 59
def prefixEnd_831172 : Nat := 4983230072969 + 3 ^ 40 * 831172 * 2
def baseEnd_831172 : Nat := 284527161705951512951677

theorem tailTrace_831172 : CollatzResearch.WordTrace tailWord_831172 prefixEnd_831172 284527161705951512951677 := by
  unfold tailWord_831172
  simp only [CollatzResearch.WordTrace]
  refine ⟨15157666672406635860631885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20210222229875514480842513 15157666672406635860631885)
  ·
    refine ⟨5684125002152488447736957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15157666672406635860631885 5684125002152488447736957)
    ·
      refine ⟨2131546875807183167901359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5684125002152488447736957 2131546875807183167901359)
      ·
        refine ⟨3197320313710774751852039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2131546875807183167901359 3197320313710774751852039)
        ·
          refine ⟨4795980470566162127778059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3197320313710774751852039 4795980470566162127778059)
          ·
            refine ⟨7193970705849243191667089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4795980470566162127778059 7193970705849243191667089)
            ·
              refine ⟨5395478029386932393750317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7193970705849243191667089 5395478029386932393750317)
              ·
                refine ⟨2023304261020099647656369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5395478029386932393750317 2023304261020099647656369)
                ·
                  refine ⟨1517478195765074735742277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2023304261020099647656369 1517478195765074735742277)
                  ·
                    refine ⟨284527161705951512951677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1517478195765074735742277 284527161705951512951677)
                    ·
                      rfl

theorem cell22_831172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 2, 3, 2, 4].length) (baseStart_831172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831172 prefixEnd_831172 := by exact prefixLift 831172
  have htrace : WordTrace (prefixWord ++ tailWord_831172) baseStart_831172 baseEnd_831172 := by
    simpa [prefixWord, tailWord_831172, baseEnd_831172] using wordTrace_append hprefix tailTrace_831172
  have hstable : (prefixWord ++ tailWord_831172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831172).length < 2 ^ (prefixWord ++ tailWord_831172).sum := by decide
  have hdescent : baseEnd_831172 < baseStart_831172 := by decide
  rcases family_descends (prefixWord ++ tailWord_831172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831238 : List Nat := [6, 2, 2, 1, 1, 10]
def baseStart_831238 : Nat := 118140960795 + 831238 * 2 ^ 59
def prefixEnd_831238 : Nat := 4983230072969 + 3 ^ 40 * 831238 * 2
def baseEnd_831238 : Nat := 3512959936478386923475

theorem tailTrace_831238 : CollatzResearch.WordTrace tailWord_831238 prefixEnd_831238 3512959936478386923475 := by
  unfold tailWord_831238
  simp only [CollatzResearch.WordTrace]
  refine ⟨947429392580442656036449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20211827041716109995444245 947429392580442656036449)
  ·
    refine ⟨710572044435331992027337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 947429392580442656036449 710572044435331992027337)
    ·
      refine ⟨532929033326498994020503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 710572044435331992027337 532929033326498994020503)
      ·
        refine ⟨799393549989748491030755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 532929033326498994020503 799393549989748491030755)
        ·
          refine ⟨1199090324984622736546133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 799393549989748491030755 1199090324984622736546133)
          ·
            refine ⟨3512959936478386923475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 1199090324984622736546133 3512959936478386923475)
            ·
              rfl

theorem cell22_831238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 10].length) (baseStart_831238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831238 prefixEnd_831238 := by exact prefixLift 831238
  have htrace : WordTrace (prefixWord ++ tailWord_831238) baseStart_831238 baseEnd_831238 := by
    simpa [prefixWord, tailWord_831238, baseEnd_831238] using wordTrace_append hprefix tailTrace_831238
  have hstable : (prefixWord ++ tailWord_831238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831238).length < 2 ^ (prefixWord ++ tailWord_831238).sum := by decide
  have hdescent : baseEnd_831238 < baseStart_831238 := by decide
  rcases family_descends (prefixWord ++ tailWord_831238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831253 : List Nat := [1, 3, 2, 1, 2, 5, 2, 2, 1, 3]
def baseStart_831253 : Nat := 118140960795 + 831253 * 2 ^ 59
def prefixEnd_831253 : Nat := 4983230072969 + 3 ^ 40 * 831253 * 2
def baseEnd_831253 : Nat := 284554889661294301676429

theorem tailTrace_831253 : CollatzResearch.WordTrace tailWord_831253 prefixEnd_831253 284554889661294301676429 := by
  unfold tailWord_831253
  simp only [CollatzResearch.WordTrace]
  refine ⟨30318287657519822554962413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20212191771679881703308275 30318287657519822554962413)
  ·
    refine ⟨11369357871569933458110905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30318287657519822554962413 11369357871569933458110905)
    ·
      refine ⟨8527018403677450093583179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11369357871569933458110905 8527018403677450093583179)
      ·
        refine ⟨12790527605516175140374769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8527018403677450093583179 12790527605516175140374769)
        ·
          refine ⟨9592895704137131355281077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12790527605516175140374769 9592895704137131355281077)
          ·
            refine ⟨899333972262856064557601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9592895704137131355281077 899333972262856064557601)
            ·
              refine ⟨674500479197142048418201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899333972262856064557601 674500479197142048418201)
              ·
                refine ⟨505875359397856536313651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 674500479197142048418201 505875359397856536313651)
                ·
                  refine ⟨758813039096784804470477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 505875359397856536313651 758813039096784804470477)
                  ·
                    refine ⟨284554889661294301676429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 758813039096784804470477 284554889661294301676429)
                    ·
                      rfl

theorem cell22_831253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 5, 2, 2, 1, 3].length) (baseStart_831253 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831253 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831253 prefixEnd_831253 := by exact prefixLift 831253
  have htrace : WordTrace (prefixWord ++ tailWord_831253) baseStart_831253 baseEnd_831253 := by
    simpa [prefixWord, tailWord_831253, baseEnd_831253] using wordTrace_append hprefix tailTrace_831253
  have hstable : (prefixWord ++ tailWord_831253).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831253).length < 2 ^ (prefixWord ++ tailWord_831253).sum := by decide
  have hdescent : baseEnd_831253 < baseStart_831253 := by decide
  rcases family_descends (prefixWord ++ tailWord_831253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831292 : List Nat := [2, 2, 2, 2, 1, 1, 4, 2, 1, 5]
def baseStart_831292 : Nat := 118140960795 + 831292 * 2 ^ 59
def prefixEnd_831292 : Nat := 4983230072969 + 3 ^ 40 * 831292 * 2
def baseEnd_831292 : Nat := 284568240158311199951309

theorem tailTrace_831292 : CollatzResearch.WordTrace tailWord_831292 prefixEnd_831292 284568240158311199951309 := by
  unfold tailWord_831292
  simp only [CollatzResearch.WordTrace]
  refine ⟨15159855052189266107816065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20213140069585688143754753 15159855052189266107816065)
  ·
    refine ⟨11369891289141949580862049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15159855052189266107816065 11369891289141949580862049)
    ·
      refine ⟨8527418466856462185646537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11369891289141949580862049 8527418466856462185646537)
      ·
        refine ⟨6395563850142346639234903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8527418466856462185646537 6395563850142346639234903)
        ·
          refine ⟨9593345775213519958852355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6395563850142346639234903 9593345775213519958852355)
          ·
            refine ⟨14390018662820279938278533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9593345775213519958852355 14390018662820279938278533)
            ·
              refine ⟨2698128499278802488427225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14390018662820279938278533 2698128499278802488427225)
              ·
                refine ⟨2023596374459101866320419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2698128499278802488427225 2023596374459101866320419)
                ·
                  refine ⟨3035394561688652799480629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2023596374459101866320419 3035394561688652799480629)
                  ·
                    refine ⟨284568240158311199951309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3035394561688652799480629 284568240158311199951309)
                    ·
                      rfl

theorem cell22_831292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 4, 2, 1, 5].length) (baseStart_831292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831292 prefixEnd_831292 := by exact prefixLift 831292
  have htrace : WordTrace (prefixWord ++ tailWord_831292) baseStart_831292 baseEnd_831292 := by
    simpa [prefixWord, tailWord_831292, baseEnd_831292] using wordTrace_append hprefix tailTrace_831292
  have hstable : (prefixWord ++ tailWord_831292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831292).length < 2 ^ (prefixWord ++ tailWord_831292).sum := by decide
  have hdescent : baseEnd_831292 < baseStart_831292 := by decide
  rcases family_descends (prefixWord ++ tailWord_831292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831305 : List Nat := [1, 2, 1, 1, 2, 4, 11]
def baseStart_831305 : Nat := 118140960795 + 831305 * 2 ^ 59
def prefixEnd_831305 : Nat := 4983230072969 + 3 ^ 40 * 831305 * 2
def baseEnd_831305 : Nat := 10539729271258648125047

theorem tailTrace_831305 : CollatzResearch.WordTrace tailWord_831305 prefixEnd_831305 10539729271258648125047 := by
  unfold tailWord_831305
  simp only [CollatzResearch.WordTrace]
  refine ⟨30320184253331435435855369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20213456168887623623903579 30320184253331435435855369)
  ·
    refine ⟨22740138189998576576891527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30320184253331435435855369 22740138189998576576891527)
    ·
      refine ⟨34110207284997864865337291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22740138189998576576891527 34110207284997864865337291)
      ·
        refine ⟨51165310927496797298005937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34110207284997864865337291 51165310927496797298005937)
        ·
          refine ⟨38373983195622597973504453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51165310927496797298005937 38373983195622597973504453)
          ·
            refine ⟨7195121849179237120032085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38373983195622597973504453 7195121849179237120032085)
            ·
              refine ⟨10539729271258648125047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 7195121849179237120032085 10539729271258648125047)
              ·
                rfl

theorem cell22_831305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 11].length) (baseStart_831305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831305 prefixEnd_831305 := by exact prefixLift 831305
  have htrace : WordTrace (prefixWord ++ tailWord_831305) baseStart_831305 baseEnd_831305 := by
    simpa [prefixWord, tailWord_831305, baseEnd_831305] using wordTrace_append hprefix tailTrace_831305
  have hstable : (prefixWord ++ tailWord_831305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831305).length < 2 ^ (prefixWord ++ tailWord_831305).sum := by decide
  have hdescent : baseEnd_831305 < baseStart_831305 := by decide
  rcases family_descends (prefixWord ++ tailWord_831305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831457 : List Nat := [1, 2, 3, 1, 2, 1, 2, 10]
def baseStart_831457 : Nat := 118140960795 + 831457 * 2 ^ 59
def prefixEnd_831457 : Nat := 4983230072969 + 3 ^ 40 * 831457 * 2
def baseEnd_831457 : Nat := 31624969225589529952867

theorem tailTrace_831457 : CollatzResearch.WordTrace tailWord_831457 prefixEnd_831457 31624969225589529952867 := by
  unfold tailWord_831457
  simp only [CollatzResearch.WordTrace]
  refine ⟨30325728148780765395388625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20217152099187176930259083 30325728148780765395388625)
  ·
    refine ⟨22744296111585574046541469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30325728148780765395388625 22744296111585574046541469)
    ·
      refine ⟨8529111041844590267453051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22744296111585574046541469 8529111041844590267453051)
      ·
        refine ⟨12793666562766885401179577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8529111041844590267453051 12793666562766885401179577)
        ·
          refine ⟨9595249922075164050884683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12793666562766885401179577 9595249922075164050884683)
          ·
            refine ⟨14392874883112746076327025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9595249922075164050884683 14392874883112746076327025)
            ·
              refine ⟨10794656162334559557245269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14392874883112746076327025 10794656162334559557245269)
              ·
                refine ⟨31624969225589529952867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 10794656162334559557245269 31624969225589529952867)
                ·
                  rfl

theorem cell22_831457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 2, 10].length) (baseStart_831457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831457 prefixEnd_831457 := by exact prefixLift 831457
  have htrace : WordTrace (prefixWord ++ tailWord_831457) baseStart_831457 baseEnd_831457 := by
    simpa [prefixWord, tailWord_831457, baseEnd_831457] using wordTrace_append hprefix tailTrace_831457
  have hstable : (prefixWord ++ tailWord_831457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831457).length < 2 ^ (prefixWord ++ tailWord_831457).sum := by decide
  have hdescent : baseEnd_831457 < baseStart_831457 := by decide
  rcases family_descends (prefixWord ++ tailWord_831457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831459 : List Nat := [1, 1, 1, 6, 1, 3, 1, 1, 1, 6]
def baseStart_831459 : Nat := 118140960795 + 831459 * 2 ^ 59
def prefixEnd_831459 : Nat := 4983230072969 + 3 ^ 40 * 831459 * 2
def baseEnd_831459 : Nat := 284625407671178431025797

theorem tailTrace_831459 : CollatzResearch.WordTrace tailWord_831459 prefixEnd_831459 284625407671178431025797 := by
  unfold tailWord_831459
  simp only [CollatzResearch.WordTrace]
  refine ⟨30325801094773519736961431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20217200729849013157974287 30325801094773519736961431)
  ·
    refine ⟨45488701642160279605442147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30325801094773519736961431 45488701642160279605442147)
    ·
      refine ⟨68233052463240419408163221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45488701642160279605442147 68233052463240419408163221)
      ·
        refine ⟨3198424334214394659757651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 68233052463240419408163221 3198424334214394659757651)
        ·
          refine ⟨4797636501321591989636477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3198424334214394659757651 4797636501321591989636477)
          ·
            refine ⟨1799113687995596996113679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4797636501321591989636477 1799113687995596996113679)
            ·
              refine ⟨2698670531993395494170519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1799113687995596996113679 2698670531993395494170519)
              ·
                refine ⟨4048005797990093241255779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2698670531993395494170519 4048005797990093241255779)
                ·
                  refine ⟨6072008696985139861883669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4048005797990093241255779 6072008696985139861883669)
                  ·
                    refine ⟨284625407671178431025797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6072008696985139861883669 284625407671178431025797)
                    ·
                      rfl

theorem cell22_831459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 3, 1, 1, 1, 6].length) (baseStart_831459 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831459 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831459 prefixEnd_831459 := by exact prefixLift 831459
  have htrace : WordTrace (prefixWord ++ tailWord_831459) baseStart_831459 baseEnd_831459 := by
    simpa [prefixWord, tailWord_831459, baseEnd_831459] using wordTrace_append hprefix tailTrace_831459
  have hstable : (prefixWord ++ tailWord_831459).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831459).length < 2 ^ (prefixWord ++ tailWord_831459).sum := by decide
  have hdescent : baseEnd_831459 < baseStart_831459 := by decide
  rcases family_descends (prefixWord ++ tailWord_831459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831463 : List Nat := [1, 1, 5, 2, 3, 1, 2, 3, 4]
def baseStart_831463 : Nat := 118140960795 + 831463 * 2 ^ 59
def prefixEnd_831463 : Nat := 4983230072969 + 3 ^ 40 * 831463 * 2
def baseEnd_831463 : Nat := 94875592317641251308595

theorem tailTrace_831463 : CollatzResearch.WordTrace tailWord_831463 prefixEnd_831463 94875592317641251308595 := by
  unfold tailWord_831463
  simp only [CollatzResearch.WordTrace]
  refine ⟨30325946986759028420107043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20217297991172685613404695 30325946986759028420107043)
  ·
    refine ⟨45488920480138542630160565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30325946986759028420107043 45488920480138542630160565)
    ·
      refine ⟨4264586295012988371577553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 45488920480138542630160565 4264586295012988371577553)
      ·
        refine ⟨3198439721259741278683165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4264586295012988371577553 3198439721259741278683165)
        ·
          refine ⟨1199414895472402979506187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3198439721259741278683165 1199414895472402979506187)
          ·
            refine ⟨1799122343208604469259281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1199414895472402979506187 1799122343208604469259281)
            ·
              refine ⟨1349341757406453351944461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1799122343208604469259281 1349341757406453351944461)
              ·
                refine ⟨506003159027420006979173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1349341757406453351944461 506003159027420006979173)
                ·
                  refine ⟨94875592317641251308595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 506003159027420006979173 94875592317641251308595)
                  ·
                    rfl

theorem cell22_831463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 2, 3, 4].length) (baseStart_831463 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831463 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831463 prefixEnd_831463 := by exact prefixLift 831463
  have htrace : WordTrace (prefixWord ++ tailWord_831463) baseStart_831463 baseEnd_831463 := by
    simpa [prefixWord, tailWord_831463, baseEnd_831463] using wordTrace_append hprefix tailTrace_831463
  have hstable : (prefixWord ++ tailWord_831463).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831463).length < 2 ^ (prefixWord ++ tailWord_831463).sum := by decide
  have hdescent : baseEnd_831463 < baseStart_831463 := by decide
  rcases family_descends (prefixWord ++ tailWord_831463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831478 : List Nat := [5, 1, 1, 1, 4, 1, 1, 1, 4, 3]
def baseStart_831478 : Nat := 118140960795 + 831478 * 2 ^ 59
def prefixEnd_831478 : Nat := 4983230072969 + 3 ^ 40 * 831478 * 2
def baseEnd_831478 : Nat := 284631911759468714800739

theorem tailTrace_831478 : CollatzResearch.WordTrace tailWord_831478 prefixEnd_831478 284631911759468714800739 := by
  unfold tailWord_831478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1895405880106542873868943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20217662721136457321268725 1895405880106542873868943)
  ·
    refine ⟨2843108820159814310803415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1895405880106542873868943 2843108820159814310803415)
    ·
      refine ⟨4264663230239721466205123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2843108820159814310803415 4264663230239721466205123)
      ·
        refine ⟨6396994845359582199307685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4264663230239721466205123 6396994845359582199307685)
        ·
          refine ⟨1199436533504921662370191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6396994845359582199307685 1199436533504921662370191)
          ·
            refine ⟨1799154800257382493555287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1199436533504921662370191 1799154800257382493555287)
            ·
              refine ⟨2698732200386073740332931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1799154800257382493555287 2698732200386073740332931)
              ·
                refine ⟨4048098300579110610499397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2698732200386073740332931 4048098300579110610499397)
                ·
                  refine ⟨759018431358583239468637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4048098300579110610499397 759018431358583239468637)
                  ·
                    refine ⟨284631911759468714800739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 759018431358583239468637 284631911759468714800739)
                    ·
                      rfl

theorem cell22_831478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_831478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831478 prefixEnd_831478 := by exact prefixLift 831478
  have htrace : WordTrace (prefixWord ++ tailWord_831478) baseStart_831478 baseEnd_831478 := by
    simpa [prefixWord, tailWord_831478, baseEnd_831478] using wordTrace_append hprefix tailTrace_831478
  have hstable : (prefixWord ++ tailWord_831478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831478).length < 2 ^ (prefixWord ++ tailWord_831478).sum := by decide
  have hdescent : baseEnd_831478 < baseStart_831478 := by decide
  rcases family_descends (prefixWord ++ tailWord_831478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831487 : List Nat := [1, 1, 2, 2, 1, 2, 1, 3, 1, 8]
def baseStart_831487 : Nat := 118140960795 + 831487 * 2 ^ 59
def prefixEnd_831487 : Nat := 4983230072969 + 3 ^ 40 * 831487 * 2
def baseEnd_831487 : Nat := 284634992643395691325711

theorem tailTrace_831487 : CollatzResearch.WordTrace tailWord_831487 prefixEnd_831487 284634992643395691325711 := by
  unfold tailWord_831487
  simp only [CollatzResearch.WordTrace]
  refine ⟨30326822338672080518980715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20217881559114720345987143 30326822338672080518980715)
  ·
    refine ⟨45490233508008120778471073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30326822338672080518980715 45490233508008120778471073)
    ·
      refine ⟨34117675131006090583853305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45490233508008120778471073 34117675131006090583853305)
      ·
        refine ⟨25588256348254567937889979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34117675131006090583853305 25588256348254567937889979)
        ·
          refine ⟨38382384522381851906834969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25588256348254567937889979 38382384522381851906834969)
          ·
            refine ⟨28786788391786388930126227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38382384522381851906834969 28786788391786388930126227)
            ·
              refine ⟨43180182587679583395189341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28786788391786388930126227 43180182587679583395189341)
              ·
                refine ⟨16192568470379843773196003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43180182587679583395189341 16192568470379843773196003)
                ·
                  refine ⟨24288852705569765659794005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16192568470379843773196003 24288852705569765659794005)
                  ·
                    refine ⟨284634992643395691325711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24288852705569765659794005 284634992643395691325711)
                    ·
                      rfl

theorem cell22_831487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 3, 1, 8].length) (baseStart_831487 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831487 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831487 prefixEnd_831487 := by exact prefixLift 831487
  have htrace : WordTrace (prefixWord ++ tailWord_831487) baseStart_831487 baseEnd_831487 := by
    simpa [prefixWord, tailWord_831487, baseEnd_831487] using wordTrace_append hprefix tailTrace_831487
  have hstable : (prefixWord ++ tailWord_831487).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831487).length < 2 ^ (prefixWord ++ tailWord_831487).sum := by decide
  have hdescent : baseEnd_831487 < baseStart_831487 := by decide
  rcases family_descends (prefixWord ++ tailWord_831487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831508 : List Nat := [2, 4, 3, 2, 1, 1, 1, 8]
def baseStart_831508 : Nat := 118140960795 + 831508 * 2 ^ 59
def prefixEnd_831508 : Nat := 4983230072969 + 3 ^ 40 * 831508 * 2
def baseEnd_831508 : Nat := 31626909041395404061183

theorem tailTrace_831508 : CollatzResearch.WordTrace tailWord_831508 prefixEnd_831508 31626909041395404061183 := by
  unfold tailWord_831508
  simp only [CollatzResearch.WordTrace]
  refine ⟨15163794135798000552747589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20218392181064000736996785 15163794135798000552747589)
  ·
    refine ⟨2843211400462125103640173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15163794135798000552747589 2843211400462125103640173)
    ·
      refine ⟨1066204275173296913865065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2843211400462125103640173 1066204275173296913865065)
      ·
        refine ⟨799653206379972685398799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1066204275173296913865065 799653206379972685398799)
        ·
          refine ⟨1199479809569959028098199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 799653206379972685398799 1199479809569959028098199)
          ·
            refine ⟨1799219714354938542147299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1199479809569959028098199 1799219714354938542147299)
            ·
              refine ⟨2698829571532407813220949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1799219714354938542147299 2698829571532407813220949)
              ·
                refine ⟨31626909041395404061183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2698829571532407813220949 31626909041395404061183)
                ·
                  rfl

theorem cell22_831508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 1, 1, 8].length) (baseStart_831508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831508 prefixEnd_831508 := by exact prefixLift 831508
  have htrace : WordTrace (prefixWord ++ tailWord_831508) baseStart_831508 baseEnd_831508 := by
    simpa [prefixWord, tailWord_831508, baseEnd_831508] using wordTrace_append hprefix tailTrace_831508
  have hstable : (prefixWord ++ tailWord_831508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831508).length < 2 ^ (prefixWord ++ tailWord_831508).sum := by decide
  have hdescent : baseEnd_831508 < baseStart_831508 := by decide
  rcases family_descends (prefixWord ++ tailWord_831508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831553 : List Nat := [1, 2, 5, 1, 2, 1, 4, 1, 5]
def baseStart_831553 : Nat := 118140960795 + 831553 * 2 ^ 59
def prefixEnd_831553 : Nat := 4983230072969 + 3 ^ 40 * 831553 * 2
def baseEnd_831553 : Nat := 94885861930731173058503

theorem tailTrace_831553 : CollatzResearch.WordTrace tailWord_831553 prefixEnd_831553 94885861930731173058503 := by
  unfold tailWord_831553
  simp only [CollatzResearch.WordTrace]
  refine ⟨30329229556432973790883313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20219486370955315860588875 30329229556432973790883313)
  ·
    refine ⟨22746922167324730343162485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30329229556432973790883313 22746922167324730343162485)
    ·
      refine ⟨2132523953186693469671483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22746922167324730343162485 2132523953186693469671483)
      ·
        refine ⟨3198785929780040204507225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2132523953186693469671483 3198785929780040204507225)
        ·
          refine ⟨2399089447335030153380419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3198785929780040204507225 2399089447335030153380419)
          ·
            refine ⟨3598634171002545230070629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2399089447335030153380419 3598634171002545230070629)
            ·
              refine ⟨674743907062977230638243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3598634171002545230070629 674743907062977230638243)
              ·
                refine ⟨1012115860594465845957365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674743907062977230638243 1012115860594465845957365)
                ·
                  refine ⟨94885861930731173058503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1012115860594465845957365 94885861930731173058503)
                  ·
                    rfl

theorem cell22_831553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 4, 1, 5].length) (baseStart_831553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831553 prefixEnd_831553 := by exact prefixLift 831553
  have htrace : WordTrace (prefixWord ++ tailWord_831553) baseStart_831553 baseEnd_831553 := by
    simpa [prefixWord, tailWord_831553, baseEnd_831553] using wordTrace_append hprefix tailTrace_831553
  have hstable : (prefixWord ++ tailWord_831553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831553).length < 2 ^ (prefixWord ++ tailWord_831553).sum := by decide
  have hdescent : baseEnd_831553 < baseStart_831553 := by decide
  rcases family_descends (prefixWord ++ tailWord_831553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831564 : List Nat := [2, 2, 1, 3, 1, 1, 2, 4, 6]
def baseStart_831564 : Nat := 118140960795 + 831564 * 2 ^ 59
def prefixEnd_831564 : Nat := 4983230072969 + 3 ^ 40 * 831564 * 2
def baseEnd_831564 : Nat := 94887117105664385716825

theorem tailTrace_831564 : CollatzResearch.WordTrace tailWord_831564 prefixEnd_831564 94887117105664385716825 := by
  unfold tailWord_831564
  simp only [CollatzResearch.WordTrace]
  refine ⟨15164815379696561334766873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20219753839595415113022497 15164815379696561334766873)
  ·
    refine ⟨11373611534772421001075155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15164815379696561334766873 11373611534772421001075155)
    ·
      refine ⟨17060417302158631501612733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11373611534772421001075155 17060417302158631501612733)
      ·
        refine ⟨6397656488309486813104775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17060417302158631501612733 6397656488309486813104775)
        ·
          refine ⟨9596484732464230219657163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6397656488309486813104775 9596484732464230219657163)
          ·
            refine ⟨14394727098696345329485745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9596484732464230219657163 14394727098696345329485745)
            ·
              refine ⟨10796045324022258997114309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14394727098696345329485745 10796045324022258997114309)
              ·
                refine ⟨2024258498254173561958933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10796045324022258997114309 2024258498254173561958933)
                ·
                  refine ⟨94887117105664385716825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2024258498254173561958933 94887117105664385716825)
                  ·
                    rfl

theorem cell22_831564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 2, 4, 6].length) (baseStart_831564 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831564 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831564 prefixEnd_831564 := by exact prefixLift 831564
  have htrace : WordTrace (prefixWord ++ tailWord_831564) baseStart_831564 baseEnd_831564 := by
    simpa [prefixWord, tailWord_831564, baseEnd_831564] using wordTrace_append hprefix tailTrace_831564
  have hstable : (prefixWord ++ tailWord_831564).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831564).length < 2 ^ (prefixWord ++ tailWord_831564).sum := by decide
  have hdescent : baseEnd_831564 < baseStart_831564 := by decide
  rcases family_descends (prefixWord ++ tailWord_831564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831566 : List Nat := [4, 1, 1, 1, 1, 5, 1, 1, 3, 4]
def baseStart_831566 : Nat := 118140960795 + 831566 * 2 ^ 59
def prefixEnd_831566 : Nat := 4983230072969 + 3 ^ 40 * 831566 * 2
def baseEnd_831566 : Nat := 284662035957865818600469

theorem tailTrace_831566 : CollatzResearch.WordTrace tailWord_831566 prefixEnd_831566 284662035957865818600469 := by
  unfold tailWord_831566
  simp only [CollatzResearch.WordTrace]
  refine ⟨3791212963173234626388319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20219802470257251340737701 3791212963173234626388319)
  ·
    refine ⟨5686819444759851939582479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3791212963173234626388319 5686819444759851939582479)
    ·
      refine ⟨8530229167139777909373719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5686819444759851939582479 8530229167139777909373719)
      ·
        refine ⟨12795343750709666864060579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8530229167139777909373719 12795343750709666864060579)
        ·
          refine ⟨19193015626064500296090869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12795343750709666864060579 19193015626064500296090869)
          ·
            refine ⟨1799345214943546902758519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19193015626064500296090869 1799345214943546902758519)
            ·
              refine ⟨2699017822415320354137779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1799345214943546902758519 2699017822415320354137779)
              ·
                refine ⟨4048526733622980531206669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2699017822415320354137779 4048526733622980531206669)
                ·
                  refine ⟨1518197525108617699202501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4048526733622980531206669 1518197525108617699202501)
                  ·
                    refine ⟨284662035957865818600469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1518197525108617699202501 284662035957865818600469)
                    ·
                      rfl

theorem cell22_831566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 5, 1, 1, 3, 4].length) (baseStart_831566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831566 prefixEnd_831566 := by exact prefixLift 831566
  have htrace : WordTrace (prefixWord ++ tailWord_831566) baseStart_831566 baseEnd_831566 := by
    simpa [prefixWord, tailWord_831566, baseEnd_831566] using wordTrace_append hprefix tailTrace_831566
  have hstable : (prefixWord ++ tailWord_831566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831566).length < 2 ^ (prefixWord ++ tailWord_831566).sum := by decide
  have hdescent : baseEnd_831566 < baseStart_831566 := by decide
  rcases family_descends (prefixWord ++ tailWord_831566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831598 : List Nat := [4, 1, 2, 2, 1, 1, 3, 4, 4]
def baseStart_831598 : Nat := 118140960795 + 831598 * 2 ^ 59
def prefixEnd_831598 : Nat := 4983230072969 + 3 ^ 40 * 831598 * 2
def baseEnd_831598 : Nat := 94890996737276133933457

theorem tailTrace_831598 : CollatzResearch.WordTrace tailWord_831598 prefixEnd_831598 94890996737276133933457 := by
  unfold tailWord_831598
  simp only [CollatzResearch.WordTrace]
  refine ⟨3791358855158743309533931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20220580560846630984180965 3791358855158743309533931)
  ·
    refine ⟨5687038282738114964300897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3791358855158743309533931 5687038282738114964300897)
    ·
      refine ⟨4265278712053586223225673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5687038282738114964300897 4265278712053586223225673)
      ·
        refine ⟨3198959034040189667419255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4265278712053586223225673 3198959034040189667419255)
        ·
          refine ⟨4798438551060284501128883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3198959034040189667419255 4798438551060284501128883)
          ·
            refine ⟨7197657826590426751693325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4798438551060284501128883 7197657826590426751693325)
            ·
              refine ⟨2699121684971410031884997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7197657826590426751693325 2699121684971410031884997)
              ·
                refine ⟨506085315932139380978437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2699121684971410031884997 506085315932139380978437)
                ·
                  refine ⟨94890996737276133933457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 506085315932139380978437 94890996737276133933457)
                  ·
                    rfl

theorem cell22_831598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 1, 3, 4, 4].length) (baseStart_831598 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831598 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831598 prefixEnd_831598 := by exact prefixLift 831598
  have htrace : WordTrace (prefixWord ++ tailWord_831598) baseStart_831598 baseEnd_831598 := by
    simpa [prefixWord, tailWord_831598, baseEnd_831598] using wordTrace_append hprefix tailTrace_831598
  have hstable : (prefixWord ++ tailWord_831598).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831598).length < 2 ^ (prefixWord ++ tailWord_831598).sum := by decide
  have hdescent : baseEnd_831598 < baseStart_831598 := by decide
  rcases family_descends (prefixWord ++ tailWord_831598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831613 : List Nat := [1, 4, 1, 1, 3, 2, 2, 3, 2, 3]
def baseStart_831613 : Nat := 118140960795 + 831613 * 2 ^ 59
def prefixEnd_831613 : Nat := 4983230072969 + 3 ^ 40 * 831613 * 2
def baseEnd_831613 : Nat := 284678125018373362675325

theorem tailTrace_831613 : CollatzResearch.WordTrace tailWord_831613 prefixEnd_831613 284678125018373362675325 := by
  unfold tailWord_831613
  simp only [CollatzResearch.WordTrace]
  refine ⟨30331417936215604038067493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20220945290810402692044995 30331417936215604038067493)
  ·
    refine ⟨5687140863040425757137655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30331417936215604038067493 5687140863040425757137655)
    ·
      refine ⟨8530711294560638635706483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5687140863040425757137655 8530711294560638635706483)
      ·
        refine ⟨12796066941840957953559725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8530711294560638635706483 12796066941840957953559725)
        ·
          refine ⟨4798525103190359232584897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12796066941840957953559725 4798525103190359232584897)
          ·
            refine ⟨3598893827392769424438673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4798525103190359232584897 3598893827392769424438673)
            ·
              refine ⟨2699170370544577068329005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3598893827392769424438673 2699170370544577068329005)
              ·
                refine ⟨1012188888954216400623377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2699170370544577068329005 1012188888954216400623377)
                ·
                  refine ⟨759141666715662300467533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1012188888954216400623377 759141666715662300467533)
                  ·
                    refine ⟨284678125018373362675325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 759141666715662300467533 284678125018373362675325)
                    ·
                      rfl

theorem cell22_831613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 2, 2, 3, 2, 3].length) (baseStart_831613 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831613 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831613 prefixEnd_831613 := by exact prefixLift 831613
  have htrace : WordTrace (prefixWord ++ tailWord_831613) baseStart_831613 baseEnd_831613 := by
    simpa [prefixWord, tailWord_831613, baseEnd_831613] using wordTrace_append hprefix tailTrace_831613
  have hstable : (prefixWord ++ tailWord_831613).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831613).length < 2 ^ (prefixWord ++ tailWord_831613).sum := by decide
  have hdescent : baseEnd_831613 < baseStart_831613 := by decide
  rcases family_descends (prefixWord ++ tailWord_831613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831709 : List Nat := [1, 4, 3, 2, 1, 2, 3, 2, 1, 3]
def baseStart_831709 : Nat := 118140960795 + 831709 * 2 ^ 59
def prefixEnd_831709 : Nat := 4983230072969 + 3 ^ 40 * 831709 * 2
def baseEnd_831709 : Nat := 284710987780261112275031

theorem tailTrace_831709 : CollatzResearch.WordTrace tailWord_831709 prefixEnd_831709 284710987780261112275031 := by
  unfold tailWord_831709
  simp only [CollatzResearch.WordTrace]
  refine ⟨30334919343867812433562181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20223279562578541622374787 30334919343867812433562181)
  ·
    refine ⟨5687797376975214831292909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30334919343867812433562181 5687797376975214831292909)
    ·
      refine ⟨2132924016365705561734841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5687797376975214831292909 2132924016365705561734841)
      ·
        refine ⟨1599693012274279171301131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2132924016365705561734841 1599693012274279171301131)
        ·
          refine ⟨2399539518411418756951697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1599693012274279171301131 2399539518411418756951697)
          ·
            refine ⟨1799654638808564067713773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2399539518411418756951697 1799654638808564067713773)
            ·
              refine ⟨674870489553211525392665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1799654638808564067713773 674870489553211525392665)
              ·
                refine ⟨506152867164908644044499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 674870489553211525392665 506152867164908644044499)
                ·
                  refine ⟨759229300747362966066749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 506152867164908644044499 759229300747362966066749)
                  ·
                    refine ⟨284710987780261112275031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 759229300747362966066749 284710987780261112275031)
                    ·
                      rfl

theorem cell22_831709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 3, 2, 1, 3].length) (baseStart_831709 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831709 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831709 prefixEnd_831709 := by exact prefixLift 831709
  have htrace : WordTrace (prefixWord ++ tailWord_831709) baseStart_831709 baseEnd_831709 := by
    simpa [prefixWord, tailWord_831709, baseEnd_831709] using wordTrace_append hprefix tailTrace_831709
  have hstable : (prefixWord ++ tailWord_831709).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831709).length < 2 ^ (prefixWord ++ tailWord_831709).sum := by decide
  have hdescent : baseEnd_831709 < baseStart_831709 := by decide
  rcases family_descends (prefixWord ++ tailWord_831709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831731 : List Nat := [1, 1, 1, 2, 2, 4, 2, 3, 1, 5]
def baseStart_831731 : Nat := 118140960795 + 831731 * 2 ^ 59
def prefixEnd_831731 : Nat := 4983230072969 + 3 ^ 40 * 831731 * 2
def baseEnd_831731 : Nat := 284718518829860388224963

theorem tailTrace_831731 : CollatzResearch.WordTrace tailWord_831731 prefixEnd_831731 284718518829860388224963 := by
  unfold tailWord_831731
  simp only [CollatzResearch.WordTrace]
  refine ⟨30335721749788110190863047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20223814499858740127242031 30335721749788110190863047)
  ·
    refine ⟨45503582624682165286294571, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30335721749788110190863047 45503582624682165286294571)
    ·
      refine ⟨68255373937023247929441857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45503582624682165286294571 68255373937023247929441857)
      ·
        refine ⟨51191530452767435947081393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68255373937023247929441857 51191530452767435947081393)
        ·
          refine ⟨38393647839575576960311045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51191530452767435947081393 38393647839575576960311045)
          ·
            refine ⟨7198808969920420680058321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38393647839575576960311045 7198808969920420680058321)
            ·
              refine ⟨5399106727440315510043741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7198808969920420680058321 5399106727440315510043741)
              ·
                refine ⟨2024665022790118316266403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5399106727440315510043741 2024665022790118316266403)
                ·
                  refine ⟨3036997534185177474399605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2024665022790118316266403 3036997534185177474399605)
                  ·
                    refine ⟨284718518829860388224963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3036997534185177474399605 284718518829860388224963)
                    ·
                      rfl

theorem cell22_831731_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 2, 3, 1, 5].length) (baseStart_831731 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831731 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831731 prefixEnd_831731 := by exact prefixLift 831731
  have htrace : WordTrace (prefixWord ++ tailWord_831731) baseStart_831731 baseEnd_831731 := by
    simpa [prefixWord, tailWord_831731, baseEnd_831731] using wordTrace_append hprefix tailTrace_831731
  have hstable : (prefixWord ++ tailWord_831731).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831731).length < 2 ^ (prefixWord ++ tailWord_831731).sum := by decide
  have hdescent : baseEnd_831731 < baseStart_831731 := by decide
  rcases family_descends (prefixWord ++ tailWord_831731) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831767 : List Nat := [1, 1, 3, 4, 1, 4, 2, 2, 4]
def baseStart_831767 : Nat := 118140960795 + 831767 * 2 ^ 59
def prefixEnd_831767 : Nat := 4983230072969 + 3 ^ 40 * 831767 * 2
def baseEnd_831767 : Nat := 94910280788522764774951

theorem tailTrace_831767 : CollatzResearch.WordTrace tailWord_831767 prefixEnd_831767 94910280788522764774951 := by
  unfold tailWord_831767
  simp only [CollatzResearch.WordTrace]
  refine ⟨30337034777657688339173555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20224689851771792226115703 30337034777657688339173555)
  ·
    refine ⟨45505552166486532508760333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30337034777657688339173555 45505552166486532508760333)
    ·
      refine ⟨17064582062432449690785125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45505552166486532508760333 17064582062432449690785125)
      ·
        refine ⟨3199609136706084317022211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17064582062432449690785125 3199609136706084317022211)
        ·
          refine ⟨4799413705059126475533317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3199609136706084317022211 4799413705059126475533317)
          ·
            refine ⟨899890069698586214162497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4799413705059126475533317 899890069698586214162497)
            ·
              refine ⟨674917552273939660621873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 899890069698586214162497 674917552273939660621873)
              ·
                refine ⟨506188164205454745466405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 674917552273939660621873 506188164205454745466405)
                ·
                  refine ⟨94910280788522764774951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 506188164205454745466405 94910280788522764774951)
                  ·
                    rfl

theorem cell22_831767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 4, 2, 2, 4].length) (baseStart_831767 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831767 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831767 prefixEnd_831767 := by exact prefixLift 831767
  have htrace : WordTrace (prefixWord ++ tailWord_831767) baseStart_831767 baseEnd_831767 := by
    simpa [prefixWord, tailWord_831767, baseEnd_831767] using wordTrace_append hprefix tailTrace_831767
  have hstable : (prefixWord ++ tailWord_831767).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831767).length < 2 ^ (prefixWord ++ tailWord_831767).sum := by decide
  have hdescent : baseEnd_831767 < baseStart_831767 := by decide
  rcases family_descends (prefixWord ++ tailWord_831767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831778 : List Nat := [3, 3, 1, 1, 3, 1, 3, 7]
def baseStart_831778 : Nat := 118140960795 + 831778 * 2 ^ 59
def prefixEnd_831778 : Nat := 4983230072969 + 3 ^ 40 * 831778 * 2
def baseEnd_831778 : Nat := 31637178654485325811091

theorem tailTrace_831778 : CollatzResearch.WordTrace tailWord_831778 prefixEnd_831778 31637178654485325811091 := by
  unfold tailWord_831778
  simp only [CollatzResearch.WordTrace]
  refine ⟨7584358995154459304455997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20224957320411891478549325 7584358995154459304455997)
  ·
    refine ⟨2844134623182922239170999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7584358995154459304455997 2844134623182922239170999)
    ·
      refine ⟨4266201934774383358756499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2844134623182922239170999 4266201934774383358756499)
      ·
        refine ⟨6399302902161575038134749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4266201934774383358756499 6399302902161575038134749)
        ·
          refine ⟨2399738588310590639300531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6399302902161575038134749 2399738588310590639300531)
          ·
            refine ⟨3599607882465885958950797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2399738588310590639300531 3599607882465885958950797)
            ·
              refine ⟨1349852955924707234606549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3599607882465885958950797 1349852955924707234606549)
              ·
                refine ⟨31637178654485325811091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1349852955924707234606549 31637178654485325811091)
                ·
                  rfl

theorem cell22_831778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 3, 7].length) (baseStart_831778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831778 prefixEnd_831778 := by exact prefixLift 831778
  have htrace : WordTrace (prefixWord ++ tailWord_831778) baseStart_831778 baseEnd_831778 := by
    simpa [prefixWord, tailWord_831778, baseEnd_831778] using wordTrace_append hprefix tailTrace_831778
  have hstable : (prefixWord ++ tailWord_831778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831778).length < 2 ^ (prefixWord ++ tailWord_831778).sum := by decide
  have hdescent : baseEnd_831778 < baseStart_831778 := by decide
  rcases family_descends (prefixWord ++ tailWord_831778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831917 : List Nat := [1, 5, 2, 2, 2, 1, 1, 2, 1, 5]
def baseStart_831917 : Nat := 118140960795 + 831917 * 2 ^ 59
def prefixEnd_831917 : Nat := 4983230072969 + 3 ^ 40 * 831917 * 2
def baseEnd_831917 : Nat := 284782190431017903074393

theorem tailTrace_831917 : CollatzResearch.WordTrace tailWord_831917 prefixEnd_831917 284782190431017903074393 := by
  unfold tailWord_831917
  simp only [CollatzResearch.WordTrace]
  refine ⟨30342505727114263957134005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20228337151409509304756003 30342505727114263957134005)
  ·
    refine ⟨2844609911916962245981313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30342505727114263957134005 2844609911916962245981313)
    ·
      refine ⟨2133457433937721684485985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2844609911916962245981313 2133457433937721684485985)
      ·
        refine ⟨1600093075453291263364489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2133457433937721684485985 1600093075453291263364489)
        ·
          refine ⟨1200069806589968447523367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1600093075453291263364489 1200069806589968447523367)
          ·
            refine ⟨1800104709884952671285051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1200069806589968447523367 1800104709884952671285051)
            ·
              refine ⟨2700157064827429006927577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1800104709884952671285051 2700157064827429006927577)
              ·
                refine ⟨2025117798620571755195683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2700157064827429006927577 2025117798620571755195683)
                ·
                  refine ⟨3037676697930857632793525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2025117798620571755195683 3037676697930857632793525)
                  ·
                    refine ⟨284782190431017903074393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3037676697930857632793525 284782190431017903074393)
                    ·
                      rfl

theorem cell22_831917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 1, 2, 1, 5].length) (baseStart_831917 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831917 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831917 prefixEnd_831917 := by exact prefixLift 831917
  have htrace : WordTrace (prefixWord ++ tailWord_831917) baseStart_831917 baseEnd_831917 := by
    simpa [prefixWord, tailWord_831917, baseEnd_831917] using wordTrace_append hprefix tailTrace_831917
  have hstable : (prefixWord ++ tailWord_831917).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831917).length < 2 ^ (prefixWord ++ tailWord_831917).sum := by decide
  have hdescent : baseEnd_831917 < baseStart_831917 := by decide
  rcases family_descends (prefixWord ++ tailWord_831917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831943 : List Nat := [1, 1, 4, 1, 1, 4, 1, 1, 2, 6]
def baseStart_831943 : Nat := 118140960795 + 831943 * 2 ^ 59
def prefixEnd_831943 : Nat := 4983230072969 + 3 ^ 40 * 831943 * 2
def baseEnd_831943 : Nat := 284791090762362501924313

theorem tailTrace_831943 : CollatzResearch.WordTrace tailWord_831943 prefixEnd_831943 284791090762362501924313 := by
  unfold tailWord_831943
  simp only [CollatzResearch.WordTrace]
  refine ⟨30343454025020070397580483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20228969350013380265053655 30343454025020070397580483)
  ·
    refine ⟨45515181037530105596370725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30343454025020070397580483 45515181037530105596370725)
    ·
      refine ⟨8534096444536894799319511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45515181037530105596370725 8534096444536894799319511)
      ·
        refine ⟨12801144666805342198979267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8534096444536894799319511 12801144666805342198979267)
        ·
          refine ⟨19201717000208013298468901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12801144666805342198979267 19201717000208013298468901)
          ·
            refine ⟨3600321937539002493462919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19201717000208013298468901 3600321937539002493462919)
            ·
              refine ⟨5400482906308503740194379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3600321937539002493462919 5400482906308503740194379)
              ·
                refine ⟨8100724359462755610291569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5400482906308503740194379 8100724359462755610291569)
                ·
                  refine ⟨6075543269597066707718677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8100724359462755610291569 6075543269597066707718677)
                  ·
                    refine ⟨284791090762362501924313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6075543269597066707718677 284791090762362501924313)
                    ·
                      rfl

theorem cell22_831943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 1, 1, 2, 6].length) (baseStart_831943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831943 prefixEnd_831943 := by exact prefixLift 831943
  have htrace : WordTrace (prefixWord ++ tailWord_831943) baseStart_831943 baseEnd_831943 := by
    simpa [prefixWord, tailWord_831943, baseEnd_831943] using wordTrace_append hprefix tailTrace_831943
  have hstable : (prefixWord ++ tailWord_831943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831943).length < 2 ^ (prefixWord ++ tailWord_831943).sum := by decide
  have hdescent : baseEnd_831943 < baseStart_831943 := by decide
  rcases family_descends (prefixWord ++ tailWord_831943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_831990 : List Nat := [5, 1, 1, 1, 2, 1, 1, 1, 4, 5]
def baseStart_831990 : Nat := 118140960795 + 831990 * 2 ^ 59
def prefixEnd_831990 : Nat := 4983230072969 + 3 ^ 40 * 831990 * 2
def baseEnd_831990 : Nat := 284807179822870045999169

theorem tailTrace_831990 : CollatzResearch.WordTrace tailWord_831990 prefixEnd_831990 284807179822870045999169 := by
  unfold tailWord_831990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1896573015990612339033839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20230112170566531616360949 1896573015990612339033839)
  ·
    refine ⟨2844859523985918508550759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1896573015990612339033839 2844859523985918508550759)
    ·
      refine ⟨4267289285978877762826139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2844859523985918508550759 4267289285978877762826139)
      ·
        refine ⟨6400933928968316644239209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4267289285978877762826139 6400933928968316644239209)
        ·
          refine ⟨4800700446726237483179407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6400933928968316644239209 4800700446726237483179407)
          ·
            refine ⟨7201050670089356224769111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4800700446726237483179407 7201050670089356224769111)
            ·
              refine ⟨10801576005134034337153667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7201050670089356224769111 10801576005134034337153667)
              ·
                refine ⟨16202364007701051505730501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10801576005134034337153667 16202364007701051505730501)
                ·
                  refine ⟨3037943251443947157324469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16202364007701051505730501 3037943251443947157324469)
                  ·
                    refine ⟨284807179822870045999169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3037943251443947157324469 284807179822870045999169)
                    ·
                      rfl

theorem cell22_831990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 1, 4, 5].length) (baseStart_831990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_831990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_831990 prefixEnd_831990 := by exact prefixLift 831990
  have htrace : WordTrace (prefixWord ++ tailWord_831990) baseStart_831990 baseEnd_831990 := by
    simpa [prefixWord, tailWord_831990, baseEnd_831990] using wordTrace_append hprefix tailTrace_831990
  have hstable : (prefixWord ++ tailWord_831990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_831990).length < 2 ^ (prefixWord ++ tailWord_831990).sum := by decide
  have hdescent : baseEnd_831990 < baseStart_831990 := by decide
  rcases family_descends (prefixWord ++ tailWord_831990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832037 : List Nat := [1, 3, 1, 2, 2, 1, 5, 3, 4]
def baseStart_832037 : Nat := 118140960795 + 832037 * 2 ^ 59
def prefixEnd_832037 : Nat := 4983230072969 + 3 ^ 40 * 832037 * 2
def baseEnd_832037 : Nat := 94941089627792530024675

theorem tailTrace_832037 : CollatzResearch.WordTrace tailWord_832037 prefixEnd_832037 94941089627792530024675 := by
  unfold tailWord_832037
  simp only [CollatzResearch.WordTrace]
  refine ⟨30346882486679524451502365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20231254991119682967668243 30346882486679524451502365)
  ·
    refine ⟨11380080932504821669313387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30346882486679524451502365 11380080932504821669313387)
    ·
      refine ⟨17070121398757232503970081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11380080932504821669313387 17070121398757232503970081)
      ·
        refine ⟨12802591049067924377977561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17070121398757232503970081 12802591049067924377977561)
        ·
          refine ⟨9601943286800943283483171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12802591049067924377977561 9601943286800943283483171)
          ·
            refine ⟨14402914930201414925224757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9601943286800943283483171 14402914930201414925224757)
            ·
              refine ⟨1350273274706382649239821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14402914930201414925224757 1350273274706382649239821)
              ·
                refine ⟨506352478014893493464933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1350273274706382649239821 506352478014893493464933)
                ·
                  refine ⟨94941089627792530024675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 506352478014893493464933 94941089627792530024675)
                  ·
                    rfl

theorem cell22_832037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 5, 3, 4].length) (baseStart_832037 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832037 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832037 prefixEnd_832037 := by exact prefixLift 832037
  have htrace : WordTrace (prefixWord ++ tailWord_832037) baseStart_832037 baseEnd_832037 := by
    simpa [prefixWord, tailWord_832037, baseEnd_832037] using wordTrace_append hprefix tailTrace_832037
  have hstable : (prefixWord ++ tailWord_832037).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832037).length < 2 ^ (prefixWord ++ tailWord_832037).sum := by decide
  have hdescent : baseEnd_832037 < baseStart_832037 := by decide
  rcases family_descends (prefixWord ++ tailWord_832037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832048 : List Nat := [2, 1, 1, 1, 2, 3, 12]
def baseStart_832048 : Nat := 118140960795 + 832048 * 2 ^ 59
def prefixEnd_832048 : Nat := 4983230072969 + 3 ^ 40 * 832048 * 2
def baseEnd_832048 : Nat := 10549149422525082520333

theorem tailTrace_832048 : CollatzResearch.WordTrace tailWord_832048 prefixEnd_832048 10549149422525082520333 := by
  unfold tailWord_832048
  simp only [CollatzResearch.WordTrace]
  refine ⟨15173641844819836665076399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20231522459759782220101865 15173641844819836665076399)
  ·
    refine ⟨22760462767229754997614599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15173641844819836665076399 22760462767229754997614599)
    ·
      refine ⟨34140694150844632496421899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22760462767229754997614599 34140694150844632496421899)
      ·
        refine ⟨51211041226266948744632849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34140694150844632496421899 51211041226266948744632849)
        ·
          refine ⟨38408280919700211558474637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51211041226266948744632849 38408280919700211558474637)
          ·
            refine ⟨14403105344887579334427989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38408280919700211558474637 14403105344887579334427989)
            ·
              refine ⟨10549149422525082520333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 14403105344887579334427989 10549149422525082520333)
              ·
                rfl

theorem cell22_832048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 12].length) (baseStart_832048 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832048 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832048 prefixEnd_832048 := by exact prefixLift 832048
  have htrace : WordTrace (prefixWord ++ tailWord_832048) baseStart_832048 baseEnd_832048 := by
    simpa [prefixWord, tailWord_832048, baseEnd_832048] using wordTrace_append hprefix tailTrace_832048
  have hstable : (prefixWord ++ tailWord_832048).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832048).length < 2 ^ (prefixWord ++ tailWord_832048).sum := by decide
  have hdescent : baseEnd_832048 < baseStart_832048 := by decide
  rcases family_descends (prefixWord ++ tailWord_832048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832050 : List Nat := [3, 2, 1, 1, 2, 1, 3, 1, 4, 4]
def baseStart_832050 : Nat := 118140960795 + 832050 * 2 ^ 59
def prefixEnd_832050 : Nat := 4983230072969 + 3 ^ 40 * 832050 * 2
def baseEnd_832050 : Nat := 284827719049049889498985

theorem tailTrace_832050 : CollatzResearch.WordTrace tailWord_832050 prefixEnd_832050 284827719049049889498985 := by
  unfold tailWord_832050
  simp only [CollatzResearch.WordTrace]
  refine ⟨7586839158908106917931401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20231571090421618447817069 7586839158908106917931401)
  ·
    refine ⟨5690129369181080188448551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7586839158908106917931401 5690129369181080188448551)
    ·
      refine ⟨8535194053771620282672827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5690129369181080188448551 8535194053771620282672827)
      ·
        refine ⟨12802791080657430424009241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8535194053771620282672827 12802791080657430424009241)
        ·
          refine ⟨9602093310493072818006931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12802791080657430424009241 9602093310493072818006931)
          ·
            refine ⟨14403139965739609227010397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9602093310493072818006931 14403139965739609227010397)
            ·
              refine ⟨5401177487152353460128899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14403139965739609227010397 5401177487152353460128899)
              ·
                refine ⟨8101766230728530190193349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5401177487152353460128899 8101766230728530190193349)
                ·
                  refine ⟨1519081168261599410661253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8101766230728530190193349 1519081168261599410661253)
                  ·
                    refine ⟨284827719049049889498985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1519081168261599410661253 284827719049049889498985)
                    ·
                      rfl

theorem cell22_832050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 3, 1, 4, 4].length) (baseStart_832050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832050 prefixEnd_832050 := by exact prefixLift 832050
  have htrace : WordTrace (prefixWord ++ tailWord_832050) baseStart_832050 baseEnd_832050 := by
    simpa [prefixWord, tailWord_832050, baseEnd_832050] using wordTrace_append hprefix tailTrace_832050
  have hstable : (prefixWord ++ tailWord_832050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832050).length < 2 ^ (prefixWord ++ tailWord_832050).sum := by decide
  have hdescent : baseEnd_832050 < baseStart_832050 := by decide
  rcases family_descends (prefixWord ++ tailWord_832050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832054 : List Nat := [5, 1, 2, 1, 2, 3, 1, 1, 6]
def baseStart_832054 : Nat := 118140960795 + 832054 * 2 ^ 59
def prefixEnd_832054 : Nat := 4983230072969 + 3 ^ 40 * 832054 * 2
def baseEnd_832054 : Nat := 94943029443598404132991

theorem tailTrace_832054 : CollatzResearch.WordTrace tailWord_832054 prefixEnd_832054 94943029443598404132991 := by
  unfold tailWord_832054
  simp only [CollatzResearch.WordTrace]
  refine ⟨1896718907976121022179451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20231668351745290903247477 1896718907976121022179451)
  ·
    refine ⟨2845078361964181533269177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1896718907976121022179451 2845078361964181533269177)
    ·
      refine ⟨2133808771473136149951883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2845078361964181533269177 2133808771473136149951883)
      ·
        refine ⟨3200713157209704224927825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2133808771473136149951883 3200713157209704224927825)
        ·
          refine ⟨2400534867907278168695869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3200713157209704224927825 2400534867907278168695869)
          ·
            refine ⟨900200575465229313260951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2400534867907278168695869 900200575465229313260951)
            ·
              refine ⟨1350300863197843969891427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 900200575465229313260951 1350300863197843969891427)
              ·
                refine ⟨2025451294796765954837141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1350300863197843969891427 2025451294796765954837141)
                ·
                  refine ⟨94943029443598404132991, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2025451294796765954837141 94943029443598404132991)
                  ·
                    rfl

theorem cell22_832054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_832054 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832054 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832054 prefixEnd_832054 := by exact prefixLift 832054
  have htrace : WordTrace (prefixWord ++ tailWord_832054) baseStart_832054 baseEnd_832054 := by
    simpa [prefixWord, tailWord_832054, baseEnd_832054] using wordTrace_append hprefix tailTrace_832054
  have hstable : (prefixWord ++ tailWord_832054).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832054).length < 2 ^ (prefixWord ++ tailWord_832054).sum := by decide
  have hdescent : baseEnd_832054 < baseStart_832054 := by decide
  rcases family_descends (prefixWord ++ tailWord_832054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832065 : List Nat := [1, 2, 5, 1, 1, 2, 1, 9]
def baseStart_832065 : Nat := 118140960795 + 832065 * 2 ^ 59
def prefixEnd_832065 : Nat := 4983230072969 + 3 ^ 40 * 832065 * 2
def baseEnd_832065 : Nat := 31648094872843872263771

theorem tailTrace_832065 : CollatzResearch.WordTrace tailWord_832065 prefixEnd_832065 31648094872843872263771 := by
  unfold tailWord_832065
  simp only [CollatzResearch.WordTrace]
  refine ⟨30347903730578085233521649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20231935820385390155681099 30347903730578085233521649)
  ·
    refine ⟨22760927797933563925141237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30347903730578085233521649 22760927797933563925141237)
    ·
      refine ⟨2133836981056271617981991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22760927797933563925141237 2133836981056271617981991)
      ·
        refine ⟨3200755471584407426972987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2133836981056271617981991 3200755471584407426972987)
        ·
          refine ⟨4801133207376611140459481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3200755471584407426972987 4801133207376611140459481)
          ·
            refine ⟨3600849905532458355344611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4801133207376611140459481 3600849905532458355344611)
            ·
              refine ⟨5401274858298687533016917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3600849905532458355344611 5401274858298687533016917)
              ·
                refine ⟨31648094872843872263771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5401274858298687533016917 31648094872843872263771)
                ·
                  rfl

theorem cell22_832065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 1, 9].length) (baseStart_832065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832065 prefixEnd_832065 := by exact prefixLift 832065
  have htrace : WordTrace (prefixWord ++ tailWord_832065) baseStart_832065 baseEnd_832065 := by
    simpa [prefixWord, tailWord_832065, baseEnd_832065] using wordTrace_append hprefix tailTrace_832065
  have hstable : (prefixWord ++ tailWord_832065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832065).length < 2 ^ (prefixWord ++ tailWord_832065).sum := by decide
  have hdescent : baseEnd_832065 < baseStart_832065 := by decide
  rcases family_descends (prefixWord ++ tailWord_832065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832069 : List Nat := [1, 3, 1, 1, 1, 5, 4, 1, 2, 3]
def baseStart_832069 : Nat := 118140960795 + 832069 * 2 ^ 59
def prefixEnd_832069 : Nat := 4983230072969 + 3 ^ 40 * 832069 * 2
def baseEnd_832069 : Nat := 284834223137340173273927

theorem tailTrace_832069 : CollatzResearch.WordTrace tailWord_832069 prefixEnd_832069 284834223137340173273927 := by
  unfold tailWord_832069
  simp only [CollatzResearch.WordTrace]
  refine ⟨30348049622563593916667261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20232033081709062611111507 30348049622563593916667261)
  ·
    refine ⟨11380518608461347718750223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30348049622563593916667261 11380518608461347718750223)
    ·
      refine ⟨17070777912692021578125335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11380518608461347718750223 17070777912692021578125335)
      ·
        refine ⟨25606166869038032367188003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17070777912692021578125335 25606166869038032367188003)
        ·
          refine ⟨38409250303557048550782005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25606166869038032367188003 38409250303557048550782005)
          ·
            refine ⟨3600867215958473301635813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38409250303557048550782005 3600867215958473301635813)
            ·
              refine ⟨675162602992213744056715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3600867215958473301635813 675162602992213744056715)
              ·
                refine ⟨1012743904488320616085073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675162602992213744056715 1012743904488320616085073)
                ·
                  refine ⟨759557928366240462063805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1012743904488320616085073 759557928366240462063805)
                  ·
                    refine ⟨284834223137340173273927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 759557928366240462063805 284834223137340173273927)
                    ·
                      rfl

theorem cell22_832069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 4, 1, 2, 3].length) (baseStart_832069 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832069 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832069 prefixEnd_832069 := by exact prefixLift 832069
  have htrace : WordTrace (prefixWord ++ tailWord_832069) baseStart_832069 baseEnd_832069 := by
    simpa [prefixWord, tailWord_832069, baseEnd_832069] using wordTrace_append hprefix tailTrace_832069
  have hstable : (prefixWord ++ tailWord_832069).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832069).length < 2 ^ (prefixWord ++ tailWord_832069).sum := by decide
  have hdescent : baseEnd_832069 < baseStart_832069 := by decide
  rcases family_descends (prefixWord ++ tailWord_832069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832148 : List Nat := [2, 4, 2, 2, 1, 2, 2, 3, 1, 3]
def baseStart_832148 : Nat := 118140960795 + 832148 * 2 ^ 59
def prefixEnd_832148 : Nat := 4983230072969 + 3 ^ 40 * 832148 * 2
def baseEnd_832148 : Nat := 284861266451810300548685

theorem tailTrace_832148 : CollatzResearch.WordTrace tailWord_832148 prefixEnd_832148 284861266451810300548685 := by
  unfold tailWord_832148
  simp only [CollatzResearch.WordTrace]
  refine ⟨15175465494638695204396549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20233953992851593605862065 15175465494638695204396549)
  ·
    refine ⟨2845399780244755350824353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15175465494638695204396549 2845399780244755350824353)
    ·
      refine ⟨2134049835183566513118265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2845399780244755350824353 2134049835183566513118265)
      ·
        refine ⟨1600537376387674884838699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2134049835183566513118265 1600537376387674884838699)
        ·
          refine ⟨2400806064581512327258049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1600537376387674884838699 2400806064581512327258049)
          ·
            refine ⟨1800604548436134245443537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2400806064581512327258049 1800604548436134245443537)
            ·
              refine ⟨1350453411327100684082653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1800604548436134245443537 1350453411327100684082653)
              ·
                refine ⟨506420029247662756530995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1350453411327100684082653 506420029247662756530995)
                ·
                  refine ⟨759630043871494134796493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 506420029247662756530995 759630043871494134796493)
                  ·
                    refine ⟨284861266451810300548685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 759630043871494134796493 284861266451810300548685)
                    ·
                      rfl

theorem cell22_832148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 2, 1, 2, 2, 3, 1, 3].length) (baseStart_832148 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832148 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832148 prefixEnd_832148 := by exact prefixLift 832148
  have htrace : WordTrace (prefixWord ++ tailWord_832148) baseStart_832148 baseEnd_832148 := by
    simpa [prefixWord, tailWord_832148, baseEnd_832148] using wordTrace_append hprefix tailTrace_832148
  have hstable : (prefixWord ++ tailWord_832148).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832148).length < 2 ^ (prefixWord ++ tailWord_832148).sum := by decide
  have hdescent : baseEnd_832148 < baseStart_832148 := by decide
  rcases family_descends (prefixWord ++ tailWord_832148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832161 : List Nat := [1, 2, 3, 3, 4, 1, 1, 2, 5]
def baseStart_832161 : Nat := 118140960795 + 832161 * 2 ^ 59
def prefixEnd_832161 : Nat := 4983230072969 + 3 ^ 40 * 832161 * 2
def baseEnd_832161 : Nat := 94955238872494199991215

theorem tailTrace_832161 : CollatzResearch.WordTrace tailWord_832161 prefixEnd_832161 94955238872494199991215 := by
  unfold tailWord_832161
  simp only [CollatzResearch.WordTrace]
  refine ⟨30351405138230293629016337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20234270092153529086010891 30351405138230293629016337)
  ·
    refine ⟨22763553853672720221762253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30351405138230293629016337 22763553853672720221762253)
    ·
      refine ⟨8536332695127270083160845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22763553853672720221762253 8536332695127270083160845)
      ·
        refine ⟨3201124760672726281185317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8536332695127270083160845 3201124760672726281185317)
        ·
          refine ⟨600210892626136177722247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3201124760672726281185317 600210892626136177722247)
          ·
            refine ⟨900316338939204266583371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600210892626136177722247 900316338939204266583371)
            ·
              refine ⟨1350474508408806399875057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 900316338939204266583371 1350474508408806399875057)
              ·
                refine ⟨1012855881306604799906293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1350474508408806399875057 1012855881306604799906293)
                ·
                  refine ⟨94955238872494199991215, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1012855881306604799906293 94955238872494199991215)
                  ·
                    rfl

theorem cell22_832161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 4, 1, 1, 2, 5].length) (baseStart_832161 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832161 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832161 prefixEnd_832161 := by exact prefixLift 832161
  have htrace : WordTrace (prefixWord ++ tailWord_832161) baseStart_832161 baseEnd_832161 := by
    simpa [prefixWord, tailWord_832161, baseEnd_832161] using wordTrace_append hprefix tailTrace_832161
  have hstable : (prefixWord ++ tailWord_832161).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832161).length < 2 ^ (prefixWord ++ tailWord_832161).sum := by decide
  have hdescent : baseEnd_832161 < baseStart_832161 := by decide
  rcases family_descends (prefixWord ++ tailWord_832161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832202 : List Nat := [3, 1, 2, 1, 4, 1, 2, 1, 1, 6]
def baseStart_832202 : Nat := 118140960795 + 832202 * 2 ^ 59
def prefixEnd_832202 : Nat := 4983230072969 + 3 ^ 40 * 832202 * 2
def baseEnd_832202 : Nat := 284879751755372159698519

theorem tailTrace_832202 : CollatzResearch.WordTrace tailWord_832202 prefixEnd_832202 284879751755372159698519 := by
  unfold tailWord_832202
  simp only [CollatzResearch.WordTrace]
  refine ⟨7588225132770439407814715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20235267020721171754172573 7588225132770439407814715)
  ·
    refine ⟨11382337699155659111722073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7588225132770439407814715 11382337699155659111722073)
    ·
      refine ⟨8536753274366744333791555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11382337699155659111722073 8536753274366744333791555)
      ·
        refine ⟨12805129911550116500687333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8536753274366744333791555 12805129911550116500687333)
        ·
          refine ⟨2400961858415646843878875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12805129911550116500687333 2400961858415646843878875)
          ·
            refine ⟨3601442787623470265818313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2400961858415646843878875 3601442787623470265818313)
            ·
              refine ⟨2701082090717602699363735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3601442787623470265818313 2701082090717602699363735)
              ·
                refine ⟨4051623136076404049045603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2701082090717602699363735 4051623136076404049045603)
                ·
                  refine ⟨6077434704114606073568405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4051623136076404049045603 6077434704114606073568405)
                  ·
                    refine ⟨284879751755372159698519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6077434704114606073568405 284879751755372159698519)
                    ·
                      rfl

theorem cell22_832202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 1, 2, 1, 1, 6].length) (baseStart_832202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832202 prefixEnd_832202 := by exact prefixLift 832202
  have htrace : WordTrace (prefixWord ++ tailWord_832202) baseStart_832202 baseEnd_832202 := by
    simpa [prefixWord, tailWord_832202, baseEnd_832202] using wordTrace_append hprefix tailTrace_832202
  have hstable : (prefixWord ++ tailWord_832202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832202).length < 2 ^ (prefixWord ++ tailWord_832202).sum := by decide
  have hdescent : baseEnd_832202 < baseStart_832202 := by decide
  rcases family_descends (prefixWord ++ tailWord_832202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832204 : List Nat := [2, 2, 1, 5, 1, 1, 1, 2, 4, 3]
def baseStart_832204 : Nat := 118140960795 + 832204 * 2 ^ 59
def prefixEnd_832204 : Nat := 4983230072969 + 3 ^ 40 * 832204 * 2
def baseEnd_832204 : Nat := 284880436396244821148513

theorem tailTrace_832204 : CollatzResearch.WordTrace tailWord_832204 prefixEnd_832204 284880436396244821148513 := by
  unfold tailWord_832204
  simp only [CollatzResearch.WordTrace]
  refine ⟨15176486738537255986415833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20235315651383007981887777 15176486738537255986415833)
  ·
    refine ⟨11382365053902941989811875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15176486738537255986415833 11382365053902941989811875)
    ·
      refine ⟨17073547580854412984717813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11382365053902941989811875 17073547580854412984717813)
      ·
        refine ⟨1600645085705101217317295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 17073547580854412984717813 1600645085705101217317295)
        ·
          refine ⟨2400967628557651825975943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1600645085705101217317295 2400967628557651825975943)
          ·
            refine ⟨3601451442836477738963915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2400967628557651825975943 3601451442836477738963915)
            ·
              refine ⟨5402177164254716608445873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3601451442836477738963915 5402177164254716608445873)
              ·
                refine ⟨4051632873191037456334405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5402177164254716608445873 4051632873191037456334405)
                ·
                  refine ⟨759681163723319523062701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4051632873191037456334405 759681163723319523062701)
                  ·
                    refine ⟨284880436396244821148513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 759681163723319523062701 284880436396244821148513)
                    ·
                      rfl

theorem cell22_832204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 1, 1, 1, 2, 4, 3].length) (baseStart_832204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832204 prefixEnd_832204 := by exact prefixLift 832204
  have htrace : WordTrace (prefixWord ++ tailWord_832204) baseStart_832204 baseEnd_832204 := by
    simpa [prefixWord, tailWord_832204, baseEnd_832204] using wordTrace_append hprefix tailTrace_832204
  have hstable : (prefixWord ++ tailWord_832204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832204).length < 2 ^ (prefixWord ++ tailWord_832204).sum := by decide
  have hdescent : baseEnd_832204 < baseStart_832204 := by decide
  rcases family_descends (prefixWord ++ tailWord_832204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832206 : List Nat := [4, 1, 1, 1, 3, 4, 1, 3, 4]
def baseStart_832206 : Nat := 118140960795 + 832206 * 2 ^ 59
def prefixEnd_832206 : Nat := 4983230072969 + 3 ^ 40 * 832206 * 2
def baseEnd_832206 : Nat := 94960373679039160866169

theorem tailTrace_832206 : CollatzResearch.WordTrace tailWord_832206 prefixEnd_832206 94960373679039160866169 := by
  unfold tailWord_832206
  simp only [CollatzResearch.WordTrace]
  refine ⟨3794130802883408289300559, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20235364282044844209602981 3794130802883408289300559)
  ·
    refine ⟨5691196204325112433950839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3794130802883408289300559 5691196204325112433950839)
    ·
      refine ⟨8536794306487668650926259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5691196204325112433950839 8536794306487668650926259)
      ·
        refine ⟨12805191459731502976389389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8536794306487668650926259 12805191459731502976389389)
        ·
          refine ⟨4801946797399313616146021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12805191459731502976389389 4801946797399313616146021)
          ·
            refine ⟨900365024512371303027379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4801946797399313616146021 900365024512371303027379)
            ·
              refine ⟨1350547536768556954541069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 900365024512371303027379 1350547536768556954541069)
              ·
                refine ⟨506455326288208857952901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1350547536768556954541069 506455326288208857952901)
                ·
                  refine ⟨94960373679039160866169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 506455326288208857952901 94960373679039160866169)
                  ·
                    rfl

theorem cell22_832206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 4, 1, 3, 4].length) (baseStart_832206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832206 prefixEnd_832206 := by exact prefixLift 832206
  have htrace : WordTrace (prefixWord ++ tailWord_832206) baseStart_832206 baseEnd_832206 := by
    simpa [prefixWord, tailWord_832206, baseEnd_832206] using wordTrace_append hprefix tailTrace_832206
  have hstable : (prefixWord ++ tailWord_832206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832206).length < 2 ^ (prefixWord ++ tailWord_832206).sum := by decide
  have hdescent : baseEnd_832206 < baseStart_832206 := by decide
  rcases family_descends (prefixWord ++ tailWord_832206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832238 : List Nat := [4, 1, 2, 1, 1, 5, 2, 1, 2, 3]
def baseStart_832238 : Nat := 118140960795 + 832238 * 2 ^ 59
def prefixEnd_832238 : Nat := 4983230072969 + 3 ^ 40 * 832238 * 2
def baseEnd_832238 : Nat := 284892075291080065798409

theorem tailTrace_832238 : CollatzResearch.WordTrace tailWord_832238 prefixEnd_832238 284892075291080065798409 := by
  unfold tailWord_832238
  simp only [CollatzResearch.WordTrace]
  refine ⟨3794276694868916972446171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20236142372634223853046245 3794276694868916972446171)
  ·
    refine ⟨5691415042303375458669257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3794276694868916972446171 5691415042303375458669257)
    ·
      refine ⟨4268561281727531594001943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5691415042303375458669257 4268561281727531594001943)
      ·
        refine ⟨6402841922591297391002915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4268561281727531594001943 6402841922591297391002915)
        ·
          refine ⟨9604262883886946086504373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6402841922591297391002915 9604262883886946086504373)
          ·
            refine ⟨900399645364401195609785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9604262883886946086504373 900399645364401195609785)
            ·
              refine ⟨675299734023300896707339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 900399645364401195609785 675299734023300896707339)
              ·
                refine ⟨1012949601034951345061009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675299734023300896707339 1012949601034951345061009)
                ·
                  refine ⟨759712200776213508795757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1012949601034951345061009 759712200776213508795757)
                  ·
                    refine ⟨284892075291080065798409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 759712200776213508795757 284892075291080065798409)
                    ·
                      rfl

theorem cell22_832238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2, 1, 2, 3].length) (baseStart_832238 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832238 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832238 prefixEnd_832238 := by exact prefixLift 832238
  have htrace : WordTrace (prefixWord ++ tailWord_832238) baseStart_832238 baseEnd_832238 := by
    simpa [prefixWord, tailWord_832238, baseEnd_832238] using wordTrace_append hprefix tailTrace_832238
  have hstable : (prefixWord ++ tailWord_832238).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832238).length < 2 ^ (prefixWord ++ tailWord_832238).sum := by decide
  have hdescent : baseEnd_832238 < baseStart_832238 := by decide
  rcases family_descends (prefixWord ++ tailWord_832238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832266 : List Nat := [3, 1, 2, 2, 1, 2, 2, 5, 1, 3]
def baseStart_832266 : Nat := 118140960795 + 832266 * 2 ^ 59
def prefixEnd_832266 : Nat := 4983230072969 + 3 ^ 40 * 832266 * 2
def baseEnd_832266 : Nat := 284901660263297326098323

theorem tailTrace_832266 : CollatzResearch.WordTrace tailWord_832266 prefixEnd_832266 284901660263297326098323 := by
  unfold tailWord_832266
  simp only [CollatzResearch.WordTrace]
  refine ⟨7588808700712474140397163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20236823201899931041059101 7588808700712474140397163)
  ·
    refine ⟨11383213051068711210595745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7588808700712474140397163 11383213051068711210595745)
    ·
      refine ⟨8537409788301533407946809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11383213051068711210595745 8537409788301533407946809)
      ·
        refine ⟨6403057341226150055960107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8537409788301533407946809 6403057341226150055960107)
        ·
          refine ⟨9604586011839225083940161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6403057341226150055960107 9604586011839225083940161)
          ·
            refine ⟨7203439508879418812955121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9604586011839225083940161 7203439508879418812955121)
            ·
              refine ⟨5402579631659564109716341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7203439508879418812955121 5402579631659564109716341)
              ·
                refine ⟨506491840468084135285907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5402579631659564109716341 506491840468084135285907)
                ·
                  refine ⟨759737760702126202928861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 506491840468084135285907 759737760702126202928861)
                  ·
                    refine ⟨284901660263297326098323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 759737760702126202928861 284901660263297326098323)
                    ·
                      rfl

theorem cell22_832266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 2, 2, 5, 1, 3].length) (baseStart_832266 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832266 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832266 prefixEnd_832266 := by exact prefixLift 832266
  have htrace : WordTrace (prefixWord ++ tailWord_832266) baseStart_832266 baseEnd_832266 := by
    simpa [prefixWord, tailWord_832266, baseEnd_832266] using wordTrace_append hprefix tailTrace_832266
  have hstable : (prefixWord ++ tailWord_832266).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832266).length < 2 ^ (prefixWord ++ tailWord_832266).sum := by decide
  have hdescent : baseEnd_832266 < baseStart_832266 := by decide
  rcases family_descends (prefixWord ++ tailWord_832266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832277 : List Nat := [1, 3, 2, 1, 2, 2, 2, 2, 2, 5]
def baseStart_832277 : Nat := 118140960795 + 832277 * 2 ^ 59
def prefixEnd_832277 : Nat := 4983230072969 + 3 ^ 40 * 832277 * 2
def baseEnd_832277 : Nat := 284905425788096964073289

theorem tailTrace_832277 : CollatzResearch.WordTrace tailWord_832277 prefixEnd_832277 284905425788096964073289 := by
  unfold tailWord_832277
  simp only [CollatzResearch.WordTrace]
  refine ⟨30355636005810045440239085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20237090670540030293492723 30355636005810045440239085)
  ·
    refine ⟨11383363502178767040089657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30355636005810045440239085 11383363502178767040089657)
    ·
      refine ⟨8537522626634075280067243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11383363502178767040089657 8537522626634075280067243)
      ·
        refine ⟨12806283939951112920100865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8537522626634075280067243 12806283939951112920100865)
        ·
          refine ⟨9604712954963334690075649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12806283939951112920100865 9604712954963334690075649)
          ·
            refine ⟨7203534716222501017556737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9604712954963334690075649 7203534716222501017556737)
            ·
              refine ⟨5402651037166875763167553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7203534716222501017556737 5402651037166875763167553)
              ·
                refine ⟨4051988277875156822375665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5402651037166875763167553 4051988277875156822375665)
                ·
                  refine ⟨3038991208406367616781749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4051988277875156822375665 3038991208406367616781749)
                  ·
                    refine ⟨284905425788096964073289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3038991208406367616781749 284905425788096964073289)
                    ·
                      rfl

theorem cell22_832277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 2, 2, 5].length) (baseStart_832277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832277 prefixEnd_832277 := by exact prefixLift 832277
  have htrace : WordTrace (prefixWord ++ tailWord_832277) baseStart_832277 baseEnd_832277 := by
    simpa [prefixWord, tailWord_832277, baseEnd_832277] using wordTrace_append hprefix tailTrace_832277
  have hstable : (prefixWord ++ tailWord_832277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832277).length < 2 ^ (prefixWord ++ tailWord_832277).sum := by decide
  have hdescent : baseEnd_832277 < baseStart_832277 := by decide
  rcases family_descends (prefixWord ++ tailWord_832277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832307 : List Nat := [1, 1, 1, 2, 6, 1, 1, 1, 8]
def baseStart_832307 : Nat := 118140960795 + 832307 * 2 ^ 59
def prefixEnd_832307 : Nat := 4983230072969 + 3 ^ 40 * 832307 * 2
def baseEnd_832307 : Nat := 94971898467062295274399

theorem tailTrace_832307 : CollatzResearch.WordTrace tailWord_832307 prefixEnd_832307 94971898467062295274399 := by
  unfold tailWord_832307
  simp only [CollatzResearch.WordTrace]
  refine ⟨30356730195701360563831175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20237820130467573709220783 30356730195701360563831175)
  ·
    refine ⟨45535095293552040845746763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30356730195701360563831175 45535095293552040845746763)
    ·
      refine ⟨68302642940328061268620145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45535095293552040845746763 68302642940328061268620145)
      ·
        refine ⟨51226982205246045951465109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68302642940328061268620145 51226982205246045951465109)
        ·
          refine ⟨2401264790870908403974927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 51226982205246045951465109 2401264790870908403974927)
          ·
            refine ⟨3601897186306362605962391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2401264790870908403974927 3601897186306362605962391)
            ·
              refine ⟨5402845779459543908943587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3601897186306362605962391 5402845779459543908943587)
              ·
                refine ⟨8104268669189315863415381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5402845779459543908943587 8104268669189315863415381)
                ·
                  refine ⟨94971898467062295274399, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8104268669189315863415381 94971898467062295274399)
                  ·
                    rfl

theorem cell22_832307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 1, 8].length) (baseStart_832307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832307 prefixEnd_832307 := by exact prefixLift 832307
  have htrace : WordTrace (prefixWord ++ tailWord_832307) baseStart_832307 baseEnd_832307 := by
    simpa [prefixWord, tailWord_832307, baseEnd_832307] using wordTrace_append hprefix tailTrace_832307
  have hstable : (prefixWord ++ tailWord_832307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832307).length < 2 ^ (prefixWord ++ tailWord_832307).sum := by decide
  have hdescent : baseEnd_832307 < baseStart_832307 := by decide
  rcases family_descends (prefixWord ++ tailWord_832307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832309 : List Nat := [1, 3, 3, 1, 3, 1, 2, 1, 3, 4]
def baseStart_832309 : Nat := 118140960795 + 832309 * 2 ^ 59
def prefixEnd_832309 : Nat := 4983230072969 + 3 ^ 40 * 832309 * 2
def baseEnd_832309 : Nat := 284916380042059547273191

theorem tailTrace_832309 : CollatzResearch.WordTrace tailWord_832309 prefixEnd_832309 284916380042059547273191 := by
  unfold tailWord_832309
  simp only [CollatzResearch.WordTrace]
  refine ⟨30356803141694114905403981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20237868761129409936935987 30356803141694114905403981)
  ·
    refine ⟨11383801178135293089526493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30356803141694114905403981 11383801178135293089526493)
    ·
      refine ⟨4268925441800734908572435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11383801178135293089526493 4268925441800734908572435)
      ·
        refine ⟨6403388162701102362858653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4268925441800734908572435 6403388162701102362858653)
        ·
          refine ⟨2401270561012913386071995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6403388162701102362858653 2401270561012913386071995)
          ·
            refine ⟨3601905841519370079107993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2401270561012913386071995 3601905841519370079107993)
            ·
              refine ⟨2701429381139527559330995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3601905841519370079107993 2701429381139527559330995)
              ·
                refine ⟨4052144071709291338996493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2701429381139527559330995 4052144071709291338996493)
                ·
                  refine ⟨1519554026890984252123685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4052144071709291338996493 1519554026890984252123685)
                  ·
                    refine ⟨284916380042059547273191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1519554026890984252123685 284916380042059547273191)
                    ·
                      rfl

theorem cell22_832309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 1, 2, 1, 3, 4].length) (baseStart_832309 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832309 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832309 prefixEnd_832309 := by exact prefixLift 832309
  have htrace : WordTrace (prefixWord ++ tailWord_832309) baseStart_832309 baseEnd_832309 := by
    simpa [prefixWord, tailWord_832309, baseEnd_832309] using wordTrace_append hprefix tailTrace_832309
  have hstable : (prefixWord ++ tailWord_832309).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832309).length < 2 ^ (prefixWord ++ tailWord_832309).sum := by decide
  have hdescent : baseEnd_832309 < baseStart_832309 := by decide
  rcases family_descends (prefixWord ++ tailWord_832309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832352 : List Nat := [2, 1, 1, 3, 3, 1, 2, 9]
def baseStart_832352 : Nat := 118140960795 + 832352 * 2 ^ 59
def prefixEnd_832352 : Nat := 4983230072969 + 3 ^ 40 * 832352 * 2
def baseEnd_832352 : Nat := 31659011091202418716451

theorem tailTrace_832352 : CollatzResearch.WordTrace tailWord_832352 prefixEnd_832352 31659011091202418716451 := by
  unfold tailWord_832352
  simp only [CollatzResearch.WordTrace]
  refine ⟨15179185740269166624609655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20238914320358888832812873 15179185740269166624609655)
  ·
    refine ⟨22768778610403749936914483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15179185740269166624609655 22768778610403749936914483)
    ·
      refine ⟨34153167915605624905371725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22768778610403749936914483 34153167915605624905371725)
      ·
        refine ⟨12807437968352109339514397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34153167915605624905371725 12807437968352109339514397)
        ·
          refine ⟨4802789238132041002317899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12807437968352109339514397 4802789238132041002317899)
          ·
            refine ⟨7204183857198061503476849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4802789238132041002317899 7204183857198061503476849)
            ·
              refine ⟨5403137892898546127607637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7204183857198061503476849 5403137892898546127607637)
              ·
                refine ⟨31659011091202418716451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 5403137892898546127607637 31659011091202418716451)
                ·
                  rfl

theorem cell22_832352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 2, 9].length) (baseStart_832352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832352 prefixEnd_832352 := by exact prefixLift 832352
  have htrace : WordTrace (prefixWord ++ tailWord_832352) baseStart_832352 baseEnd_832352 := by
    simpa [prefixWord, tailWord_832352, baseEnd_832352] using wordTrace_append hprefix tailTrace_832352
  have hstable : (prefixWord ++ tailWord_832352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832352).length < 2 ^ (prefixWord ++ tailWord_832352).sum := by decide
  have hdescent : baseEnd_832352 < baseStart_832352 := by decide
  rcases family_descends (prefixWord ++ tailWord_832352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832356 : List Nat := [2, 3, 1, 1, 4, 3, 1, 1, 1, 5]
def baseStart_832356 : Nat := 118140960795 + 832356 * 2 ^ 59
def prefixEnd_832356 : Nat := 4983230072969 + 3 ^ 40 * 832356 * 2
def baseEnd_832356 : Nat := 284932469102567091348047

theorem tailTrace_832356 : CollatzResearch.WordTrace tailWord_832356 prefixEnd_832356 284932469102567091348047 := by
  unfold tailWord_832356
  simp only [CollatzResearch.WordTrace]
  refine ⟨15179258686261920966182461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20239011581682561288243281 15179258686261920966182461)
  ·
    refine ⟨5692222007348220362318423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15179258686261920966182461 5692222007348220362318423)
    ·
      refine ⟨8538333011022330543477635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5692222007348220362318423 8538333011022330543477635)
      ·
        refine ⟨12807499516533495815216453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8538333011022330543477635 12807499516533495815216453)
        ·
          refine ⟨2401406159350030465353085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12807499516533495815216453 2401406159350030465353085)
          ·
            refine ⟨900527309756261424507407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2401406159350030465353085 900527309756261424507407)
            ·
              refine ⟨1350790964634392136761111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 900527309756261424507407 1350790964634392136761111)
              ·
                refine ⟨2026186446951588205141667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1350790964634392136761111 2026186446951588205141667)
                ·
                  refine ⟨3039279670427382307712501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2026186446951588205141667 3039279670427382307712501)
                  ·
                    refine ⟨284932469102567091348047, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3039279670427382307712501 284932469102567091348047)
                    ·
                      rfl

theorem cell22_832356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 3, 1, 1, 1, 5].length) (baseStart_832356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832356 prefixEnd_832356 := by exact prefixLift 832356
  have htrace : WordTrace (prefixWord ++ tailWord_832356) baseStart_832356 baseEnd_832356 := by
    simpa [prefixWord, tailWord_832356, baseEnd_832356] using wordTrace_append hprefix tailTrace_832356
  have hstable : (prefixWord ++ tailWord_832356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832356).length < 2 ^ (prefixWord ++ tailWord_832356).sum := by decide
  have hdescent : baseEnd_832356 < baseStart_832356 := by decide
  rcases family_descends (prefixWord ++ tailWord_832356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832369 : List Nat := [1, 2, 2, 2, 1, 4, 4, 6]
def baseStart_832369 : Nat := 118140960795 + 832369 * 2 ^ 59
def prefixEnd_832369 : Nat := 4983230072969 + 3 ^ 40 * 832369 * 2
def baseEnd_832369 : Nat := 31659657696471043419223

theorem tailTrace_832369 : CollatzResearch.WordTrace tailWord_832369 prefixEnd_832369 31659657696471043419223 := by
  unfold tailWord_832369
  simp only [CollatzResearch.WordTrace]
  refine ⟨30358991521476745152588161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20239327680984496768392107 30358991521476745152588161)
  ·
    refine ⟨22769243641107558864441121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30358991521476745152588161 22769243641107558864441121)
    ·
      refine ⟨17076932730830669148330841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22769243641107558864441121 17076932730830669148330841)
      ·
        refine ⟨12807699548123001861248131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17076932730830669148330841 12807699548123001861248131)
        ·
          refine ⟨19211549322184502791872197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12807699548123001861248131 19211549322184502791872197)
          ·
            refine ⟨3602165497909594273476037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19211549322184502791872197 3602165497909594273476037)
            ·
              refine ⟨675406030858048926276757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3602165497909594273476037 675406030858048926276757)
              ·
                refine ⟨31659657696471043419223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 675406030858048926276757 31659657696471043419223)
                ·
                  rfl

theorem cell22_832369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 4, 6].length) (baseStart_832369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832369 prefixEnd_832369 := by exact prefixLift 832369
  have htrace : WordTrace (prefixWord ++ tailWord_832369) baseStart_832369 baseEnd_832369 := by
    simpa [prefixWord, tailWord_832369, baseEnd_832369] using wordTrace_append hprefix tailTrace_832369
  have hstable : (prefixWord ++ tailWord_832369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832369).length < 2 ^ (prefixWord ++ tailWord_832369).sum := by decide
  have hdescent : baseEnd_832369 < baseStart_832369 := by decide
  rcases family_descends (prefixWord ++ tailWord_832369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832427 : List Nat := [1, 1, 1, 1, 2, 1, 1, 4, 2, 8]
def baseStart_832427 : Nat := 118140960795 + 832427 * 2 ^ 59
def prefixEnd_832427 : Nat := 4983230072969 + 3 ^ 40 * 832427 * 2
def baseEnd_832427 : Nat := 284956773853546572822829

theorem tailTrace_832427 : CollatzResearch.WordTrace tailWord_832427 prefixEnd_832427 284956773853546572822829 := by
  unfold tailWord_832427
  simp only [CollatzResearch.WordTrace]
  refine ⟨30361106955266621058199535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20240737970177747372133023 30361106955266621058199535)
  ·
    refine ⟨45541660432899931587299303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30361106955266621058199535 45541660432899931587299303)
    ·
      refine ⟨68312490649349897380948955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45541660432899931587299303 68312490649349897380948955)
      ·
        refine ⟨102468735974024846071423433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68312490649349897380948955 102468735974024846071423433)
        ·
          refine ⟨76851551980518634553567575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 102468735974024846071423433 76851551980518634553567575)
          ·
            refine ⟨115277327970777951830351363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 76851551980518634553567575 115277327970777951830351363)
            ·
              refine ⟨172915991956166927745527045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115277327970777951830351363 172915991956166927745527045)
              ·
                refine ⟨32421748491781298952286321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 172915991956166927745527045 32421748491781298952286321)
                ·
                  refine ⟨24316311368835974214214741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32421748491781298952286321 24316311368835974214214741)
                  ·
                    refine ⟨284956773853546572822829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 24316311368835974214214741 284956773853546572822829)
                    ·
                      rfl

theorem cell22_832427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 4, 2, 8].length) (baseStart_832427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832427 prefixEnd_832427 := by exact prefixLift 832427
  have htrace : WordTrace (prefixWord ++ tailWord_832427) baseStart_832427 baseEnd_832427 := by
    simpa [prefixWord, tailWord_832427, baseEnd_832427] using wordTrace_append hprefix tailTrace_832427
  have hstable : (prefixWord ++ tailWord_832427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832427).length < 2 ^ (prefixWord ++ tailWord_832427).sum := by decide
  have hdescent : baseEnd_832427 < baseStart_832427 := by decide
  rcases family_descends (prefixWord ++ tailWord_832427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832452 : List Nat := [2, 3, 3, 3, 1, 1, 1, 4, 1, 3]
def baseStart_832452 : Nat := 118140960795 + 832452 * 2 ^ 59
def prefixEnd_832452 : Nat := 4983230072969 + 3 ^ 40 * 832452 * 2
def baseEnd_832452 : Nat := 284965331864454840947753

theorem tailTrace_832452 : CollatzResearch.WordTrace tailWord_832452 prefixEnd_832452 284965331864454840947753 := by
  unfold tailWord_832452
  simp only [CollatzResearch.WordTrace]
  refine ⟨15181009390088025163929805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20241345853450700218573073 15181009390088025163929805)
  ·
    refine ⟨5692878521283009436473677, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15181009390088025163929805 5692878521283009436473677)
    ·
      refine ⟨2134829445481128538677629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5692878521283009436473677 2134829445481128538677629)
      ·
        refine ⟨800561042055423202004111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2134829445481128538677629 800561042055423202004111)
        ·
          refine ⟨1200841563083134803006167, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 800561042055423202004111 1200841563083134803006167)
          ·
            refine ⟨1801262344624702204509251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1200841563083134803006167 1801262344624702204509251)
            ·
              refine ⟨2701893516937053306763877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1801262344624702204509251 2701893516937053306763877)
              ·
                refine ⟨506605034425697495018227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2701893516937053306763877 506605034425697495018227)
                ·
                  refine ⟨759907551638546242527341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 506605034425697495018227 759907551638546242527341)
                  ·
                    refine ⟨284965331864454840947753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 759907551638546242527341 284965331864454840947753)
                    ·
                      rfl

theorem cell22_832452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 3, 1, 1, 1, 4, 1, 3].length) (baseStart_832452 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832452 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832452 prefixEnd_832452 := by exact prefixLift 832452
  have htrace : WordTrace (prefixWord ++ tailWord_832452) baseStart_832452 baseEnd_832452 := by
    simpa [prefixWord, tailWord_832452, baseEnd_832452] using wordTrace_append hprefix tailTrace_832452
  have hstable : (prefixWord ++ tailWord_832452).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832452).length < 2 ^ (prefixWord ++ tailWord_832452).sum := by decide
  have hdescent : baseEnd_832452 < baseStart_832452 := by decide
  rcases family_descends (prefixWord ++ tailWord_832452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832454 : List Nat := [6, 1, 3, 1, 2, 1, 1, 7]
def baseStart_832454 : Nat := 118140960795 + 832454 * 2 ^ 59
def prefixEnd_832454 : Nat := 4983230072969 + 3 ^ 40 * 832454 * 2
def baseEnd_832454 : Nat := 31662890722814166933083

theorem tailTrace_832454 : CollatzResearch.WordTrace tailWord_832454 prefixEnd_832454 31662890722814166933083 := by
  unfold tailWord_832454
  simp only [CollatzResearch.WordTrace]
  refine ⟨948815366442775145919763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 20241394484112536446288277 948815366442775145919763)
  ·
    refine ⟨1423223049664162718879645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 948815366442775145919763 1423223049664162718879645)
    ·
      refine ⟨533708643624061019579867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1423223049664162718879645 533708643624061019579867)
      ·
        refine ⟨800562965436091529369801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533708643624061019579867 800562965436091529369801)
        ·
          refine ⟨600422224077068647027351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 800562965436091529369801 600422224077068647027351)
          ·
            refine ⟨900633336115602970541027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 600422224077068647027351 900633336115602970541027)
            ·
              refine ⟨1350950004173404455811541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 900633336115602970541027 1350950004173404455811541)
              ·
                refine ⟨31662890722814166933083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1350950004173404455811541 31662890722814166933083)
                ·
                  rfl

theorem cell22_832454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 1, 1, 7].length) (baseStart_832454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832454 prefixEnd_832454 := by exact prefixLift 832454
  have htrace : WordTrace (prefixWord ++ tailWord_832454) baseStart_832454 baseEnd_832454 := by
    simpa [prefixWord, tailWord_832454, baseEnd_832454] using wordTrace_append hprefix tailTrace_832454
  have hstable : (prefixWord ++ tailWord_832454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832454).length < 2 ^ (prefixWord ++ tailWord_832454).sum := by decide
  have hdescent : baseEnd_832454 < baseStart_832454 := by decide
  rcases family_descends (prefixWord ++ tailWord_832454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832508 : List Nat := [2, 2, 2, 1, 2, 3, 3, 2, 2, 3]
def baseStart_832508 : Nat := 118140960795 + 832508 * 2 ^ 59
def prefixEnd_832508 : Nat := 4983230072969 + 3 ^ 40 * 832508 * 2
def baseEnd_832508 : Nat := 284984501808889361547581

theorem tailTrace_832508 : CollatzResearch.WordTrace tailWord_832508 prefixEnd_832508 284984501808889361547581 := by
  unfold tailWord_832508
  simp only [CollatzResearch.WordTrace]
  refine ⟨15182030633986585945949089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20242707511982114594598785 15182030633986585945949089)
  ·
    refine ⟨11386522975489939459461817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15182030633986585945949089 11386522975489939459461817)
    ·
      refine ⟨8539892231617454594596363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11386522975489939459461817 8539892231617454594596363)
      ·
        refine ⟨12809838347426181891894545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8539892231617454594596363 12809838347426181891894545)
        ·
          refine ⟨9607378760569636418920909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12809838347426181891894545 9607378760569636418920909)
          ·
            refine ⟨3602767035213613657095341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9607378760569636418920909 3602767035213613657095341)
            ·
              refine ⟨1351037638205105121410753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3602767035213613657095341 1351037638205105121410753)
              ·
                refine ⟨1013278228653828841058065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1351037638205105121410753 1013278228653828841058065)
                ·
                  refine ⟨759958671490371630793549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1013278228653828841058065 759958671490371630793549)
                  ·
                    refine ⟨284984501808889361547581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 759958671490371630793549 284984501808889361547581)
                    ·
                      rfl

theorem cell22_832508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 3, 3, 2, 2, 3].length) (baseStart_832508 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832508 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832508 prefixEnd_832508 := by exact prefixLift 832508
  have htrace : WordTrace (prefixWord ++ tailWord_832508) baseStart_832508 baseEnd_832508 := by
    simpa [prefixWord, tailWord_832508, baseEnd_832508] using wordTrace_append hprefix tailTrace_832508
  have hstable : (prefixWord ++ tailWord_832508).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832508).length < 2 ^ (prefixWord ++ tailWord_832508).sum := by decide
  have hdescent : baseEnd_832508 < baseStart_832508 := by decide
  rcases family_descends (prefixWord ++ tailWord_832508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832549 : List Nat := [1, 3, 1, 2, 2, 2, 1, 1, 9]
def baseStart_832549 : Nat := 118140960795 + 832549 * 2 ^ 59
def prefixEnd_832549 : Nat := 4983230072969 + 3 ^ 40 * 832549 * 2
def baseEnd_832549 : Nat := 94999512315592973757485

theorem tailTrace_832549 : CollatzResearch.WordTrace tailWord_832549 prefixEnd_832549 94999512315592973757485 := by
  unfold tailWord_832549
  simp only [CollatzResearch.WordTrace]
  refine ⟨30365556660824635894140701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20243704440549757262760467 30365556660824635894140701)
  ·
    refine ⟨11387083747809238460302763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30365556660824635894140701 11387083747809238460302763)
    ·
      refine ⟨17080625621713857690454145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11387083747809238460302763 17080625621713857690454145)
      ·
        refine ⟨12810469216285393267840609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17080625621713857690454145 12810469216285393267840609)
        ·
          refine ⟨9607851912214044950880457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12810469216285393267840609 9607851912214044950880457)
          ·
            refine ⟨7205888934160533713160343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9607851912214044950880457 7205888934160533713160343)
            ·
              refine ⟨10808833401240800569740515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7205888934160533713160343 10808833401240800569740515)
              ·
                refine ⟨16213250101861200854610773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10808833401240800569740515 16213250101861200854610773)
                ·
                  refine ⟨94999512315592973757485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16213250101861200854610773 94999512315592973757485)
                  ·
                    rfl

theorem cell22_832549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 9].length) (baseStart_832549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832549 prefixEnd_832549 := by exact prefixLift 832549
  have htrace : WordTrace (prefixWord ++ tailWord_832549) baseStart_832549 baseEnd_832549 := by
    simpa [prefixWord, tailWord_832549, baseEnd_832549] using wordTrace_append hprefix tailTrace_832549
  have hstable : (prefixWord ++ tailWord_832549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832549).length < 2 ^ (prefixWord ++ tailWord_832549).sum := by decide
  have hdescent : baseEnd_832549 < baseStart_832549 := by decide
  rcases family_descends (prefixWord ++ tailWord_832549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832583 : List Nat := [1, 1, 4, 1, 3, 2, 4, 1, 5]
def baseStart_832583 : Nat := 118140960795 + 832583 * 2 ^ 59
def prefixEnd_832583 : Nat := 4983230072969 + 3 ^ 40 * 832583 * 2
def baseEnd_832583 : Nat := 95003391947204721974117

theorem tailTrace_832583 : CollatzResearch.WordTrace tailWord_832583 prefixEnd_832583 95003391947204721974117 := by
  unfold tailWord_832583
  simp only [CollatzResearch.WordTrace]
  refine ⟨30366796742701459700878403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20244531161800973133918935 30366796742701459700878403)
  ·
    refine ⟨45550195114052189551317605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30366796742701459700878403 45550195114052189551317605)
    ·
      refine ⟨8540661583884785540872051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45550195114052189551317605 8540661583884785540872051)
      ·
        refine ⟨12810992375827178311308077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8540661583884785540872051 12810992375827178311308077)
        ·
          refine ⟨4804122140935191866740529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12810992375827178311308077 4804122140935191866740529)
          ·
            refine ⟨3603091605701393900055397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4804122140935191866740529 3603091605701393900055397)
            ·
              refine ⟨675579676069011356260387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3603091605701393900055397 675579676069011356260387)
              ·
                refine ⟨1013369514103517034390581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675579676069011356260387 1013369514103517034390581)
                ·
                  refine ⟨95003391947204721974117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1013369514103517034390581 95003391947204721974117)
                  ·
                    rfl

theorem cell22_832583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 4, 1, 5].length) (baseStart_832583 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832583 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832583 prefixEnd_832583 := by exact prefixLift 832583
  have htrace : WordTrace (prefixWord ++ tailWord_832583) baseStart_832583 baseEnd_832583 := by
    simpa [prefixWord, tailWord_832583, baseEnd_832583] using wordTrace_append hprefix tailTrace_832583
  have hstable : (prefixWord ++ tailWord_832583).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832583).length < 2 ^ (prefixWord ++ tailWord_832583).sum := by decide
  have hdescent : baseEnd_832583 < baseStart_832583 := by decide
  rcases family_descends (prefixWord ++ tailWord_832583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832626 : List Nat := [3, 2, 1, 2, 2, 1, 1, 2, 3, 5]
def baseStart_832626 : Nat := 118140960795 + 832626 * 2 ^ 59
def prefixEnd_832626 : Nat := 4983230072969 + 3 ^ 40 * 832626 * 2
def baseEnd_832626 : Nat := 285024895620376387097219

theorem tailTrace_832626 : CollatzResearch.WordTrace tailWord_832626 prefixEnd_832626 285024895620376387097219 := by
  unfold tailWord_832626
  simp only [CollatzResearch.WordTrace]
  refine ⟨7592091270386419511173433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20245576721030452029795821 7592091270386419511173433)
  ·
    refine ⟨5694068452789814633380075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7592091270386419511173433 5694068452789814633380075)
    ·
      refine ⟨8541102679184721950070113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5694068452789814633380075 8541102679184721950070113)
      ·
        refine ⟨6405827009388541462552585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8541102679184721950070113 6405827009388541462552585)
        ·
          refine ⟨4804370257041406096914439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6405827009388541462552585 4804370257041406096914439)
          ·
            refine ⟨7206555385562109145371659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4804370257041406096914439 7206555385562109145371659)
            ·
              refine ⟨10809833078343163718057489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7206555385562109145371659 10809833078343163718057489)
              ·
                refine ⟨8107374808757372788543117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10809833078343163718057489 8107374808757372788543117)
                ·
                  refine ⟨3040265553284014795703669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8107374808757372788543117 3040265553284014795703669)
                  ·
                    refine ⟨285024895620376387097219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3040265553284014795703669 285024895620376387097219)
                    ·
                      rfl

theorem cell22_832626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 1, 2, 3, 5].length) (baseStart_832626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832626 prefixEnd_832626 := by exact prefixLift 832626
  have htrace : WordTrace (prefixWord ++ tailWord_832626) baseStart_832626 baseEnd_832626 := by
    simpa [prefixWord, tailWord_832626, baseEnd_832626] using wordTrace_append hprefix tailTrace_832626
  have hstable : (prefixWord ++ tailWord_832626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832626).length < 2 ^ (prefixWord ++ tailWord_832626).sum := by decide
  have hdescent : baseEnd_832626 < baseStart_832626 := by decide
  rcases family_descends (prefixWord ++ tailWord_832626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832643 : List Nat := [1, 1, 1, 3, 3, 2, 1, 5, 2, 3]
def baseStart_832643 : Nat := 118140960795 + 832643 * 2 ^ 59
def prefixEnd_832643 : Nat := 4983230072969 + 3 ^ 40 * 832643 * 2
def baseEnd_832643 : Nat := 285030715067794009422167

theorem tailTrace_832643 : CollatzResearch.WordTrace tailWord_832643 prefixEnd_832643 285030715067794009422167 := by
  unfold tailWord_832643
  simp only [CollatzResearch.WordTrace]
  refine ⟨30368985122484089948062583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20245990081656059965375055 30368985122484089948062583)
  ·
    refine ⟨45553477683726134922093875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30368985122484089948062583 45553477683726134922093875)
    ·
      refine ⟨68330216525589202383140813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45553477683726134922093875 68330216525589202383140813)
      ·
        refine ⟨25623831197095950893677805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68330216525589202383140813 25623831197095950893677805)
        ·
          refine ⟨9608936698910981585129177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25623831197095950893677805 9608936698910981585129177)
          ·
            refine ⟨7206702524183236188846883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9608936698910981585129177 7206702524183236188846883)
            ·
              refine ⟨10810053786274854283270325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7206702524183236188846883 10810053786274854283270325)
              ·
                refine ⟨1013442542463267589056593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10810053786274854283270325 1013442542463267589056593)
                ·
                  refine ⟨760081906847450691792445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1013442542463267589056593 760081906847450691792445)
                  ·
                    refine ⟨285030715067794009422167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 760081906847450691792445 285030715067794009422167)
                    ·
                      rfl

theorem cell22_832643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 1, 5, 2, 3].length) (baseStart_832643 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832643 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832643 prefixEnd_832643 := by exact prefixLift 832643
  have htrace : WordTrace (prefixWord ++ tailWord_832643) baseStart_832643 baseEnd_832643 := by
    simpa [prefixWord, tailWord_832643, baseEnd_832643] using wordTrace_append hprefix tailTrace_832643
  have hstable : (prefixWord ++ tailWord_832643).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832643).length < 2 ^ (prefixWord ++ tailWord_832643).sum := by decide
  have hdescent : baseEnd_832643 < baseStart_832643 := by decide
  rcases family_descends (prefixWord ++ tailWord_832643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832658 : List Nat := [3, 2, 3, 1, 1, 3, 1, 1, 1, 6]
def baseStart_832658 : Nat := 118140960795 + 832658 * 2 ^ 59
def prefixEnd_832658 : Nat := 4983230072969 + 3 ^ 40 * 832658 * 2
def baseEnd_832658 : Nat := 285035849874338970297121

theorem tailTrace_832658 : CollatzResearch.WordTrace tailWord_832658 prefixEnd_832658 285035849874338970297121 := by
  unfold tailWord_832658
  simp only [CollatzResearch.WordTrace]
  refine ⟨7592383054357436877464657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20246354811619831673239085 7592383054357436877464657)
  ·
    refine ⟨5694287290768077658098493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7592383054357436877464657 5694287290768077658098493)
    ·
      refine ⟨2135357734038029121786935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5694287290768077658098493 2135357734038029121786935)
      ·
        refine ⟨3203036601057043682680403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2135357734038029121786935 3203036601057043682680403)
        ·
          refine ⟨4804554901585565524020605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3203036601057043682680403 4804554901585565524020605)
          ·
            refine ⟨1801708088094587071507727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4804554901585565524020605 1801708088094587071507727)
            ·
              refine ⟨2702562132141880607261591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1801708088094587071507727 2702562132141880607261591)
              ·
                refine ⟨4053843198212820910892387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2702562132141880607261591 4053843198212820910892387)
                ·
                  refine ⟨6080764797319231366338581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4053843198212820910892387 6080764797319231366338581)
                  ·
                    refine ⟨285035849874338970297121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6080764797319231366338581 285035849874338970297121)
                    ·
                      rfl

theorem cell22_832658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 3, 1, 1, 1, 6].length) (baseStart_832658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832658 prefixEnd_832658 := by exact prefixLift 832658
  have htrace : WordTrace (prefixWord ++ tailWord_832658) baseStart_832658 baseEnd_832658 := by
    simpa [prefixWord, tailWord_832658, baseEnd_832658] using wordTrace_append hprefix tailTrace_832658
  have hstable : (prefixWord ++ tailWord_832658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832658).length < 2 ^ (prefixWord ++ tailWord_832658).sum := by decide
  have hdescent : baseEnd_832658 < baseStart_832658 := by decide
  rcases family_descends (prefixWord ++ tailWord_832658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832694 : List Nat := [5, 1, 3, 2, 1, 2, 1, 1, 1, 5]
def baseStart_832694 : Nat := 118140960795 + 832694 * 2 ^ 59
def prefixEnd_832694 : Nat := 4983230072969 + 3 ^ 40 * 832694 * 2
def baseEnd_832694 : Nat := 285048173410046876397011

theorem tailTrace_832694 : CollatzResearch.WordTrace tailWord_832694 prefixEnd_832694 285048173410046876397011 := by
  unfold tailWord_832694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1898177827831207853635571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20247230163532883772112757 1898177827831207853635571)
  ·
    refine ⟨2847266741746811780453357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1898177827831207853635571 2847266741746811780453357)
    ·
      refine ⟨1067725028155054417670009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2847266741746811780453357 1067725028155054417670009)
      ·
        refine ⟨800793771116290813252507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1067725028155054417670009 800793771116290813252507)
        ·
          refine ⟨1201190656674436219878761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 800793771116290813252507 1201190656674436219878761)
          ·
            refine ⟨900892992505827164909071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1201190656674436219878761 900892992505827164909071)
            ·
              refine ⟨1351339488758740747363607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 900892992505827164909071 1351339488758740747363607)
              ·
                refine ⟨2027009233138111121045411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1351339488758740747363607 2027009233138111121045411)
                ·
                  refine ⟨3040513849707166681568117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2027009233138111121045411 3040513849707166681568117)
                  ·
                    refine ⟨285048173410046876397011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3040513849707166681568117 285048173410046876397011)
                    ·
                      rfl

theorem cell22_832694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 2, 1, 2, 1, 1, 1, 5].length) (baseStart_832694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832694 prefixEnd_832694 := by exact prefixLift 832694
  have htrace : WordTrace (prefixWord ++ tailWord_832694) baseStart_832694 baseEnd_832694 := by
    simpa [prefixWord, tailWord_832694, baseEnd_832694] using wordTrace_append hprefix tailTrace_832694
  have hstable : (prefixWord ++ tailWord_832694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832694).length < 2 ^ (prefixWord ++ tailWord_832694).sum := by decide
  have hdescent : baseEnd_832694 < baseStart_832694 := by decide
  rcases family_descends (prefixWord ++ tailWord_832694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832782 : List Nat := [4, 1, 1, 2, 1, 4, 3, 1, 1, 4]
def baseStart_832782 : Nat := 118140960795 + 832782 * 2 ^ 59
def prefixEnd_832782 : Nat := 4983230072969 + 3 ^ 40 * 832782 * 2
def baseEnd_832782 : Nat := 285078297608443980196741

theorem tailTrace_832782 : CollatzResearch.WordTrace tailWord_832782 prefixEnd_832782 285078297608443980196741 := by
  unfold tailWord_832782
  simp only [CollatzResearch.WordTrace]
  refine ⟨3796756858622564585921575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20249369912653677791581733 3796756858622564585921575)
  ·
    refine ⟨5695135287933846878882363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3796756858622564585921575 5695135287933846878882363)
    ·
      refine ⟨8542702931900770318323545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5695135287933846878882363 8542702931900770318323545)
      ·
        refine ⟨6407027198925577738742659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8542702931900770318323545 6407027198925577738742659)
        ·
          refine ⟨9610540798388366608113989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6407027198925577738742659 9610540798388366608113989)
          ·
            refine ⟨1801976399697818739021373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9610540798388366608113989 1801976399697818739021373)
            ·
              refine ⟨675741149886682027133015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1801976399697818739021373 675741149886682027133015)
              ·
                refine ⟨1013611724830023040699523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675741149886682027133015 1013611724830023040699523)
                ·
                  refine ⟨1520417587245034561049285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1013611724830023040699523 1520417587245034561049285)
                  ·
                    refine ⟨285078297608443980196741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1520417587245034561049285 285078297608443980196741)
                    ·
                      rfl

theorem cell22_832782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 3, 1, 1, 4].length) (baseStart_832782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832782 prefixEnd_832782 := by exact prefixLift 832782
  have htrace : WordTrace (prefixWord ++ tailWord_832782) baseStart_832782 baseEnd_832782 := by
    simpa [prefixWord, tailWord_832782, baseEnd_832782] using wordTrace_append hprefix tailTrace_832782
  have hstable : (prefixWord ++ tailWord_832782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832782).length < 2 ^ (prefixWord ++ tailWord_832782).sum := by decide
  have hdescent : baseEnd_832782 < baseStart_832782 := by decide
  rcases family_descends (prefixWord ++ tailWord_832782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832797 : List Nat := [1, 4, 2, 3, 1, 2, 1, 4, 4]
def baseStart_832797 : Nat := 118140960795 + 832797 * 2 ^ 59
def prefixEnd_832797 : Nat := 4983230072969 + 3 ^ 40 * 832797 * 2
def baseEnd_832797 : Nat := 95027810804996313690565

theorem tailTrace_832797 : CollatzResearch.WordTrace tailWord_832797 prefixEnd_832797 95027810804996313690565 := by
  unfold tailWord_832797
  simp only [CollatzResearch.WordTrace]
  refine ⟨30374601963926174249168645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20249734642617449499445763 30374601963926174249168645)
  ·
    refine ⟨5695237868236157671719121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30374601963926174249168645 5695237868236157671719121)
    ·
      refine ⟨4271428401177118253789341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5695237868236157671719121 4271428401177118253789341)
      ·
        refine ⟨1601785650441419345171003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4271428401177118253789341 1601785650441419345171003)
        ·
          refine ⟨2402678475662129017756505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1601785650441419345171003 2402678475662129017756505)
          ·
            refine ⟨1802008856746596763317379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2402678475662129017756505 1802008856746596763317379)
            ·
              refine ⟨2703013285119895144976069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1802008856746596763317379 2703013285119895144976069)
              ·
                refine ⟨506814990959980339683013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2703013285119895144976069 506814990959980339683013)
                ·
                  refine ⟨95027810804996313690565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 506814990959980339683013 95027810804996313690565)
                  ·
                    rfl

theorem cell22_832797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 2, 1, 4, 4].length) (baseStart_832797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832797 prefixEnd_832797 := by exact prefixLift 832797
  have htrace : WordTrace (prefixWord ++ tailWord_832797) baseStart_832797 baseEnd_832797 := by
    simpa [prefixWord, tailWord_832797, baseEnd_832797] using wordTrace_append hprefix tailTrace_832797
  have hstable : (prefixWord ++ tailWord_832797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832797).length < 2 ^ (prefixWord ++ tailWord_832797).sum := by decide
  have hdescent : baseEnd_832797 < baseStart_832797 := by decide
  rcases family_descends (prefixWord ++ tailWord_832797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832857 : List Nat := [1, 2, 1, 2, 2, 2, 4, 4, 1, 3]
def baseStart_832857 : Nat := 118140960795 + 832857 * 2 ^ 59
def prefixEnd_832857 : Nat := 4983230072969 + 3 ^ 40 * 832857 * 2
def baseEnd_832857 : Nat := 285103971641168784571511

theorem tailTrace_832857 : CollatzResearch.WordTrace tailWord_832857 prefixEnd_832857 285103971641168784571511 := by
  unfold tailWord_832857
  simp only [CollatzResearch.WordTrace]
  refine ⟨30376790343708804496352825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20251193562472536330901883 30376790343708804496352825)
  ·
    refine ⟨22782592757781603372264619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30376790343708804496352825 22782592757781603372264619)
    ·
      refine ⟨34173889136672405058396929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22782592757781603372264619 34173889136672405058396929)
      ·
        refine ⟨25630416852504303793797697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34173889136672405058396929 25630416852504303793797697)
        ·
          refine ⟨19222812639378227845348273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25630416852504303793797697 19222812639378227845348273)
          ·
            refine ⟨14417109479533670884011205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19222812639378227845348273 14417109479533670884011205)
            ·
              refine ⟨2703208027412563290752101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14417109479533670884011205 2703208027412563290752101)
              ·
                refine ⟨506851505139855617016019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2703208027412563290752101 506851505139855617016019)
                ·
                  refine ⟨760277257709783425524029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 506851505139855617016019 760277257709783425524029)
                  ·
                    refine ⟨285103971641168784571511, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 760277257709783425524029 285103971641168784571511)
                    ·
                      rfl

theorem cell22_832857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 4, 4, 1, 3].length) (baseStart_832857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832857 prefixEnd_832857 := by exact prefixLift 832857
  have htrace : WordTrace (prefixWord ++ tailWord_832857) baseStart_832857 baseEnd_832857 := by
    simpa [prefixWord, tailWord_832857, baseEnd_832857] using wordTrace_append hprefix tailTrace_832857
  have hstable : (prefixWord ++ tailWord_832857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832857).length < 2 ^ (prefixWord ++ tailWord_832857).sum := by decide
  have hdescent : baseEnd_832857 < baseStart_832857 := by decide
  rcases family_descends (prefixWord ++ tailWord_832857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832913 : List Nat := [1, 2, 2, 1, 1, 1, 2, 4, 3, 5]
def baseStart_832913 : Nat := 118140960795 + 832913 * 2 ^ 59
def prefixEnd_832913 : Nat := 4983230072969 + 3 ^ 40 * 832913 * 2
def baseEnd_832913 : Nat := 285123141585603305171339

theorem tailTrace_832913 : CollatzResearch.WordTrace tailWord_832913 prefixEnd_832913 285123141585603305171339 := by
  unfold tailWord_832913
  simp only [CollatzResearch.WordTrace]
  refine ⟨30378832831505926060391393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20252555221003950706927595 30378832831505926060391393)
  ·
    refine ⟨22784124623629444545293545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30378832831505926060391393 22784124623629444545293545)
    ·
      refine ⟨17088093467722083408970159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22784124623629444545293545 17088093467722083408970159)
      ·
        refine ⟨25632140201583125113455239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17088093467722083408970159 25632140201583125113455239)
        ·
          refine ⟨38448210302374687670182859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25632140201583125113455239 38448210302374687670182859)
          ·
            refine ⟨57672315453562031505274289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38448210302374687670182859 57672315453562031505274289)
            ·
              refine ⟨43254236590171523628955717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57672315453562031505274289 43254236590171523628955717)
              ·
                refine ⟨8110169360657160680429197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43254236590171523628955717 8110169360657160680429197)
                ·
                  refine ⟨3041313510246435255160949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8110169360657160680429197 3041313510246435255160949)
                  ·
                    refine ⟨285123141585603305171339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3041313510246435255160949 285123141585603305171339)
                    ·
                      rfl

theorem cell22_832913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 5].length) (baseStart_832913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832913 prefixEnd_832913 := by exact prefixLift 832913
  have htrace : WordTrace (prefixWord ++ tailWord_832913) baseStart_832913 baseEnd_832913 := by
    simpa [prefixWord, tailWord_832913, baseEnd_832913] using wordTrace_append hprefix tailTrace_832913
  have hstable : (prefixWord ++ tailWord_832913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832913).length < 2 ^ (prefixWord ++ tailWord_832913).sum := by decide
  have hdescent : baseEnd_832913 < baseStart_832913 := by decide
  rcases family_descends (prefixWord ++ tailWord_832913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_832964 : List Nat := [2, 3, 3, 2, 1, 1, 1, 4, 2, 3]
def baseStart_832964 : Nat := 118140960795 + 832964 * 2 ^ 59
def prefixEnd_832964 : Nat := 4983230072969 + 3 ^ 40 * 832964 * 2
def baseEnd_832964 : Nat := 285140599927856172146183

theorem tailTrace_832964 : CollatzResearch.WordTrace tailWord_832964 prefixEnd_832964 285140599927856172146183 := by
  unfold tailWord_832964
  simp only [CollatzResearch.WordTrace]
  refine ⟨15190346477160580885248973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20253795302880774513665297 15190346477160580885248973)
  ·
    refine ⟨5696379928935217831968365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15190346477160580885248973 5696379928935217831968365)
    ·
      refine ⟨2136142473350706686988137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5696379928935217831968365 2136142473350706686988137)
      ·
        refine ⟨1602106855013030015241103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2136142473350706686988137 1602106855013030015241103)
        ·
          refine ⟨2403160282519545022861655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1602106855013030015241103 2403160282519545022861655)
          ·
            refine ⟨3604740423779317534292483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2403160282519545022861655 3604740423779317534292483)
            ·
              refine ⟨5407110635668976301438725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3604740423779317534292483 5407110635668976301438725)
              ·
                refine ⟨1013833244187933056519761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5407110635668976301438725 1013833244187933056519761)
                ·
                  refine ⟨760374933140949792389821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1013833244187933056519761 760374933140949792389821)
                  ·
                    refine ⟨285140599927856172146183, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 760374933140949792389821 285140599927856172146183)
                    ·
                      rfl

theorem cell22_832964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 1, 1, 1, 4, 2, 3].length) (baseStart_832964 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_832964 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_832964 prefixEnd_832964 := by exact prefixLift 832964
  have htrace : WordTrace (prefixWord ++ tailWord_832964) baseStart_832964 baseEnd_832964 := by
    simpa [prefixWord, tailWord_832964, baseEnd_832964] using wordTrace_append hprefix tailTrace_832964
  have hstable : (prefixWord ++ tailWord_832964).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_832964).length < 2 ^ (prefixWord ++ tailWord_832964).sum := by decide
  have hdescent : baseEnd_832964 < baseStart_832964 := by decide
  rcases family_descends (prefixWord ++ tailWord_832964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833009 : List Nat := [1, 2, 2, 2, 3, 2, 1, 5, 1, 3]
def baseStart_833009 : Nat := 118140960795 + 833009 * 2 ^ 59
def prefixEnd_833009 : Nat := 4983230072969 + 3 ^ 40 * 833009 * 2
def baseEnd_833009 : Nat := 285156004347491054771045

theorem tailTrace_833009 : CollatzResearch.WordTrace tailWord_833009 prefixEnd_833009 285156004347491054771045 := by
  unfold tailWord_833009
  simp only [CollatzResearch.WordTrace]
  refine ⟨30382334239158134455886081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20254889492772089637257387 30382334239158134455886081)
  ·
    refine ⟨22786750679368600841914561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30382334239158134455886081 22786750679368600841914561)
    ·
      refine ⟨17090063009526450631435921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22786750679368600841914561 17090063009526450631435921)
      ·
        refine ⟨12817547257144837973576941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17090063009526450631435921 12817547257144837973576941)
        ·
          refine ⟨4806580221429314240091353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12817547257144837973576941 4806580221429314240091353)
          ·
            refine ⟨3604935166071985680068515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4806580221429314240091353 3604935166071985680068515)
            ·
              refine ⟨5407402749107978520102773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3604935166071985680068515 5407402749107978520102773)
              ·
                refine ⟨506944007728872986259635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5407402749107978520102773 506944007728872986259635)
                ·
                  refine ⟨760416011593309479389453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 506944007728872986259635 760416011593309479389453)
                  ·
                    refine ⟨285156004347491054771045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 760416011593309479389453 285156004347491054771045)
                    ·
                      rfl

theorem cell22_833009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 2, 1, 5, 1, 3].length) (baseStart_833009 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833009 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833009 prefixEnd_833009 := by exact prefixLift 833009
  have htrace : WordTrace (prefixWord ++ tailWord_833009) baseStart_833009 baseEnd_833009 := by
    simpa [prefixWord, tailWord_833009, baseEnd_833009] using wordTrace_append hprefix tailTrace_833009
  have hstable : (prefixWord ++ tailWord_833009).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833009).length < 2 ^ (prefixWord ++ tailWord_833009).sum := by decide
  have hdescent : baseEnd_833009 < baseStart_833009 := by decide
  rcases family_descends (prefixWord ++ tailWord_833009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833020 : List Nat := [2, 2, 2, 1, 2, 1, 3, 2, 2, 5]
def baseStart_833020 : Nat := 118140960795 + 833020 * 2 ^ 59
def prefixEnd_833020 : Nat := 4983230072969 + 3 ^ 40 * 833020 * 2
def baseEnd_833020 : Nat := 285159769872290692746011

theorem tailTrace_833020 : CollatzResearch.WordTrace tailWord_833020 prefixEnd_833020 285159769872290692746011 := by
  unfold tailWord_833020
  simp only [CollatzResearch.WordTrace]
  refine ⟨15191367721059141667268257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20255156961412188889691009 15191367721059141667268257)
  ·
    refine ⟨11393525790794356250451193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15191367721059141667268257 11393525790794356250451193)
    ·
      refine ⟨8545144343095767187838395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11393525790794356250451193 8545144343095767187838395)
      ·
        refine ⟨12817716514643650781757593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8545144343095767187838395 12817716514643650781757593)
        ·
          refine ⟨9613287385982738086318195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12817716514643650781757593 9613287385982738086318195)
          ·
            refine ⟨14419931078974107129477293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9613287385982738086318195 14419931078974107129477293)
            ·
              refine ⟨5407474154615290173553985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14419931078974107129477293 5407474154615290173553985)
              ·
                refine ⟨4055605615961467630165489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5407474154615290173553985 4055605615961467630165489)
                ·
                  refine ⟨3041704211971100722624117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4055605615961467630165489 3041704211971100722624117)
                  ·
                    refine ⟨285159769872290692746011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3041704211971100722624117 285159769872290692746011)
                    ·
                      rfl

theorem cell22_833020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 2, 2, 5].length) (baseStart_833020 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833020 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833020 prefixEnd_833020 := by exact prefixLift 833020
  have htrace : WordTrace (prefixWord ++ tailWord_833020) baseStart_833020 baseEnd_833020 := by
    simpa [prefixWord, tailWord_833020, baseEnd_833020] using wordTrace_append hprefix tailTrace_833020
  have hstable : (prefixWord ++ tailWord_833020).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833020).length < 2 ^ (prefixWord ++ tailWord_833020).sum := by decide
  have hdescent : baseEnd_833020 < baseStart_833020 := by decide
  rcases family_descends (prefixWord ++ tailWord_833020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833026 : List Nat := [3, 4, 1, 2, 1, 2, 2, 1, 3, 3]
def baseStart_833026 : Nat := 118140960795 + 833026 * 2 ^ 59
def prefixEnd_833026 : Nat := 4983230072969 + 3 ^ 40 * 833026 * 2
def baseEnd_833026 : Nat := 285161823794908677095993

theorem tailTrace_833026 : CollatzResearch.WordTrace tailWord_833026 prefixEnd_833026 285161823794908677095993 := by
  unfold tailWord_833026
  simp only [CollatzResearch.WordTrace]
  refine ⟨7595738570024136589813733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20255302853397697572836621 7595738570024136589813733)
  ·
    refine ⟨1424200981879525610590075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7595738570024136589813733 1424200981879525610590075)
    ·
      refine ⟨2136301472819288415885113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1424200981879525610590075 2136301472819288415885113)
      ·
        refine ⟨1602226104614466311913835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2136301472819288415885113 1602226104614466311913835)
        ·
          refine ⟨2403339156921699467870753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1602226104614466311913835 2403339156921699467870753)
          ·
            refine ⟨1802504367691274600903065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2403339156921699467870753 1802504367691274600903065)
            ·
              refine ⟨1351878275768455950677299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1802504367691274600903065 1351878275768455950677299)
              ·
                refine ⟨2027817413652683926015949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1351878275768455950677299 2027817413652683926015949)
                ·
                  refine ⟨760431530119756472255981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2027817413652683926015949 760431530119756472255981)
                  ·
                    refine ⟨285161823794908677095993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 760431530119756472255981 285161823794908677095993)
                    ·
                      rfl

theorem cell22_833026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 2, 2, 1, 3, 3].length) (baseStart_833026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833026 prefixEnd_833026 := by exact prefixLift 833026
  have htrace : WordTrace (prefixWord ++ tailWord_833026) baseStart_833026 baseEnd_833026 := by
    simpa [prefixWord, tailWord_833026, baseEnd_833026] using wordTrace_append hprefix tailTrace_833026
  have hstable : (prefixWord ++ tailWord_833026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833026).length < 2 ^ (prefixWord ++ tailWord_833026).sum := by decide
  have hdescent : baseEnd_833026 < baseStart_833026 := by decide
  rcases family_descends (prefixWord ++ tailWord_833026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833082 : List Nat := [3, 1, 1, 1, 3, 2, 1, 3, 4, 3]
def baseStart_833082 : Nat := 118140960795 + 833082 * 2 ^ 59
def prefixEnd_833082 : Nat := 4983230072969 + 3 ^ 40 * 833082 * 2
def baseEnd_833082 : Nat := 285180993739343197695821

theorem tailTrace_833082 : CollatzResearch.WordTrace tailWord_833082 prefixEnd_833082 285180993739343197695821 := by
  unfold tailWord_833082
  simp only [CollatzResearch.WordTrace]
  refine ⟨7596249191973416980823375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20256664511929111948862333 7596249191973416980823375)
  ·
    refine ⟨11394373787960125471235063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7596249191973416980823375 11394373787960125471235063)
    ·
      refine ⟨17091560681940188206852595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11394373787960125471235063 17091560681940188206852595)
      ·
        refine ⟨25637341022910282310278893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17091560681940188206852595 25637341022910282310278893)
        ·
          refine ⟨9614002883591355866354585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25637341022910282310278893 9614002883591355866354585)
          ·
            refine ⟨7210502162693516899765939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9614002883591355866354585 7210502162693516899765939)
            ·
              refine ⟨10815753244040275349648909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7210502162693516899765939 10815753244040275349648909)
              ·
                refine ⟨4055907466515103256118341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10815753244040275349648909 4055907466515103256118341)
                ·
                  refine ⟨760482649971581860522189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4055907466515103256118341 760482649971581860522189)
                  ·
                    refine ⟨285180993739343197695821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 760482649971581860522189 285180993739343197695821)
                    ·
                      rfl

theorem cell22_833082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 1, 3, 4, 3].length) (baseStart_833082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833082 prefixEnd_833082 := by exact prefixLift 833082
  have htrace : WordTrace (prefixWord ++ tailWord_833082) baseStart_833082 baseEnd_833082 := by
    simpa [prefixWord, tailWord_833082, baseEnd_833082] using wordTrace_append hprefix tailTrace_833082
  have hstable : (prefixWord ++ tailWord_833082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833082).length < 2 ^ (prefixWord ++ tailWord_833082).sum := by decide
  have hdescent : baseEnd_833082 < baseStart_833082 := by decide
  rcases family_descends (prefixWord ++ tailWord_833082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833084 : List Nat := [2, 2, 2, 2, 4, 2, 1, 1, 6]
def baseStart_833084 : Nat := 118140960795 + 833084 * 2 ^ 59
def prefixEnd_833084 : Nat := 4983230072969 + 3 ^ 40 * 833084 * 2
def baseEnd_833084 : Nat := 95060559460071953048605

theorem tailTrace_833084 : CollatzResearch.WordTrace tailWord_833084 prefixEnd_833084 95060559460071953048605 := by
  unfold tailWord_833084
  simp only [CollatzResearch.WordTrace]
  refine ⟨15192534856943211132433153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20256713142590948176577537 15192534856943211132433153)
  ·
    refine ⟨11394401142707408349324865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15192534856943211132433153 11394401142707408349324865)
    ·
      refine ⟨8545800857030556261993649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11394401142707408349324865 8545800857030556261993649)
      ·
        refine ⟨6409350642772917196495237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8545800857030556261993649 6409350642772917196495237)
        ·
          refine ⟨1201753245519921974342857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6409350642772917196495237 1201753245519921974342857)
          ·
            refine ⟨901314934139941480757143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1201753245519921974342857 901314934139941480757143)
            ·
              refine ⟨1351972401209912221135715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 901314934139941480757143 1351972401209912221135715)
              ·
                refine ⟨2027958601814868331703573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1351972401209912221135715 2027958601814868331703573)
                ·
                  refine ⟨95060559460071953048605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2027958601814868331703573 95060559460071953048605)
                  ·
                    rfl

theorem cell22_833084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 1, 1, 6].length) (baseStart_833084 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833084 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833084 prefixEnd_833084 := by exact prefixLift 833084
  have htrace : WordTrace (prefixWord ++ tailWord_833084) baseStart_833084 baseEnd_833084 := by
    simpa [prefixWord, tailWord_833084, baseEnd_833084] using wordTrace_append hprefix tailTrace_833084
  have hstable : (prefixWord ++ tailWord_833084).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833084).length < 2 ^ (prefixWord ++ tailWord_833084).sum := by decide
  have hdescent : baseEnd_833084 < baseStart_833084 := by decide
  rcases family_descends (prefixWord ++ tailWord_833084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833157 : List Nat := [1, 3, 1, 1, 4, 1, 1, 5, 5]
def baseStart_833157 : Nat := 118140960795 + 833157 * 2 ^ 59
def prefixEnd_833157 : Nat := 4983230072969 + 3 ^ 40 * 833157 * 2
def baseEnd_833157 : Nat := 95068889257356000690197

theorem tailTrace_833157 : CollatzResearch.WordTrace tailWord_833157 prefixEnd_833157 95068889257356000690197 := by
  unfold tailWord_833157
  simp only [CollatzResearch.WordTrace]
  refine ⟨30387732242621955732273725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20258488161747970488182483 30387732242621955732273725)
  ·
    refine ⟨11395399590983233399602647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30387732242621955732273725 11395399590983233399602647)
    ·
      refine ⟨17093099386474850099403971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11395399590983233399602647 17093099386474850099403971)
      ·
        refine ⟨25639649079712275149105957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17093099386474850099403971 25639649079712275149105957)
        ·
          refine ⟨4807434202446051590457367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25639649079712275149105957 4807434202446051590457367)
          ·
            refine ⟨7211151303669077385686051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4807434202446051590457367 7211151303669077385686051)
            ·
              refine ⟨10816726955503616078529077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7211151303669077385686051 10816726955503616078529077)
              ·
                refine ⟨1014068152078464007362101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10816726955503616078529077 1014068152078464007362101)
                ·
                  refine ⟨95068889257356000690197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1014068152078464007362101 95068889257356000690197)
                  ·
                    rfl

theorem cell22_833157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 1, 5, 5].length) (baseStart_833157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833157 prefixEnd_833157 := by exact prefixLift 833157
  have htrace : WordTrace (prefixWord ++ tailWord_833157) baseStart_833157 baseEnd_833157 := by
    simpa [prefixWord, tailWord_833157, baseEnd_833157] using wordTrace_append hprefix tailTrace_833157
  have hstable : (prefixWord ++ tailWord_833157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833157).length < 2 ^ (prefixWord ++ tailWord_833157).sum := by decide
  have hdescent : baseEnd_833157 < baseStart_833157 := by decide
  rcases family_descends (prefixWord ++ tailWord_833157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833202 : List Nat := [3, 2, 1, 1, 1, 2, 3, 3, 6]
def baseStart_833202 : Nat := 118140960795 + 833202 * 2 ^ 59
def prefixEnd_833202 : Nat := 4983230072969 + 3 ^ 40 * 833202 * 2
def baseEnd_833202 : Nat := 95074024063900961565151

theorem tailTrace_833202 : CollatzResearch.WordTrace tailWord_833202 prefixEnd_833202 95074024063900961565151 := by
  unfold tailWord_833202
  simp only [CollatzResearch.WordTrace]
  refine ⟨7597343381864732104415465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20259582351639285611774573 7597343381864732104415465)
  ·
    refine ⟨5698007536398549078311599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7597343381864732104415465 5698007536398549078311599)
    ·
      refine ⟨8547011304597823617467399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5698007536398549078311599 8547011304597823617467399)
      ·
        refine ⟨12820516956896735426201099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8547011304597823617467399 12820516956896735426201099)
        ·
          refine ⟨19230775435345103139301649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12820516956896735426201099 19230775435345103139301649)
          ·
            refine ⟨14423081576508827354476237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19230775435345103139301649 14423081576508827354476237)
            ·
              refine ⟨5408655591190810257928589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14423081576508827354476237 5408655591190810257928589)
              ·
                refine ⟨2028245846696553846723221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5408655591190810257928589 2028245846696553846723221)
                ·
                  refine ⟨95074024063900961565151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2028245846696553846723221 95074024063900961565151)
                  ·
                    rfl

theorem cell22_833202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 3, 6].length) (baseStart_833202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833202 prefixEnd_833202 := by exact prefixLift 833202
  have htrace : WordTrace (prefixWord ++ tailWord_833202) baseStart_833202 baseEnd_833202 := by
    simpa [prefixWord, tailWord_833202, baseEnd_833202] using wordTrace_append hprefix tailTrace_833202
  have hstable : (prefixWord ++ tailWord_833202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833202).length < 2 ^ (prefixWord ++ tailWord_833202).sum := by decide
  have hdescent : baseEnd_833202 < baseStart_833202 := by decide
  rcases family_descends (prefixWord ++ tailWord_833202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833206 : List Nat := [5, 1, 3, 1, 1, 1, 2, 1, 2, 5]
def baseStart_833206 : Nat := 118140960795 + 833206 * 2 ^ 59
def prefixEnd_833206 : Nat := 4983230072969 + 3 ^ 40 * 833206 * 2
def baseEnd_833206 : Nat := 285223441473448207595441

theorem tailTrace_833206 : CollatzResearch.WordTrace tailWord_833206 prefixEnd_833206 285223441473448207595441 := by
  unfold tailWord_833206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1899344963715277318800467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20259679612962958067204981 1899344963715277318800467)
  ·
    refine ⟨2849017445572915978200701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1899344963715277318800467 2849017445572915978200701)
    ·
      refine ⟨1068381542089843491825263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2849017445572915978200701 1068381542089843491825263)
      ·
        refine ⟨1602572313134765237737895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1068381542089843491825263 1602572313134765237737895)
        ·
          refine ⟨2403858469702147856606843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1602572313134765237737895 2403858469702147856606843)
          ·
            refine ⟨3605787704553221784910265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2403858469702147856606843 3605787704553221784910265)
            ·
              refine ⟨2704340778414916338682699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3605787704553221784910265 2704340778414916338682699)
              ·
                refine ⟨4056511167622374508024049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2704340778414916338682699 4056511167622374508024049)
                ·
                  refine ⟨3042383375716780881018037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4056511167622374508024049 3042383375716780881018037)
                  ·
                    refine ⟨285223441473448207595441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3042383375716780881018037 285223441473448207595441)
                    ·
                      rfl

theorem cell22_833206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 2, 1, 2, 5].length) (baseStart_833206 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833206 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833206 prefixEnd_833206 := by exact prefixLift 833206
  have htrace : WordTrace (prefixWord ++ tailWord_833206) baseStart_833206 baseEnd_833206 := by
    simpa [prefixWord, tailWord_833206, baseEnd_833206] using wordTrace_append hprefix tailTrace_833206
  have hstable : (prefixWord ++ tailWord_833206).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833206).length < 2 ^ (prefixWord ++ tailWord_833206).sum := by decide
  have hdescent : baseEnd_833206 < baseStart_833206 := by decide
  rcases family_descends (prefixWord ++ tailWord_833206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833277 : List Nat := [1, 4, 1, 1, 1, 1, 2, 1, 4, 6]
def baseStart_833277 : Nat := 118140960795 + 833277 * 2 ^ 59
def prefixEnd_833277 : Nat := 4983230072969 + 3 ^ 40 * 833277 * 2
def baseEnd_833277 : Nat := 285247746224427689070223

theorem tailTrace_833277 : CollatzResearch.WordTrace tailWord_833277 prefixEnd_833277 285247746224427689070223 := by
  unfold tailWord_833277
  simp only [CollatzResearch.WordTrace]
  refine ⟨30392109002187216226642085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20261406001458144151094723 30392109002187216226642085)
  ·
    refine ⟨5698520437910103042495391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 30392109002187216226642085 5698520437910103042495391)
    ·
      refine ⟨8547780656865154563743087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5698520437910103042495391 8547780656865154563743087)
      ·
        refine ⟨12821670985297731845614631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8547780656865154563743087 12821670985297731845614631)
        ·
          refine ⟨19232506477946597768421947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12821670985297731845614631 19232506477946597768421947)
          ·
            refine ⟨28848759716919896652632921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19232506477946597768421947 28848759716919896652632921)
            ·
              refine ⟨21636569787689922489474691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28848759716919896652632921 21636569787689922489474691)
              ·
                refine ⟨32454854681534883734212037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21636569787689922489474691 32454854681534883734212037)
                ·
                  refine ⟨6085285252787790700164757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32454854681534883734212037 6085285252787790700164757)
                  ·
                    refine ⟨285247746224427689070223, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6085285252787790700164757 285247746224427689070223)
                    ·
                      rfl

theorem cell22_833277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 1, 4, 6].length) (baseStart_833277 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833277 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833277 prefixEnd_833277 := by exact prefixLift 833277
  have htrace : WordTrace (prefixWord ++ tailWord_833277) baseStart_833277 baseEnd_833277 := by
    simpa [prefixWord, tailWord_833277, baseEnd_833277] using wordTrace_append hprefix tailTrace_833277
  have hstable : (prefixWord ++ tailWord_833277).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833277).length < 2 ^ (prefixWord ++ tailWord_833277).sum := by decide
  have hdescent : baseEnd_833277 < baseStart_833277 := by decide
  rcases family_descends (prefixWord ++ tailWord_833277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833279 : List Nat := [1, 1, 2, 2, 1, 3, 2, 4, 3, 3]
def baseStart_833279 : Nat := 118140960795 + 833279 * 2 ^ 59
def prefixEnd_833279 : Nat := 4983230072969 + 3 ^ 40 * 833279 * 2
def baseEnd_833279 : Nat := 285248430865300350520217

theorem tailTrace_833279 : CollatzResearch.WordTrace tailWord_833279 prefixEnd_833279 285248430865300350520217 := by
  unfold tailWord_833279
  simp only [CollatzResearch.WordTrace]
  refine ⟨30392181948179970568214891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20261454632119980378809927 30392181948179970568214891)
  ·
    refine ⟨45588272922269955852322337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30392181948179970568214891 45588272922269955852322337)
    ·
      refine ⟨34191204691702466889241753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45588272922269955852322337 34191204691702466889241753)
      ·
        refine ⟨25643403518776850166931315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34191204691702466889241753 25643403518776850166931315)
        ·
          refine ⟨38465105278165275250396973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25643403518776850166931315 38465105278165275250396973)
          ·
            refine ⟨14424414479311978218898865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38465105278165275250396973 14424414479311978218898865)
            ·
              refine ⟨10818310859483983664174149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14424414479311978218898865 10818310859483983664174149)
              ·
                refine ⟨2028433286153246937032653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10818310859483983664174149 2028433286153246937032653)
                ·
                  refine ⟨760662482307467601387245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2028433286153246937032653 760662482307467601387245)
                  ·
                    refine ⟨285248430865300350520217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 760662482307467601387245 285248430865300350520217)
                    ·
                      rfl

theorem cell22_833279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 2, 4, 3, 3].length) (baseStart_833279 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833279 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833279 prefixEnd_833279 := by exact prefixLift 833279
  have htrace : WordTrace (prefixWord ++ tailWord_833279) baseStart_833279 baseEnd_833279 := by
    simpa [prefixWord, tailWord_833279, baseEnd_833279] using wordTrace_append hprefix tailTrace_833279
  have hstable : (prefixWord ++ tailWord_833279).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833279).length < 2 ^ (prefixWord ++ tailWord_833279).sum := by decide
  have hdescent : baseEnd_833279 < baseStart_833279 := by decide
  rcases family_descends (prefixWord ++ tailWord_833279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833292 : List Nat := [2, 2, 1, 2, 2, 1, 2, 1, 9]
def baseStart_833292 : Nat := 118140960795 + 833292 * 2 ^ 59
def prefixEnd_833292 : Nat := 4983230072969 + 3 ^ 40 * 833292 * 2
def baseEnd_833292 : Nat := 95084293676990883315059

theorem tailTrace_833292 : CollatzResearch.WordTrace tailWord_833292 prefixEnd_833292 95084293676990883315059 := by
  unfold tailWord_833292
  simp only [CollatzResearch.WordTrace]
  refine ⟨15196328048566436894219065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20261770731421915858958753 15196328048566436894219065)
  ·
    refine ⟨11397246036424827670664299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15196328048566436894219065 11397246036424827670664299)
    ·
      refine ⟨17095869054637241505996449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11397246036424827670664299 17095869054637241505996449)
      ·
        refine ⟨12821901790977931129497337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17095869054637241505996449 12821901790977931129497337)
        ·
          refine ⟨9616426343233448347123003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12821901790977931129497337 9616426343233448347123003)
          ·
            refine ⟨14424639514850172520684505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9616426343233448347123003 14424639514850172520684505)
            ·
              refine ⟨10818479636137629390513379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14424639514850172520684505 10818479636137629390513379)
              ·
                refine ⟨16227719454206444085770069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10818479636137629390513379 16227719454206444085770069)
                ·
                  refine ⟨95084293676990883315059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 16227719454206444085770069 95084293676990883315059)
                  ·
                    rfl

theorem cell22_833292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 1, 9].length) (baseStart_833292 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833292 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833292 prefixEnd_833292 := by exact prefixLift 833292
  have htrace : WordTrace (prefixWord ++ tailWord_833292) baseStart_833292 baseEnd_833292 := by
    simpa [prefixWord, tailWord_833292, baseEnd_833292] using wordTrace_append hprefix tailTrace_833292
  have hstable : (prefixWord ++ tailWord_833292).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833292).length < 2 ^ (prefixWord ++ tailWord_833292).sum := by decide
  have hdescent : baseEnd_833292 < baseStart_833292 := by decide
  rcases family_descends (prefixWord ++ tailWord_833292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833307 : List Nat := [1, 1, 1, 1, 1, 1, 4, 3, 4, 5]
def baseStart_833307 : Nat := 118140960795 + 833307 * 2 ^ 59
def prefixEnd_833307 : Nat := 4983230072969 + 3 ^ 40 * 833307 * 2
def baseEnd_833307 : Nat := 285258015837517610820131

theorem tailTrace_833307 : CollatzResearch.WordTrace tailWord_833307 prefixEnd_833307 285258015837517610820131 := by
  unfold tailWord_833307
  simp only [CollatzResearch.WordTrace]
  refine ⟨30393203192078531350234175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20262135461385687566822783 30393203192078531350234175)
  ·
    refine ⟨45589804788117797025351263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30393203192078531350234175 45589804788117797025351263)
    ·
      refine ⟨68384707182176695538026895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45589804788117797025351263 68384707182176695538026895)
      ·
        refine ⟨102577060773265043307040343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68384707182176695538026895 102577060773265043307040343)
        ·
          refine ⟨153865591159897564960560515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102577060773265043307040343 153865591159897564960560515)
          ·
            refine ⟨230798386739846347440840773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 153865591159897564960560515 230798386739846347440840773)
            ·
              refine ⟨43274697513721190145157645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 230798386739846347440840773 43274697513721190145157645)
              ·
                refine ⟨16228011567645446304434117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43274697513721190145157645 16228011567645446304434117)
                ·
                  refine ⟨3042752168933521182081397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16228011567645446304434117 3042752168933521182081397)
                  ·
                    refine ⟨285258015837517610820131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3042752168933521182081397 285258015837517610820131)
                    ·
                      rfl

theorem cell22_833307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 3, 4, 5].length) (baseStart_833307 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833307 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833307 prefixEnd_833307 := by exact prefixLift 833307
  have htrace : WordTrace (prefixWord ++ tailWord_833307) baseStart_833307 baseEnd_833307 := by
    simpa [prefixWord, tailWord_833307, baseEnd_833307] using wordTrace_append hprefix tailTrace_833307
  have hstable : (prefixWord ++ tailWord_833307).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833307).length < 2 ^ (prefixWord ++ tailWord_833307).sum := by decide
  have hdescent : baseEnd_833307 < baseStart_833307 := by decide
  rcases family_descends (prefixWord ++ tailWord_833307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833313 : List Nat := [1, 2, 3, 2, 1, 4, 1, 4, 1, 3]
def baseStart_833313 : Nat := 118140960795 + 833313 * 2 ^ 59
def prefixEnd_833313 : Nat := 4983230072969 + 3 ^ 40 * 833313 * 2
def baseEnd_833313 : Nat := 285260069760135595170113

theorem tailTrace_833313 : CollatzResearch.WordTrace tailWord_833313 prefixEnd_833313 285260069760135595170113 := by
  unfold tailWord_833313
  simp only [CollatzResearch.WordTrace]
  refine ⟨30393422030056794374952593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20262281353371196249968395 30393422030056794374952593)
  ·
    refine ⟨22795066522542595781214445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30393422030056794374952593 22795066522542595781214445)
    ·
      refine ⟨8548149945953473417955417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22795066522542595781214445 8548149945953473417955417)
      ·
        refine ⟨6411112459465105063466563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8548149945953473417955417 6411112459465105063466563)
        ·
          refine ⟨9616668689197657595199845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6411112459465105063466563 9616668689197657595199845)
          ·
            refine ⟨1803125379224560799099971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9616668689197657595199845 1803125379224560799099971)
            ·
              refine ⟨2704688068836841198649957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1803125379224560799099971 2704688068836841198649957)
              ·
                refine ⟨507129012906907724746867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2704688068836841198649957 507129012906907724746867)
                ·
                  refine ⟨760693519360361587120301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 507129012906907724746867 760693519360361587120301)
                  ·
                    refine ⟨285260069760135595170113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 760693519360361587120301 285260069760135595170113)
                    ·
                      rfl

theorem cell22_833313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4, 1, 3].length) (baseStart_833313 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833313 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833313 prefixEnd_833313 := by exact prefixLift 833313
  have htrace : WordTrace (prefixWord ++ tailWord_833313) baseStart_833313 baseEnd_833313 := by
    simpa [prefixWord, tailWord_833313, baseEnd_833313] using wordTrace_append hprefix tailTrace_833313
  have hstable : (prefixWord ++ tailWord_833313).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833313).length < 2 ^ (prefixWord ++ tailWord_833313).sum := by decide
  have hdescent : baseEnd_833313 < baseStart_833313 := by decide
  rcases family_descends (prefixWord ++ tailWord_833313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833324 : List Nat := [2, 2, 1, 1, 1, 6, 1, 1, 2, 5]
def baseStart_833324 : Nat := 118140960795 + 833324 * 2 ^ 59
def prefixEnd_833324 : Nat := 4983230072969 + 3 ^ 40 * 833324 * 2
def baseEnd_833324 : Nat := 285263835284935233145079

theorem tailTrace_833324 : CollatzResearch.WordTrace tailWord_833324 prefixEnd_833324 285263835284935233145079 := by
  unfold tailWord_833324
  simp only [CollatzResearch.WordTrace]
  refine ⟨15196911616508471626801513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20262548822011295502402017 15196911616508471626801513)
  ·
    refine ⟨11397683712381353720101135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15196911616508471626801513 11397683712381353720101135)
    ·
      refine ⟨17096525568572030580151703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11397683712381353720101135 17096525568572030580151703)
      ·
        refine ⟨25644788352858045870227555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17096525568572030580151703 25644788352858045870227555)
        ·
          refine ⟨38467182529287068805341333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25644788352858045870227555 38467182529287068805341333)
          ·
            refine ⟨1803149181060331350250375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38467182529287068805341333 1803149181060331350250375)
            ·
              refine ⟨2704723771590497025375563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1803149181060331350250375 2704723771590497025375563)
              ·
                refine ⟨4057085657385745538063345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2704723771590497025375563 4057085657385745538063345)
                ·
                  refine ⟨3042814243039309153547509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4057085657385745538063345 3042814243039309153547509)
                  ·
                    refine ⟨285263835284935233145079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3042814243039309153547509 285263835284935233145079)
                    ·
                      rfl

theorem cell22_833324_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 5].length) (baseStart_833324 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833324 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833324 prefixEnd_833324 := by exact prefixLift 833324
  have htrace : WordTrace (prefixWord ++ tailWord_833324) baseStart_833324 baseEnd_833324 := by
    simpa [prefixWord, tailWord_833324, baseEnd_833324] using wordTrace_append hprefix tailTrace_833324
  have hstable : (prefixWord ++ tailWord_833324).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833324).length < 2 ^ (prefixWord ++ tailWord_833324).sum := by decide
  have hdescent : baseEnd_833324 < baseStart_833324 := by decide
  rcases family_descends (prefixWord ++ tailWord_833324) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833384 : List Nat := [2, 1, 4, 2, 1, 1, 1, 1, 3, 6]
def baseStart_833384 : Nat := 118140960795 + 833384 * 2 ^ 59
def prefixEnd_833384 : Nat := 4983230072969 + 3 ^ 40 * 833384 * 2
def baseEnd_833384 : Nat := 285284374511115076644895

theorem tailTrace_833384 : CollatzResearch.WordTrace tailWord_833384 prefixEnd_833384 285284374511115076644895 := by
  unfold tailWord_833384
  simp only [CollatzResearch.WordTrace]
  refine ⟨15198005806399786750393603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20264007741866382333858137 15198005806399786750393603)
  ·
    refine ⟨22797008709599680125590405, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15198005806399786750393603 22797008709599680125590405)
    ·
      refine ⟨4274439133049940023548201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22797008709599680125590405 4274439133049940023548201)
      ·
        refine ⟨3205829349787455017661151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4274439133049940023548201 3205829349787455017661151)
        ·
          refine ⟨4808744024681182526491727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3205829349787455017661151 4808744024681182526491727)
          ·
            refine ⟨7213116037021773789737591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4808744024681182526491727 7213116037021773789737591)
            ·
              refine ⟨10819674055532660684606387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7213116037021773789737591 10819674055532660684606387)
              ·
                refine ⟨16229511083298991026909581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10819674055532660684606387 16229511083298991026909581)
                ·
                  refine ⟨6086066656237121635091093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16229511083298991026909581 6086066656237121635091093)
                  ·
                    refine ⟨285284374511115076644895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6086066656237121635091093 285284374511115076644895)
                    ·
                      rfl

theorem cell22_833384_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 1, 3, 6].length) (baseStart_833384 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833384 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833384 prefixEnd_833384 := by exact prefixLift 833384
  have htrace : WordTrace (prefixWord ++ tailWord_833384) baseStart_833384 baseEnd_833384 := by
    simpa [prefixWord, tailWord_833384, baseEnd_833384] using wordTrace_append hprefix tailTrace_833384
  have hstable : (prefixWord ++ tailWord_833384).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833384).length < 2 ^ (prefixWord ++ tailWord_833384).sum := by decide
  have hdescent : baseEnd_833384 < baseStart_833384 := by decide
  rcases family_descends (prefixWord ++ tailWord_833384) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833416 : List Nat := [2, 1, 3, 3, 3, 2, 8]
def baseStart_833416 : Nat := 118140960795 + 833416 * 2 ^ 59
def prefixEnd_833416 : Nat := 4983230072969 + 3 ^ 40 * 833416 * 2
def baseEnd_833416 : Nat := 10566493657965839253511

theorem tailTrace_833416 : CollatzResearch.WordTrace tailWord_833416 prefixEnd_833416 10566493657965839253511 := by
  unfold tailWord_833416
  simp only [CollatzResearch.WordTrace]
  refine ⟨15198589374341821482976051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20264785832455761977301401 15198589374341821482976051)
  ·
    refine ⟨22797884061512732224464077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15198589374341821482976051 22797884061512732224464077)
    ·
      refine ⟨8549206523067274584174029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22797884061512732224464077 8549206523067274584174029)
      ·
        refine ⟨3205952446150227969065261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8549206523067274584174029 3205952446150227969065261)
        ·
          refine ⟨1202232167306335488399473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3205952446150227969065261 1202232167306335488399473)
          ·
            refine ⟨901674125479751616299605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1202232167306335488399473 901674125479751616299605)
            ·
              refine ⟨10566493657965839253511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 901674125479751616299605 10566493657965839253511)
              ·
                rfl

theorem cell22_833416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 3, 2, 8].length) (baseStart_833416 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833416 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833416 prefixEnd_833416 := by exact prefixLift 833416
  have htrace : WordTrace (prefixWord ++ tailWord_833416) baseStart_833416 baseEnd_833416 := by
    simpa [prefixWord, tailWord_833416, baseEnd_833416] using wordTrace_append hprefix tailTrace_833416
  have hstable : (prefixWord ++ tailWord_833416).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833416).length < 2 ^ (prefixWord ++ tailWord_833416).sum := by decide
  have hdescent : baseEnd_833416 < baseStart_833416 := by decide
  rcases family_descends (prefixWord ++ tailWord_833416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833418 : List Nat := [3, 1, 2, 4, 2, 1, 1, 2, 2, 4]
def baseStart_833418 : Nat := 118140960795 + 833418 * 2 ^ 59
def prefixEnd_833418 : Nat := 4983230072969 + 3 ^ 40 * 833418 * 2
def baseEnd_833418 : Nat := 285296013405950321294791

theorem tailTrace_833418 : CollatzResearch.WordTrace tailWord_833418 prefixEnd_833418 285296013405950321294791 := by
  unfold tailWord_833418
  simp only [CollatzResearch.WordTrace]
  refine ⟨7599312923669099326881227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20264834463117598205016605 7599312923669099326881227)
  ·
    refine ⟨11398969385503648990321841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7599312923669099326881227 11398969385503648990321841)
    ·
      refine ⟨8549227039127736742741381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11398969385503648990321841 8549227039127736742741381)
      ·
        refine ⟨1602980069836450639264009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8549227039127736742741381 1602980069836450639264009)
        ·
          refine ⟨1202235052377337979448007, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1602980069836450639264009 1202235052377337979448007)
          ·
            refine ⟨1803352578566006969172011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202235052377337979448007 1803352578566006969172011)
            ·
              refine ⟨2705028867849010453758017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1803352578566006969172011 2705028867849010453758017)
              ·
                refine ⟨2028771650886757840318513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2705028867849010453758017 2028771650886757840318513)
                ·
                  refine ⟨1521578738165068380238885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2028771650886757840318513 1521578738165068380238885)
                  ·
                    refine ⟨285296013405950321294791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1521578738165068380238885 285296013405950321294791)
                    ·
                      rfl

theorem cell22_833418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 1, 1, 2, 2, 4].length) (baseStart_833418 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833418 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833418 prefixEnd_833418 := by exact prefixLift 833418
  have htrace : WordTrace (prefixWord ++ tailWord_833418) baseStart_833418 baseEnd_833418 := by
    simpa [prefixWord, tailWord_833418, baseEnd_833418] using wordTrace_append hprefix tailTrace_833418
  have hstable : (prefixWord ++ tailWord_833418).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833418).length < 2 ^ (prefixWord ++ tailWord_833418).sum := by decide
  have hdescent : baseEnd_833418 < baseStart_833418 := by decide
  rcases family_descends (prefixWord ++ tailWord_833418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833422 : List Nat := [4, 1, 1, 5, 1, 1, 3, 2, 4]
def baseStart_833422 : Nat := 118140960795 + 833422 * 2 ^ 59
def prefixEnd_833422 : Nat := 4983230072969 + 3 ^ 40 * 833422 * 2
def baseEnd_833422 : Nat := 95099127562565214731593

theorem tailTrace_833422 : CollatzResearch.WordTrace tailWord_833422 prefixEnd_833422 95099127562565214731593 := by
  unfold tailWord_833422
  simp only [CollatzResearch.WordTrace]
  refine ⟨3799674698332738248833815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 20264931724441270660447013 3799674698332738248833815)
  ·
    refine ⟨5699512047499107373250723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3799674698332738248833815 5699512047499107373250723)
    ·
      refine ⟨8549268071248661059876085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5699512047499107373250723 8549268071248661059876085)
      ·
        refine ⟨801493881679561974363383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8549268071248661059876085 801493881679561974363383)
        ·
          refine ⟨1202240822519342961545075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801493881679561974363383 1202240822519342961545075)
          ·
            refine ⟨1803361233779014442317613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202240822519342961545075 1803361233779014442317613)
            ·
              refine ⟨676260462667130415869105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1803361233779014442317613 676260462667130415869105)
              ·
                refine ⟨507195347000347811901829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 676260462667130415869105 507195347000347811901829)
                ·
                  refine ⟨95099127562565214731593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 507195347000347811901829 95099127562565214731593)
                  ·
                    rfl

theorem cell22_833422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 3, 2, 4].length) (baseStart_833422 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833422 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833422 prefixEnd_833422 := by exact prefixLift 833422
  have htrace : WordTrace (prefixWord ++ tailWord_833422) baseStart_833422 baseEnd_833422 := by
    simpa [prefixWord, tailWord_833422, baseEnd_833422] using wordTrace_append hprefix tailTrace_833422
  have hstable : (prefixWord ++ tailWord_833422).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833422).length < 2 ^ (prefixWord ++ tailWord_833422).sum := by decide
  have hdescent : baseEnd_833422 < baseStart_833422 := by decide
  rcases family_descends (prefixWord ++ tailWord_833422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833429 : List Nat := [1, 3, 2, 1, 1, 3, 2, 1, 2, 6]
def baseStart_833429 : Nat := 118140960795 + 833429 * 2 ^ 59
def prefixEnd_833429 : Nat := 4983230072969 + 3 ^ 40 * 833429 * 2
def baseEnd_833429 : Nat := 285299778930749959269757

theorem tailTrace_833429 : CollatzResearch.WordTrace tailWord_833429 prefixEnd_833429 285299778930749959269757 := by
  unfold tailWord_833429
  simp only [CollatzResearch.WordTrace]
  refine ⟨30397652897636546186175341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20265101931757697457450227 30397652897636546186175341)
  ·
    refine ⟨11399119836613704819815753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30397652897636546186175341 11399119836613704819815753)
    ·
      refine ⟨8549339877460278614861815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11399119836613704819815753 8549339877460278614861815)
      ·
        refine ⟨12824009816190417922292723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8549339877460278614861815 12824009816190417922292723)
        ·
          refine ⟨19236014724285626883439085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12824009816190417922292723 19236014724285626883439085)
          ·
            refine ⟨7213505521607110081289657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19236014724285626883439085 7213505521607110081289657)
            ·
              refine ⟨5410129141205332560967243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7213505521607110081289657 5410129141205332560967243)
              ·
                refine ⟨8115193711807998841450865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5410129141205332560967243 8115193711807998841450865)
                ·
                  refine ⟨6086395283855999131088149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8115193711807998841450865 6086395283855999131088149)
                  ·
                    refine ⟨285299778930749959269757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6086395283855999131088149 285299778930749959269757)
                    ·
                      rfl

theorem cell22_833429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 2, 6].length) (baseStart_833429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833429 prefixEnd_833429 := by exact prefixLift 833429
  have htrace : WordTrace (prefixWord ++ tailWord_833429) baseStart_833429 baseEnd_833429 := by
    simpa [prefixWord, tailWord_833429, baseEnd_833429] using wordTrace_append hprefix tailTrace_833429
  have hstable : (prefixWord ++ tailWord_833429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833429).length < 2 ^ (prefixWord ++ tailWord_833429).sum := by decide
  have hdescent : baseEnd_833429 < baseStart_833429 := by decide
  rcases family_descends (prefixWord ++ tailWord_833429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833540 : List Nat := [2, 3, 2, 4, 1, 1, 2, 1, 6]
def baseStart_833540 : Nat := 118140960795 + 833540 * 2 ^ 59
def prefixEnd_833540 : Nat := 4983230072969 + 3 ^ 40 * 833540 * 2
def baseEnd_833540 : Nat := 95112592166394223248139

theorem tailTrace_833540 : CollatzResearch.WordTrace tailWord_833540 prefixEnd_833540 95112592166394223248139 := by
  unfold tailWord_833540
  simp only [CollatzResearch.WordTrace]
  refine ⟨15200850700117206071733037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20267800933489608095644049 15200850700117206071733037)
  ·
    refine ⟨5700319012543952276899889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15200850700117206071733037 5700319012543952276899889)
    ·
      refine ⟨4275239259407964207674917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5700319012543952276899889 4275239259407964207674917)
      ·
        refine ⟨801607361138993288939047, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4275239259407964207674917 801607361138993288939047)
        ·
          refine ⟨1202411041708489933408571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 801607361138993288939047 1202411041708489933408571)
          ·
            refine ⟨1803616562562734900112857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202411041708489933408571 1803616562562734900112857)
            ·
              refine ⟨1352712421922051175084643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1803616562562734900112857 1352712421922051175084643)
              ·
                refine ⟨2029068632883076762626965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1352712421922051175084643 2029068632883076762626965)
                ·
                  refine ⟨95112592166394223248139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2029068632883076762626965 95112592166394223248139)
                  ·
                    rfl

theorem cell22_833540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 2, 1, 6].length) (baseStart_833540 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833540 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833540 prefixEnd_833540 := by exact prefixLift 833540
  have htrace : WordTrace (prefixWord ++ tailWord_833540) baseStart_833540 baseEnd_833540 := by
    simpa [prefixWord, tailWord_833540, baseEnd_833540] using wordTrace_append hprefix tailTrace_833540
  have hstable : (prefixWord ++ tailWord_833540).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833540).length < 2 ^ (prefixWord ++ tailWord_833540).sum := by decide
  have hdescent : baseEnd_833540 < baseStart_833540 := by decide
  rcases family_descends (prefixWord ++ tailWord_833540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833596 : List Nat := [2, 2, 2, 2, 2, 1, 1, 3, 7]
def baseStart_833596 : Nat := 118140960795 + 833596 * 2 ^ 59
def prefixEnd_833596 : Nat := 4983230072969 + 3 ^ 40 * 833596 * 2
def baseEnd_833596 : Nat := 95118982147872396781415

theorem tailTrace_833596 : CollatzResearch.WordTrace tailWord_833596 prefixEnd_833596 95118982147872396781415 := by
  unfold tailWord_833596
  simp only [CollatzResearch.WordTrace]
  refine ⟨15201871944015766853752321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20269162592021022471669761 15201871944015766853752321)
  ·
    refine ⟨11401403958011825140314241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15201871944015766853752321 11401403958011825140314241)
    ·
      refine ⟨8551052968508868855235681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11401403958011825140314241 8551052968508868855235681)
      ·
        refine ⟨6413289726381651641426761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8551052968508868855235681 6413289726381651641426761)
        ·
          refine ⟨4809967294786238731070071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6413289726381651641426761 4809967294786238731070071)
          ·
            refine ⟨7214950942179358096605107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4809967294786238731070071 7214950942179358096605107)
            ·
              refine ⟨10822426413269037144907661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7214950942179358096605107 10822426413269037144907661)
              ·
                refine ⟨4058409904975888929340373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10822426413269037144907661 4058409904975888929340373)
                ·
                  refine ⟨95118982147872396781415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 4058409904975888929340373 95118982147872396781415)
                  ·
                    rfl

theorem cell22_833596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 1, 3, 7].length) (baseStart_833596 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833596 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833596 prefixEnd_833596 := by exact prefixLift 833596
  have htrace : WordTrace (prefixWord ++ tailWord_833596) baseStart_833596 baseEnd_833596 := by
    simpa [prefixWord, tailWord_833596, baseEnd_833596] using wordTrace_append hprefix tailTrace_833596
  have hstable : (prefixWord ++ tailWord_833596).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833596).length < 2 ^ (prefixWord ++ tailWord_833596).sum := by decide
  have hdescent : baseEnd_833596 < baseStart_833596 := by decide
  rcases family_descends (prefixWord ++ tailWord_833596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833600 : List Nat := [2, 1, 1, 2, 2, 6, 1, 1, 3, 3]
def baseStart_833600 : Nat := 118140960795 + 833600 * 2 ^ 59
def prefixEnd_833600 : Nat := 4983230072969 + 3 ^ 40 * 833600 * 2
def baseEnd_833600 : Nat := 285358315725362513244233

theorem tailTrace_833600 : CollatzResearch.WordTrace tailWord_833600 prefixEnd_833600 285358315725362513244233 := by
  unfold tailWord_833600
  simp only [CollatzResearch.WordTrace]
  refine ⟨15201944890008521195325127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20269259853344694927100169 15201944890008521195325127)
  ·
    refine ⟨22802917335012781792987691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15201944890008521195325127 22802917335012781792987691)
    ·
      refine ⟨34204376002519172689481537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22802917335012781792987691 34204376002519172689481537)
      ·
        refine ⟨25653282001889379517111153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34204376002519172689481537 25653282001889379517111153)
        ·
          refine ⟨19239961501417034637833365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25653282001889379517111153 19239961501417034637833365)
          ·
            refine ⟨901873195378923498648439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 19239961501417034637833365 901873195378923498648439)
            ·
              refine ⟨1352809793068385247972659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 901873195378923498648439 1352809793068385247972659)
              ·
                refine ⟨2029214689602577871958989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1352809793068385247972659 2029214689602577871958989)
                ·
                  refine ⟨760955508600966701984621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2029214689602577871958989 760955508600966701984621)
                  ·
                    refine ⟨285358315725362513244233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 760955508600966701984621 285358315725362513244233)
                    ·
                      rfl

theorem cell22_833600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 6, 1, 1, 3, 3].length) (baseStart_833600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833600 prefixEnd_833600 := by exact prefixLift 833600
  have htrace : WordTrace (prefixWord ++ tailWord_833600) baseStart_833600 baseEnd_833600 := by
    simpa [prefixWord, tailWord_833600, baseEnd_833600] using wordTrace_append hprefix tailTrace_833600
  have hstable : (prefixWord ++ tailWord_833600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833600).length < 2 ^ (prefixWord ++ tailWord_833600).sum := by decide
  have hdescent : baseEnd_833600 < baseStart_833600 := by decide
  rcases family_descends (prefixWord ++ tailWord_833600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833656 : List Nat := [2, 1, 2, 1, 1, 1, 3, 1, 5, 5]
def baseStart_833656 : Nat := 118140960795 + 833656 * 2 ^ 59
def prefixEnd_833656 : Nat := 4983230072969 + 3 ^ 40 * 833656 * 2
def baseEnd_833656 : Nat := 285377485669797033844061

theorem tailTrace_833656 : CollatzResearch.WordTrace tailWord_833656 prefixEnd_833656 285377485669797033844061 := by
  unfold tailWord_833656
  simp only [CollatzResearch.WordTrace]
  refine ⟨15202966133907081977344411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20270621511876109303125881 15202966133907081977344411)
  ·
    refine ⟨22804449200860622966016617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15202966133907081977344411 22804449200860622966016617)
    ·
      refine ⟨17103336900645467224512463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22804449200860622966016617 17103336900645467224512463)
      ·
        refine ⟨25655005350968200836768695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17103336900645467224512463 25655005350968200836768695)
        ·
          refine ⟨38482508026452301255153043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25655005350968200836768695 38482508026452301255153043)
          ·
            refine ⟨57723762039678451882729565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38482508026452301255153043 57723762039678451882729565)
            ·
              refine ⟨21646410764879419456023587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57723762039678451882729565 21646410764879419456023587)
              ·
                refine ⟨32469616147319129184035381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21646410764879419456023587 32469616147319129184035381)
                ·
                  refine ⟨3044026513811168361003317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32469616147319129184035381 3044026513811168361003317)
                  ·
                    refine ⟨285377485669797033844061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3044026513811168361003317 285377485669797033844061)
                    ·
                      rfl

theorem cell22_833656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 1, 5, 5].length) (baseStart_833656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833656 prefixEnd_833656 := by exact prefixLift 833656
  have htrace : WordTrace (prefixWord ++ tailWord_833656) baseStart_833656 baseEnd_833656 := by
    simpa [prefixWord, tailWord_833656, baseEnd_833656] using wordTrace_append hprefix tailTrace_833656
  have hstable : (prefixWord ++ tailWord_833656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833656).length < 2 ^ (prefixWord ++ tailWord_833656).sum := by decide
  have hdescent : baseEnd_833656 < baseStart_833656 := by decide
  rcases family_descends (prefixWord ++ tailWord_833656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833673 : List Nat := [1, 2, 1, 1, 4, 2, 4, 1, 1, 5]
def baseStart_833673 : Nat := 118140960795 + 833673 * 2 ^ 59
def prefixEnd_833673 : Nat := 4983230072969 + 3 ^ 40 * 833673 * 2
def baseEnd_833673 : Nat := 285383305117214656169009

theorem tailTrace_833673 : CollatzResearch.WordTrace tailWord_833673 prefixEnd_833673 285383305117214656169009 := by
  unfold tailWord_833673
  simp only [CollatzResearch.WordTrace]
  refine ⟨30406552308752575858057673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20271034872501717238705115 30406552308752575858057673)
  ·
    refine ⟨22804914231564431893543255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30406552308752575858057673 22804914231564431893543255)
    ·
      refine ⟨34207371347346647840314883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22804914231564431893543255 34207371347346647840314883)
      ·
        refine ⟨51311057021019971760472325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34207371347346647840314883 51311057021019971760472325)
        ·
          refine ⟨9620823191441244705088561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51311057021019971760472325 9620823191441244705088561)
          ·
            refine ⟨7215617393580933528816421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9620823191441244705088561 7215617393580933528816421)
            ·
              refine ⟨1352928261296425036653079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7215617393580933528816421 1352928261296425036653079)
              ·
                refine ⟨2029392391944637554979619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1352928261296425036653079 2029392391944637554979619)
                ·
                  refine ⟨3044088587916956332469429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2029392391944637554979619 3044088587916956332469429)
                  ·
                    refine ⟨285383305117214656169009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3044088587916956332469429 285383305117214656169009)
                    ·
                      rfl

theorem cell22_833673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 4, 1, 1, 5].length) (baseStart_833673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833673 prefixEnd_833673 := by exact prefixLift 833673
  have htrace : WordTrace (prefixWord ++ tailWord_833673) baseStart_833673 baseEnd_833673 := by
    simpa [prefixWord, tailWord_833673, baseEnd_833673] using wordTrace_append hprefix tailTrace_833673
  have hstable : (prefixWord ++ tailWord_833673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833673).length < 2 ^ (prefixWord ++ tailWord_833673).sum := by decide
  have hdescent : baseEnd_833673 < baseStart_833673 := by decide
  rcases family_descends (prefixWord ++ tailWord_833673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833724 : List Nat := [2, 2, 2, 3, 3, 1, 3, 1, 2, 3]
def baseStart_833724 : Nat := 118140960795 + 833724 * 2 ^ 59
def prefixEnd_833724 : Nat := 4983230072969 + 3 ^ 40 * 833724 * 2
def baseEnd_833724 : Nat := 285400763459467523143853

theorem tailTrace_833724 : CollatzResearch.WordTrace tailWord_833724 prefixEnd_833724 285400763459467523143853 := by
  unfold tailWord_833724
  simp only [CollatzResearch.WordTrace]
  refine ⟨15204206215783905784082113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20272274954378541045442817 15204206215783905784082113)
  ·
    refine ⟨11403154661837929338061585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15204206215783905784082113 11403154661837929338061585)
    ·
      refine ⟨8552365996378447003546189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11403154661837929338061585 8552365996378447003546189)
      ·
        refine ⟨3207137248641917626329821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8552365996378447003546189 3207137248641917626329821)
        ·
          refine ⟨1202676468240719109873683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3207137248641917626329821 1202676468240719109873683)
          ·
            refine ⟨1804014702361078664810525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202676468240719109873683 1804014702361078664810525)
            ·
              refine ⟨676505513385404499303947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1804014702361078664810525 676505513385404499303947)
              ·
                refine ⟨1014758270078106748955921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676505513385404499303947 1014758270078106748955921)
                ·
                  refine ⟨761068702558580061716941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1014758270078106748955921 761068702558580061716941)
                  ·
                    refine ⟨285400763459467523143853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 761068702558580061716941 285400763459467523143853)
                    ·
                      rfl

theorem cell22_833724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_833724 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833724 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833724 prefixEnd_833724 := by exact prefixLift 833724
  have htrace : WordTrace (prefixWord ++ tailWord_833724) baseStart_833724 baseEnd_833724 := by
    simpa [prefixWord, tailWord_833724, baseEnd_833724] using wordTrace_append hprefix tailTrace_833724
  have hstable : (prefixWord ++ tailWord_833724).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833724).length < 2 ^ (prefixWord ++ tailWord_833724).sum := by decide
  have hdescent : baseEnd_833724 < baseStart_833724 := by decide
  rcases family_descends (prefixWord ++ tailWord_833724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833782 : List Nat := [5, 1, 1, 1, 1, 1, 6, 1, 5]
def baseStart_833782 : Nat := 118140960795 + 833782 * 2 ^ 59
def prefixEnd_833782 : Nat := 4983230072969 + 3 ^ 40 * 833782 * 2
def baseEnd_833782 : Nat := 95140206014924901731225

theorem tailTrace_833782 : CollatzResearch.WordTrace tailWord_833782 prefixEnd_833782 95140206014924901731225 := by
  unfold tailWord_833782
  simp only [CollatzResearch.WordTrace]
  refine ⟨1900657991584855467110975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 20273685243571791649183733 1900657991584855467110975)
  ·
    refine ⟨2850986987377283200666463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1900657991584855467110975 2850986987377283200666463)
    ·
      refine ⟨4276480481065924800999695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2850986987377283200666463 4276480481065924800999695)
      ·
        refine ⟨6414720721598887201499543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4276480481065924800999695 6414720721598887201499543)
        ·
          refine ⟨9622081082398330802249315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6414720721598887201499543 9622081082398330802249315)
          ·
            refine ⟨14433121623597496203373973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9622081082398330802249315 14433121623597496203373973)
            ·
              refine ⟨676552576106132634533155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14433121623597496203373973 676552576106132634533155)
              ·
                refine ⟨1014828864159198951799733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676552576106132634533155 1014828864159198951799733)
                ·
                  refine ⟨95140206014924901731225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 1014828864159198951799733 95140206014924901731225)
                  ·
                    rfl

theorem cell22_833782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_833782 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833782 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833782 prefixEnd_833782 := by exact prefixLift 833782
  have htrace : WordTrace (prefixWord ++ tailWord_833782) baseStart_833782 baseEnd_833782 := by
    simpa [prefixWord, tailWord_833782, baseEnd_833782] using wordTrace_append hprefix tailTrace_833782
  have hstable : (prefixWord ++ tailWord_833782).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833782).length < 2 ^ (prefixWord ++ tailWord_833782).sum := by decide
  have hdescent : baseEnd_833782 < baseStart_833782 := by decide
  rcases family_descends (prefixWord ++ tailWord_833782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833793 : List Nat := [1, 2, 4, 1, 1, 2, 2, 1, 8]
def baseStart_833793 : Nat := 118140960795 + 833793 * 2 ^ 59
def prefixEnd_833793 : Nat := 4983230072969 + 3 ^ 40 * 833793 * 2
def baseEnd_833793 : Nat := 95141461189858114389547

theorem tailTrace_833793 : CollatzResearch.WordTrace tailWord_833793 prefixEnd_833793 95141461189858114389547 := by
  unfold tailWord_833793
  simp only [CollatzResearch.WordTrace]
  refine ⟨30410929068317836352426033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20273952712211890901617355 30410929068317836352426033)
  ·
    refine ⟨22808196801238377264319525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30410929068317836352426033 22808196801238377264319525)
    ·
      refine ⟨4276536900232195737059911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22808196801238377264319525 4276536900232195737059911)
      ·
        refine ⟨6414805350348293605589867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4276536900232195737059911 6414805350348293605589867)
        ·
          refine ⟨9622208025522440408384801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6414805350348293605589867 9622208025522440408384801)
          ·
            refine ⟨7216656019141830306288601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9622208025522440408384801 7216656019141830306288601)
            ·
              refine ⟨5412492014356372729716451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7216656019141830306288601 5412492014356372729716451)
              ·
                refine ⟨8118738021534559094574677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5412492014356372729716451 8118738021534559094574677)
                ·
                  refine ⟨95141461189858114389547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 8118738021534559094574677 95141461189858114389547)
                  ·
                    rfl

theorem cell22_833793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 1, 8].length) (baseStart_833793 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833793 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833793 prefixEnd_833793 := by exact prefixLift 833793
  have htrace : WordTrace (prefixWord ++ tailWord_833793) baseStart_833793 baseEnd_833793 := by
    simpa [prefixWord, tailWord_833793, baseEnd_833793] using wordTrace_append hprefix tailTrace_833793
  have hstable : (prefixWord ++ tailWord_833793).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833793).length < 2 ^ (prefixWord ++ tailWord_833793).sum := by decide
  have hdescent : baseEnd_833793 < baseStart_833793 := by decide
  rcases family_descends (prefixWord ++ tailWord_833793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833825 : List Nat := [1, 2, 3, 2, 1, 1, 2, 3, 4, 3]
def baseStart_833825 : Nat := 118140960795 + 833825 * 2 ^ 59
def prefixEnd_833825 : Nat := 4983230072969 + 3 ^ 40 * 833825 * 2
def baseEnd_833825 : Nat := 285435337823536926368543

theorem tailTrace_833825 : CollatzResearch.WordTrace tailWord_833825 prefixEnd_833825 285435337823536926368543 := by
  unfold tailWord_833825
  simp only [CollatzResearch.WordTrace]
  refine ⟨30412096204201905817590929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20274730802801270545060619 30412096204201905817590929)
  ·
    refine ⟨22809072153151429363193197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30412096204201905817590929 22809072153151429363193197)
    ·
      refine ⟨8553402057431786011197449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22809072153151429363193197 8553402057431786011197449)
      ·
        refine ⟨6415051543073839508398087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8553402057431786011197449 6415051543073839508398087)
        ·
          refine ⟨9622577314610759262597131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6415051543073839508398087 9622577314610759262597131)
          ·
            refine ⟨14433865971916138893895697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9622577314610759262597131 14433865971916138893895697)
            ·
              refine ⟨10825399478937104170421773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14433865971916138893895697 10825399478937104170421773)
              ·
                refine ⟨4059524804601414063908165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10825399478937104170421773 4059524804601414063908165)
                ·
                  refine ⟨761160900862765136982781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4059524804601414063908165 761160900862765136982781)
                  ·
                    refine ⟨285435337823536926368543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 761160900862765136982781 285435337823536926368543)
                    ·
                      rfl

theorem cell22_833825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 3, 4, 3].length) (baseStart_833825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833825 prefixEnd_833825 := by exact prefixLift 833825
  have htrace : WordTrace (prefixWord ++ tailWord_833825) baseStart_833825 baseEnd_833825 := by
    simpa [prefixWord, tailWord_833825, baseEnd_833825] using wordTrace_append hprefix tailTrace_833825
  have hstable : (prefixWord ++ tailWord_833825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833825).length < 2 ^ (prefixWord ++ tailWord_833825).sum := by decide
  have hdescent : baseEnd_833825 < baseStart_833825 := by decide
  rcases family_descends (prefixWord ++ tailWord_833825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833842 : List Nat := [3, 2, 1, 1, 5, 1, 2, 1, 1, 5]
def baseStart_833842 : Nat := 118140960795 + 833842 * 2 ^ 59
def prefixEnd_833842 : Nat := 4983230072969 + 3 ^ 40 * 833842 * 2
def baseEnd_833842 : Nat := 285441157270954548693491

theorem tailTrace_833842 : CollatzResearch.WordTrace tailWord_833842 prefixEnd_833842 285441157270954548693491 := by
  unfold tailWord_833842
  simp only [CollatzResearch.WordTrace]
  refine ⟨7603179061285079430239945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 20275144163426878480639853 7603179061285079430239945)
  ·
    refine ⟨5702384295963809572679959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7603179061285079430239945 5702384295963809572679959)
    ·
      refine ⟨8553576443945714359019939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5702384295963809572679959 8553576443945714359019939)
      ·
        refine ⟨12830364665918571538529909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8553576443945714359019939 12830364665918571538529909)
        ·
          refine ⟨1202846687429866081737179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12830364665918571538529909 1202846687429866081737179)
          ·
            refine ⟨1804270031144799122605769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202846687429866081737179 1804270031144799122605769)
            ·
              refine ⟨1353202523358599341954327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1804270031144799122605769 1353202523358599341954327)
              ·
                refine ⟨2029803785037899012931491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1353202523358599341954327 2029803785037899012931491)
                ·
                  refine ⟨3044705677556848519397237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2029803785037899012931491 3044705677556848519397237)
                  ·
                    refine ⟨285441157270954548693491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3044705677556848519397237 285441157270954548693491)
                    ·
                      rfl

theorem cell22_833842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 5, 1, 2, 1, 1, 5].length) (baseStart_833842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833842 prefixEnd_833842 := by exact prefixLift 833842
  have htrace : WordTrace (prefixWord ++ tailWord_833842) baseStart_833842 baseEnd_833842 := by
    simpa [prefixWord, tailWord_833842, baseEnd_833842] using wordTrace_append hprefix tailTrace_833842
  have hstable : (prefixWord ++ tailWord_833842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833842).length < 2 ^ (prefixWord ++ tailWord_833842).sum := by decide
  have hdescent : baseEnd_833842 < baseStart_833842 := by decide
  rcases family_descends (prefixWord ++ tailWord_833842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833855 : List Nat := [1, 1, 2, 2, 4, 1, 5, 6]
def baseStart_833855 : Nat := 118140960795 + 833855 * 2 ^ 59
def prefixEnd_833855 : Nat := 4983230072969 + 3 ^ 40 * 833855 * 2
def baseEnd_833855 : Nat := 31716178604069649790939

theorem tailTrace_833855 : CollatzResearch.WordTrace tailWord_833855 prefixEnd_833855 31716178604069649790939 := by
  unfold tailWord_833855
  simp only [CollatzResearch.WordTrace]
  refine ⟨30413190394093220941183019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20275460262728813960788679 30413190394093220941183019)
  ·
    refine ⟨45619785591139831411774529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30413190394093220941183019 45619785591139831411774529)
    ·
      refine ⟨34214839193354873558830897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45619785591139831411774529 34214839193354873558830897)
      ·
        refine ⟨25661129395016155169123173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34214839193354873558830897 25661129395016155169123173)
        ·
          refine ⟨4811461761565529094210595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25661129395016155169123173 4811461761565529094210595)
          ·
            refine ⟨7217192642348293641315893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4811461761565529094210595 7217192642348293641315893)
            ·
              refine ⟨676611810220152528873365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7217192642348293641315893 676611810220152528873365)
              ·
                refine ⟨31716178604069649790939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 676611810220152528873365 31716178604069649790939)
                ·
                  rfl

theorem cell22_833855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 1, 5, 6].length) (baseStart_833855 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833855 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833855 prefixEnd_833855 := by exact prefixLift 833855
  have htrace : WordTrace (prefixWord ++ tailWord_833855) baseStart_833855 baseEnd_833855 := by
    simpa [prefixWord, tailWord_833855, baseEnd_833855] using wordTrace_append hprefix tailTrace_833855
  have hstable : (prefixWord ++ tailWord_833855).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833855).length < 2 ^ (prefixWord ++ tailWord_833855).sum := by decide
  have hdescent : baseEnd_833855 < baseStart_833855 := by decide
  rcases family_descends (prefixWord ++ tailWord_833855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833857 : List Nat := [1, 2, 5, 2, 2, 1, 1, 1, 1, 6]
def baseStart_833857 : Nat := 118140960795 + 833857 * 2 ^ 59
def prefixEnd_833857 : Nat := 4983230072969 + 3 ^ 40 * 833857 * 2
def baseEnd_833857 : Nat := 285446292077499509568445

theorem tailTrace_833857 : CollatzResearch.WordTrace tailWord_833857 prefixEnd_833857 285446292077499509568445 := by
  unfold tailWord_833857
  simp only [CollatzResearch.WordTrace]
  refine ⟨30413263340085975282755825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20275508893390650188503883 30413263340085975282755825)
  ·
    refine ⟨22809947505064481462066869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30413263340085975282755825 22809947505064481462066869)
    ·
      refine ⟨2138432578599795137068769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22809947505064481462066869 2138432578599795137068769)
      ·
        refine ⟨1603824433949846352801577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2138432578599795137068769 1603824433949846352801577)
        ·
          refine ⟨1202868325462384764601183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1603824433949846352801577 1202868325462384764601183)
          ·
            refine ⟨1804302488193577146901775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202868325462384764601183 1804302488193577146901775)
            ·
              refine ⟨2706453732290365720352663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1804302488193577146901775 2706453732290365720352663)
              ·
                refine ⟨4059680598435548580528995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2706453732290365720352663 4059680598435548580528995)
                ·
                  refine ⟨6089520897653322870793493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4059680598435548580528995 6089520897653322870793493)
                  ·
                    refine ⟨285446292077499509568445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 6089520897653322870793493 285446292077499509568445)
                    ·
                      rfl

theorem cell22_833857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 2, 1, 1, 1, 1, 6].length) (baseStart_833857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833857 prefixEnd_833857 := by exact prefixLift 833857
  have htrace : WordTrace (prefixWord ++ tailWord_833857) baseStart_833857 baseEnd_833857 := by
    simpa [prefixWord, tailWord_833857, baseEnd_833857] using wordTrace_append hprefix tailTrace_833857
  have hstable : (prefixWord ++ tailWord_833857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833857).length < 2 ^ (prefixWord ++ tailWord_833857).sum := by decide
  have hdescent : baseEnd_833857 < baseStart_833857 := by decide
  rcases family_descends (prefixWord ++ tailWord_833857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833921 : List Nat := [1, 2, 4, 3, 1, 1, 3, 3, 1, 3]
def baseStart_833921 : Nat := 118140960795 + 833921 * 2 ^ 59
def prefixEnd_833921 : Nat := 4983230072969 + 3 ^ 40 * 833921 * 2
def baseEnd_833921 : Nat := 285468200585424675968249

theorem tailTrace_833921 : CollatzResearch.WordTrace tailWord_833921 prefixEnd_833921 285468200585424675968249 := by
  unfold tailWord_833921
  simp only [CollatzResearch.WordTrace]
  refine ⟨30415597611854114213085617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20277065074569409475390411 30415597611854114213085617)
  ·
    refine ⟨22811698208890585659814213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30415597611854114213085617 22811698208890585659814213)
    ·
      refine ⟨4277193414166984811215165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22811698208890585659814213 4277193414166984811215165)
      ·
        refine ⟨1603947530312619304205687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4277193414166984811215165 1603947530312619304205687)
        ·
          refine ⟨2405921295468928956308531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1603947530312619304205687 2405921295468928956308531)
          ·
            refine ⟨3608881943203393434462797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2405921295468928956308531 3608881943203393434462797)
            ·
              refine ⟨1353330728701272537923549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3608881943203393434462797 1353330728701272537923549)
              ·
                refine ⟨507499023262977201721331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1353330728701272537923549 507499023262977201721331)
                ·
                  refine ⟨761248534894465802581997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 507499023262977201721331 761248534894465802581997)
                  ·
                    refine ⟨285468200585424675968249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 761248534894465802581997 285468200585424675968249)
                    ·
                      rfl

theorem cell22_833921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 3, 3, 1, 3].length) (baseStart_833921 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833921 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833921 prefixEnd_833921 := by exact prefixLift 833921
  have htrace : WordTrace (prefixWord ++ tailWord_833921) baseStart_833921 baseEnd_833921 := by
    simpa [prefixWord, tailWord_833921, baseEnd_833921] using wordTrace_append hprefix tailTrace_833921
  have hstable : (prefixWord ++ tailWord_833921).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833921).length < 2 ^ (prefixWord ++ tailWord_833921).sum := by decide
  have hdescent : baseEnd_833921 < baseStart_833921 := by decide
  rcases family_descends (prefixWord ++ tailWord_833921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833977 : List Nat := [1, 2, 1, 4, 3, 2, 1, 2, 1, 5]
def baseStart_833977 : Nat := 118140960795 + 833977 * 2 ^ 59
def prefixEnd_833977 : Nat := 4983230072969 + 3 ^ 40 * 833977 * 2
def baseEnd_833977 : Nat := 285487370529859196568077

theorem tailTrace_833977 : CollatzResearch.WordTrace tailWord_833977 prefixEnd_833977 285487370529859196568077 := by
  unfold tailWord_833977
  simp only [CollatzResearch.WordTrace]
  refine ⟨30417640099651235777124185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 20278426733100823851416123 30417640099651235777124185)
  ·
    refine ⟨22813230074738426832843139, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30417640099651235777124185 22813230074738426832843139)
    ·
      refine ⟨34219845112107640249264709, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22813230074738426832843139 34219845112107640249264709)
      ·
        refine ⟨6416220958520182546737133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34219845112107640249264709 6416220958520182546737133)
        ·
          refine ⟨2406082859445068455026425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6416220958520182546737133 2406082859445068455026425)
          ·
            refine ⟨1804562144583801341269819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2406082859445068455026425 1804562144583801341269819)
            ·
              refine ⟨2706843216875702011904729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1804562144583801341269819 2706843216875702011904729)
              ·
                refine ⟨2030132412656776508928547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2706843216875702011904729 2030132412656776508928547)
                ·
                  refine ⟨3045198618985164763392821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2030132412656776508928547 3045198618985164763392821)
                  ·
                    refine ⟨285487370529859196568077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 3045198618985164763392821 285487370529859196568077)
                    ·
                      rfl

theorem cell22_833977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 1, 2, 1, 5].length) (baseStart_833977 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833977 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833977 prefixEnd_833977 := by exact prefixLift 833977
  have htrace : WordTrace (prefixWord ++ tailWord_833977) baseStart_833977 baseEnd_833977 := by
    simpa [prefixWord, tailWord_833977, baseEnd_833977] using wordTrace_append hprefix tailTrace_833977
  have hstable : (prefixWord ++ tailWord_833977).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833977).length < 2 ^ (prefixWord ++ tailWord_833977).sum := by decide
  have hdescent : baseEnd_833977 < baseStart_833977 := by decide
  rcases family_descends (prefixWord ++ tailWord_833977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_833992 : List Nat := [2, 1, 3, 1, 3, 2, 2, 2, 2, 4]
def baseStart_833992 : Nat := 118140960795 + 833992 * 2 ^ 59
def prefixEnd_833992 : Nat := 4983230072969 + 3 ^ 40 * 833992 * 2
def baseEnd_833992 : Nat := 285492505336404157443031

theorem tailTrace_833992 : CollatzResearch.WordTrace tailWord_833992 prefixEnd_833992 285492505336404157443031 := by
  unfold tailWord_833992
  simp only [CollatzResearch.WordTrace]
  refine ⟨15209093597298446669460115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 20278791463064595559280153 15209093597298446669460115)
  ·
    refine ⟨22813640395947670004190173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15209093597298446669460115 22813640395947670004190173)
    ·
      refine ⟨8555115148480376251571315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22813640395947670004190173 8555115148480376251571315)
      ·
        refine ⟨12832672722720564377356973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8555115148480376251571315 12832672722720564377356973)
        ·
          refine ⟨4812252271020211641508865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12832672722720564377356973 4812252271020211641508865)
          ·
            refine ⟨3609189203265158731131649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4812252271020211641508865 3609189203265158731131649)
            ·
              refine ⟨2706891902448869048348737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3609189203265158731131649 2706891902448869048348737)
              ·
                refine ⟨2030168926836651786261553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2706891902448869048348737 2030168926836651786261553)
                ·
                  refine ⟨1522626695127488839696165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2030168926836651786261553 1522626695127488839696165)
                  ·
                    refine ⟨285492505336404157443031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1522626695127488839696165 285492505336404157443031)
                    ·
                      rfl

theorem cell22_833992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 2, 2, 2, 2, 4].length) (baseStart_833992 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_833992 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_833992 prefixEnd_833992 := by exact prefixLift 833992
  have htrace : WordTrace (prefixWord ++ tailWord_833992) baseStart_833992 baseEnd_833992 := by
    simpa [prefixWord, tailWord_833992, baseEnd_833992] using wordTrace_append hprefix tailTrace_833992
  have hstable : (prefixWord ++ tailWord_833992).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_833992).length < 2 ^ (prefixWord ++ tailWord_833992).sum := by decide
  have hdescent : baseEnd_833992 < baseStart_833992 := by decide
  rcases family_descends (prefixWord ++ tailWord_833992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
