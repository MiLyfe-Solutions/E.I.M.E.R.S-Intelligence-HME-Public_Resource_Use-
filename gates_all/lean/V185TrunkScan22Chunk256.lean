import V185TrunkScan22Chunk255

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_2282580 : List Nat := [2, 4, 1, 1, 1, 1, 3, 3, 1, 5]
def baseStart_2282580 : Nat := 118140960795 + 2282580 * 2 ^ 59
def prefixEnd_2282580 : Nat := 4983230072969 + 3 ^ 40 * 2282580 * 2
def baseEnd_2282580 : Nat := 781373781559856419301741

theorem tailTrace_2282580 : CollatzResearch.WordTrace tailWord_2282580 prefixEnd_2282580 781373781559856419301741 := by
  unfold tailWord_2282580
  simp only [CollatzResearch.WordTrace]
  refine ⟨41626266035304984236434597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55501688047073312315246129 41626266035304984236434597)
  ·
    refine ⟨7804924881619684544331487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41626266035304984236434597 7804924881619684544331487)
    ·
      refine ⟨11707387322429526816497231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7804924881619684544331487 11707387322429526816497231)
      ·
        refine ⟨17561080983644290224745847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11707387322429526816497231 17561080983644290224745847)
        ·
          refine ⟨26341621475466435337118771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17561080983644290224745847 26341621475466435337118771)
          ·
            refine ⟨39512432213199653005678157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26341621475466435337118771 39512432213199653005678157)
            ·
              refine ⟨14817162079949869877129309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39512432213199653005678157 14817162079949869877129309)
              ·
                refine ⟨5556435779981201203923491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14817162079949869877129309 5556435779981201203923491)
                ·
                  refine ⟨8334653669971801805885237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5556435779981201203923491 8334653669971801805885237)
                  ·
                    refine ⟨781373781559856419301741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8334653669971801805885237 781373781559856419301741)
                    ·
                      rfl

theorem cell22_2282580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 3, 3, 1, 5].length) (baseStart_2282580 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282580 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282580 prefixEnd_2282580 := by exact prefixLift 2282580
  have htrace : WordTrace (prefixWord ++ tailWord_2282580) baseStart_2282580 baseEnd_2282580 := by
    simpa [prefixWord, tailWord_2282580, baseEnd_2282580] using wordTrace_append hprefix tailTrace_2282580
  have hstable : (prefixWord ++ tailWord_2282580).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282580).length < 2 ^ (prefixWord ++ tailWord_2282580).sum := by decide
  have hdescent : baseEnd_2282580 < baseStart_2282580 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282593 : List Nat := [1, 2, 3, 1, 1, 2, 2, 10]
def baseStart_2282593 : Nat := 118140960795 + 2282593 * 2 ^ 59
def prefixEnd_2282593 : Nat := 4983230072969 + 3 ^ 40 * 2282593 * 2
def baseEnd_2282593 : Nat := 86819803525058746525189

theorem tailTrace_2282593 : CollatzResearch.WordTrace tailWord_2282593 prefixEnd_2282593 86819803525058746525189 := by
  unfold tailWord_2282593
  simp only [CollatzResearch.WordTrace]
  refine ⟨83253006219562871693092433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55502004146375247795394955 83253006219562871693092433)
  ·
    refine ⟨62439754664672153769819325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83253006219562871693092433 62439754664672153769819325)
    ·
      refine ⟨23414907999252057663682247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62439754664672153769819325 23414907999252057663682247)
      ·
        refine ⟨35122361998878086495523371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23414907999252057663682247 35122361998878086495523371)
        ·
          refine ⟨52683542998317129743285057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35122361998878086495523371 52683542998317129743285057)
          ·
            refine ⟨39512657248737847307463793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52683542998317129743285057 39512657248737847307463793)
            ·
              refine ⟨29634492936553385480597845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39512657248737847307463793 29634492936553385480597845)
              ·
                refine ⟨86819803525058746525189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29634492936553385480597845 86819803525058746525189)
                ·
                  rfl

theorem cell22_2282593_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 10].length) (baseStart_2282593 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282593 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282593 prefixEnd_2282593 := by exact prefixLift 2282593
  have htrace : WordTrace (prefixWord ++ tailWord_2282593) baseStart_2282593 baseEnd_2282593 := by
    simpa [prefixWord, tailWord_2282593, baseEnd_2282593] using wordTrace_append hprefix tailTrace_2282593
  have hstable : (prefixWord ++ tailWord_2282593).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282593).length < 2 ^ (prefixWord ++ tailWord_2282593).sum := by decide
  have hdescent : baseEnd_2282593 < baseStart_2282593 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282593) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282689 : List Nat := [1, 2, 6, 1, 1, 2, 1, 3, 5]
def baseStart_2282689 : Nat := 118140960795 + 2282689 * 2 ^ 59
def prefixEnd_2282689 : Nat := 4983230072969 + 3 ^ 40 * 2282689 * 2
def baseEnd_2282689 : Nat := 260470364829138822775469

theorem tailTrace_2282689 : CollatzResearch.WordTrace tailWord_2282689 prefixEnd_2282689 260470364829138822775469 := by
  unfold tailWord_2282689
  simp only [CollatzResearch.WordTrace]
  refine ⟨83256507627215080088587121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55504338418143386725724747 83256507627215080088587121)
  ·
    refine ⟨62442380720411310066440341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83256507627215080088587121 62442380720411310066440341)
    ·
      refine ⟨2926986596269280159364391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 62442380720411310066440341 2926986596269280159364391)
      ·
        refine ⟨4390479894403920239046587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2926986596269280159364391 4390479894403920239046587)
        ·
          refine ⟨6585719841605880358569881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4390479894403920239046587 6585719841605880358569881)
          ·
            refine ⟨4939289881204410268927411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6585719841605880358569881 4939289881204410268927411)
            ·
              refine ⟨7408934821806615403391117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4939289881204410268927411 7408934821806615403391117)
              ·
                refine ⟨2778350558177480776271669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7408934821806615403391117 2778350558177480776271669)
                ·
                  refine ⟨260470364829138822775469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2778350558177480776271669 260470364829138822775469)
                  ·
                    rfl

theorem cell22_2282689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 3, 5].length) (baseStart_2282689 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282689 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282689 prefixEnd_2282689 := by exact prefixLift 2282689
  have htrace : WordTrace (prefixWord ++ tailWord_2282689) baseStart_2282689 baseEnd_2282689 := by
    simpa [prefixWord, tailWord_2282689, baseEnd_2282689] using wordTrace_append hprefix tailTrace_2282689
  have hstable : (prefixWord ++ tailWord_2282689).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282689).length < 2 ^ (prefixWord ++ tailWord_2282689).sum := by decide
  have hdescent : baseEnd_2282689 < baseStart_2282689 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282764 : List Nat := [2, 2, 1, 2, 2, 5, 1, 1, 2, 4]
def baseStart_2282764 : Nat := 118140960795 + 2282764 * 2 ^ 59
def prefixEnd_2282764 : Nat := 4983230072969 + 3 ^ 40 * 2282764 * 2
def baseEnd_2282764 : Nat := 781436768520141272701177

theorem tailTrace_2282764 : CollatzResearch.WordTrace tailWord_2282764 prefixEnd_2282764 781436768520141272701177 := by
  unfold tailWord_2282764
  simp only [CollatzResearch.WordTrace]
  refine ⟨41629621550971683948783673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55506162067962245265044897 41629621550971683948783673)
  ·
    refine ⟨31222216163228762961587755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41629621550971683948783673 31222216163228762961587755)
    ·
      refine ⟨46833324244843144442381633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31222216163228762961587755 46833324244843144442381633)
      ·
        refine ⟨35124993183632358331786225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46833324244843144442381633 35124993183632358331786225)
        ·
          refine ⟨26343744887724268748839669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35124993183632358331786225 26343744887724268748839669)
          ·
            refine ⟨2469726083224150195203719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26343744887724268748839669 2469726083224150195203719)
            ·
              refine ⟨3704589124836225292805579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2469726083224150195203719 3704589124836225292805579)
              ·
                refine ⟨5556883687254337939208369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3704589124836225292805579 5556883687254337939208369)
                ·
                  refine ⟨4167662765440753454406277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5556883687254337939208369 4167662765440753454406277)
                  ·
                    refine ⟨781436768520141272701177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4167662765440753454406277 781436768520141272701177)
                    ·
                      rfl

theorem cell22_2282764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 5, 1, 1, 2, 4].length) (baseStart_2282764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282764 prefixEnd_2282764 := by exact prefixLift 2282764
  have htrace : WordTrace (prefixWord ++ tailWord_2282764) baseStart_2282764 baseEnd_2282764 := by
    simpa [prefixWord, tailWord_2282764, baseEnd_2282764] using wordTrace_append hprefix tailTrace_2282764
  have hstable : (prefixWord ++ tailWord_2282764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282764).length < 2 ^ (prefixWord ++ tailWord_2282764).sum := by decide
  have hdescent : baseEnd_2282764 < baseStart_2282764 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282770 : List Nat := [3, 2, 4, 2, 1, 2, 2, 1, 1, 4]
def baseStart_2282770 : Nat := 118140960795 + 2282770 * 2 ^ 59
def prefixEnd_2282770 : Nat := 4983230072969 + 3 ^ 40 * 2282770 * 2
def baseEnd_2282770 : Nat := 781438822442759257051159

theorem tailTrace_2282770 : CollatzResearch.WordTrace tailWord_2282770 prefixEnd_2282770 781438822442759257051159 := by
  unfold tailWord_2282770
  simp only [CollatzResearch.WordTrace]
  refine ⟨20814865484980407730571441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55506307959947753948190509 20814865484980407730571441)
  ·
    refine ⟨15611149113735305797928581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20814865484980407730571441 15611149113735305797928581)
    ·
      refine ⟨2927090458825369837111609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15611149113735305797928581 2927090458825369837111609)
      ·
        refine ⟨2195317844119027377833707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2927090458825369837111609 2195317844119027377833707)
        ·
          refine ⟨3292976766178541066750561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2195317844119027377833707 3292976766178541066750561)
          ·
            refine ⟨2469732574633905800062921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3292976766178541066750561 2469732574633905800062921)
            ·
              refine ⟨1852299430975429350047191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2469732574633905800062921 1852299430975429350047191)
              ·
                refine ⟨2778449146463144025070787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1852299430975429350047191 2778449146463144025070787)
                ·
                  refine ⟨4167673719694716037606181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2778449146463144025070787 4167673719694716037606181)
                  ·
                    refine ⟨781438822442759257051159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4167673719694716037606181 781438822442759257051159)
                    ·
                      rfl

theorem cell22_2282770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 2, 1, 1, 4].length) (baseStart_2282770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282770 prefixEnd_2282770 := by exact prefixLift 2282770
  have htrace : WordTrace (prefixWord ++ tailWord_2282770) baseStart_2282770 baseEnd_2282770 := by
    simpa [prefixWord, tailWord_2282770, baseEnd_2282770] using wordTrace_append hprefix tailTrace_2282770
  have hstable : (prefixWord ++ tailWord_2282770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282770).length < 2 ^ (prefixWord ++ tailWord_2282770).sum := by decide
  have hdescent : baseEnd_2282770 < baseStart_2282770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282783 : List Nat := [1, 1, 2, 4, 5, 1, 1, 2, 2, 3]
def baseStart_2282783 : Nat := 118140960795 + 2282783 * 2 ^ 59
def prefixEnd_2282783 : Nat := 4983230072969 + 3 ^ 40 * 2282783 * 2
def baseEnd_2282783 : Nat := 781443272608431556476119

theorem tailTrace_2282783 : CollatzResearch.WordTrace tailWord_2282783 prefixEnd_2282783 781443272608431556476119 := by
  unfold tailWord_2282783
  simp only [CollatzResearch.WordTrace]
  refine ⟨83259936088874534142509003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55506624059249689428339335 83259936088874534142509003)
  ·
    refine ⟨124889904133311801213763505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83259936088874534142509003 124889904133311801213763505)
    ·
      refine ⟨93667428099983850910322629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124889904133311801213763505 93667428099983850910322629)
      ·
        refine ⟨17562642768746972045685493, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93667428099983850910322629 17562642768746972045685493)
        ·
          refine ⟨1646497759570028629283015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 17562642768746972045685493 1646497759570028629283015)
          ·
            refine ⟨2469746639355042943924523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1646497759570028629283015 2469746639355042943924523)
            ·
              refine ⟨3704619959032564415886785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2469746639355042943924523 3704619959032564415886785)
              ·
                refine ⟨2778464969274423311915089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3704619959032564415886785 2778464969274423311915089)
                ·
                  refine ⟨2083848726955817483936317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2778464969274423311915089 2083848726955817483936317)
                  ·
                    refine ⟨781443272608431556476119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2083848726955817483936317 781443272608431556476119)
                    ·
                      rfl

theorem cell22_2282783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 5, 1, 1, 2, 2, 3].length) (baseStart_2282783 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282783 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282783 prefixEnd_2282783 := by exact prefixLift 2282783
  have htrace : WordTrace (prefixWord ++ tailWord_2282783) baseStart_2282783 baseEnd_2282783 := by
    simpa [prefixWord, tailWord_2282783, baseEnd_2282783] using wordTrace_append hprefix tailTrace_2282783
  have hstable : (prefixWord ++ tailWord_2282783).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282783).length < 2 ^ (prefixWord ++ tailWord_2282783).sum := by decide
  have hdescent : baseEnd_2282783 < baseStart_2282783 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282813 : List Nat := [1, 4, 1, 5, 2, 1, 2, 6]
def baseStart_2282813 : Nat := 118140960795 + 2282813 * 2 ^ 59
def prefixEnd_2282813 : Nat := 4983230072969 + 3 ^ 40 * 2282813 * 2
def baseEnd_2282813 : Nat := 86828171357946830914003

theorem tailTrace_2282813 : CollatzResearch.WordTrace tailWord_2282813 prefixEnd_2282813 86828171357946830914003 := by
  unfold tailWord_2282813
  simp only [CollatzResearch.WordTrace]
  refine ⟨83261030278765849266101093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55507353519177232844067395 83261030278765849266101093)
  ·
    refine ⟨15611443177268596737393955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83261030278765849266101093 15611443177268596737393955)
    ·
      refine ⟨23417164765902895106090933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15611443177268596737393955 23417164765902895106090933)
      ·
        refine ⟨2195359196803396416196025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 23417164765902895106090933 2195359196803396416196025)
        ·
          refine ⟨1646519397602547312147019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2195359196803396416196025 1646519397602547312147019)
          ·
            refine ⟨2469779096403820968220529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1646519397602547312147019 2469779096403820968220529)
            ·
              refine ⟨1852334322302865726165397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2469779096403820968220529 1852334322302865726165397)
              ·
                refine ⟨86828171357946830914003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1852334322302865726165397 86828171357946830914003)
                ·
                  rfl

theorem cell22_2282813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 2, 6].length) (baseStart_2282813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282813 prefixEnd_2282813 := by exact prefixLift 2282813
  have htrace : WordTrace (prefixWord ++ tailWord_2282813) baseStart_2282813 baseEnd_2282813 := by
    simpa [prefixWord, tailWord_2282813, baseEnd_2282813] using wordTrace_append hprefix tailTrace_2282813
  have hstable : (prefixWord ++ tailWord_2282813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282813).length < 2 ^ (prefixWord ++ tailWord_2282813).sum := by decide
  have hdescent : baseEnd_2282813 < baseStart_2282813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282828 : List Nat := [2, 2, 1, 3, 2, 4, 1, 3, 1, 3]
def baseStart_2282828 : Nat := 118140960795 + 2282828 * 2 ^ 59
def prefixEnd_2282828 : Nat := 4983230072969 + 3 ^ 40 * 2282828 * 2
def baseEnd_2282828 : Nat := 781458677028066439100981

theorem tailTrace_2282828 : CollatzResearch.WordTrace tailWord_2282828 prefixEnd_2282828 781458677028066439100981 := by
  unfold tailWord_2282828
  simp only [CollatzResearch.WordTrace]
  refine ⟨41630788686855753413948569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55507718249141004551931425 41630788686855753413948569)
  ·
    refine ⟨31223091515141815060461427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41630788686855753413948569 31223091515141815060461427)
    ·
      refine ⟨46834637272712722590692141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31223091515141815060461427 46834637272712722590692141)
      ·
        refine ⟨17562988977267270971509553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46834637272712722590692141 17562988977267270971509553)
        ·
          refine ⟨13172241732950453228632165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17562988977267270971509553 13172241732950453228632165)
          ·
            refine ⟨2469795324928209980368531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13172241732950453228632165 2469795324928209980368531)
            ·
              refine ⟨3704692987392314970552797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2469795324928209980368531 3704692987392314970552797)
              ·
                refine ⟨1389259870272118113957299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3704692987392314970552797 1389259870272118113957299)
                ·
                  refine ⟨2083889805408177170935949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1389259870272118113957299 2083889805408177170935949)
                  ·
                    refine ⟨781458677028066439100981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2083889805408177170935949 781458677028066439100981)
                    ·
                      rfl

theorem cell22_2282828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 4, 1, 3, 1, 3].length) (baseStart_2282828 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282828 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282828 prefixEnd_2282828 := by exact prefixLift 2282828
  have htrace : WordTrace (prefixWord ++ tailWord_2282828) baseStart_2282828 baseEnd_2282828 := by
    simpa [prefixWord, tailWord_2282828, baseEnd_2282828] using wordTrace_append hprefix tailTrace_2282828
  have hstable : (prefixWord ++ tailWord_2282828).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282828).length < 2 ^ (prefixWord ++ tailWord_2282828).sum := by decide
  have hdescent : baseEnd_2282828 < baseStart_2282828 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282858 : List Nat := [3, 1, 3, 3, 2, 2, 2, 1, 5]
def baseStart_2282858 : Nat := 118140960795 + 2282858 * 2 ^ 59
def prefixEnd_2282858 : Nat := 4983230072969 + 3 ^ 40 * 2282858 * 2
def baseEnd_2282858 : Nat := 260489648880385453616963

theorem tailTrace_2282858 : CollatzResearch.WordTrace tailWord_2282858 prefixEnd_2282858 260489648880385453616963 := by
  unfold tailWord_2282858
  simp only [CollatzResearch.WordTrace]
  refine ⟨20815667890900705487872307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55508447709068547967659485 20815667890900705487872307)
  ·
    refine ⟨31223501836351058231808461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20815667890900705487872307 31223501836351058231808461)
    ·
      refine ⟨11708813188631646836928173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31223501836351058231808461 11708813188631646836928173)
      ·
        refine ⟨4390804945736867563848065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11708813188631646836928173 4390804945736867563848065)
        ·
          refine ⟨3293103709302650672886049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4390804945736867563848065 3293103709302650672886049)
          ·
            refine ⟨2469827781976988004664537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3293103709302650672886049 2469827781976988004664537)
            ·
              refine ⟨1852370836482741003498403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2469827781976988004664537 1852370836482741003498403)
              ·
                refine ⟨2778556254724111505247605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1852370836482741003498403 2778556254724111505247605)
                ·
                  refine ⟨260489648880385453616963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2778556254724111505247605 260489648880385453616963)
                  ·
                    rfl

theorem cell22_2282858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 2, 2, 2, 1, 5].length) (baseStart_2282858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282858 prefixEnd_2282858 := by exact prefixLift 2282858
  have htrace : WordTrace (prefixWord ++ tailWord_2282858) baseStart_2282858 baseEnd_2282858 := by
    simpa [prefixWord, tailWord_2282858, baseEnd_2282858] using wordTrace_append hprefix tailTrace_2282858
  have hstable : (prefixWord ++ tailWord_2282858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282858).length < 2 ^ (prefixWord ++ tailWord_2282858).sum := by decide
  have hdescent : baseEnd_2282858 < baseStart_2282858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282884 : List Nat := [2, 3, 2, 1, 1, 4, 1, 2, 1, 5]
def baseStart_2282884 : Nat := 118140960795 + 2282884 * 2 ^ 59
def prefixEnd_2282884 : Nat := 4983230072969 + 3 ^ 40 * 2282884 * 2
def baseEnd_2282884 : Nat := 781477846972500959700809

theorem tailTrace_2282884 : CollatzResearch.WordTrace tailWord_2282884 prefixEnd_2282884 781477846972500959700809 := by
  unfold tailWord_2282884
  simp only [CollatzResearch.WordTrace]
  refine ⟨41631809930754314195967853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55509079907672418927957137 41631809930754314195967853)
  ·
    refine ⟨15611928724032867823487945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41631809930754314195967853 15611928724032867823487945)
    ·
      refine ⟨11708946543024650867615959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15611928724032867823487945 11708946543024650867615959)
      ·
        refine ⟨17563419814536976301423939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11708946543024650867615959 17563419814536976301423939)
        ·
          refine ⟨26345129721805464452135909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17563419814536976301423939 26345129721805464452135909)
          ·
            refine ⟨4939711822838524584775483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26345129721805464452135909 4939711822838524584775483)
            ·
              refine ⟨7409567734257786877163225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4939711822838524584775483 7409567734257786877163225)
              ·
                refine ⟨5557175800693340157872419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7409567734257786877163225 5557175800693340157872419)
                ·
                  refine ⟨8335763701040010236808629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5557175800693340157872419 8335763701040010236808629)
                  ·
                    refine ⟨781477846972500959700809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8335763701040010236808629 781477846972500959700809)
                    ·
                      rfl

theorem cell22_2282884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 1, 2, 1, 5].length) (baseStart_2282884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282884 prefixEnd_2282884 := by exact prefixLift 2282884
  have htrace : WordTrace (prefixWord ++ tailWord_2282884) baseStart_2282884 baseEnd_2282884 := by
    simpa [prefixWord, tailWord_2282884, baseEnd_2282884] using wordTrace_append hprefix tailTrace_2282884
  have hstable : (prefixWord ++ tailWord_2282884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282884).length < 2 ^ (prefixWord ++ tailWord_2282884).sum := by decide
  have hdescent : baseEnd_2282884 < baseStart_2282884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282914 : List Nat := [3, 3, 1, 2, 1, 2, 3, 7]
def baseStart_2282914 : Nat := 118140960795 + 2282914 * 2 ^ 59
def prefixEnd_2282914 : Nat := 4983230072969 + 3 ^ 40 * 2282914 * 2
def baseEnd_2282914 : Nat := 86832012953954542383413

theorem tailTrace_2282914 : CollatzResearch.WordTrace tailWord_2282914 prefixEnd_2282914 86832012953954542383413 := by
  unfold tailWord_2282914
  simp only [CollatzResearch.WordTrace]
  refine ⟨20816178512849985878881949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55509809367599962343685197 20816178512849985878881949)
  ·
    refine ⟨7806066942318744704580731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20816178512849985878881949 7806066942318744704580731)
    ·
      refine ⟨11709100413478117056871097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7806066942318744704580731 11709100413478117056871097)
      ·
        refine ⟨8781825310108587792653323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11709100413478117056871097 8781825310108587792653323)
        ·
          refine ⟨13172737965162881688979985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8781825310108587792653323 13172737965162881688979985)
          ·
            refine ⟨9879553473872161266734989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13172737965162881688979985 9879553473872161266734989)
            ·
              refine ⟨3704832552702060475025621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9879553473872161266734989 3704832552702060475025621)
              ·
                refine ⟨86832012953954542383413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3704832552702060475025621 86832012953954542383413)
                ·
                  rfl

theorem cell22_2282914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 3, 7].length) (baseStart_2282914 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282914 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282914 prefixEnd_2282914 := by exact prefixLift 2282914
  have htrace : WordTrace (prefixWord ++ tailWord_2282914) baseStart_2282914 baseEnd_2282914 := by
    simpa [prefixWord, tailWord_2282914, baseEnd_2282914] using wordTrace_append hprefix tailTrace_2282914
  have hstable : (prefixWord ++ tailWord_2282914).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282914).length < 2 ^ (prefixWord ++ tailWord_2282914).sum := by decide
  have hdescent : baseEnd_2282914 < baseStart_2282914 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282959 : List Nat := [1, 1, 2, 1, 1, 4, 5, 2, 5]
def baseStart_2282959 : Nat := 118140960795 + 2282959 * 2 ^ 59
def prefixEnd_2282959 : Nat := 4983230072969 + 3 ^ 40 * 2282959 * 2
def baseEnd_2282959 : Nat := 260501173668408588025193

theorem tailTrace_2282959 : CollatzResearch.WordTrace tailWord_2282959 prefixEnd_2282959 260501173668408588025193 := by
  unfold tailWord_2282959
  simp only [CollatzResearch.WordTrace]
  refine ⟨83266355336236916200915931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55510903557491277467277287 83266355336236916200915931)
  ·
    refine ⟨124899533004355374301373897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83266355336236916200915931 124899533004355374301373897)
    ·
      refine ⟨93674649753266530726030423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124899533004355374301373897 93674649753266530726030423)
      ·
        refine ⟨140511974629899796089045635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93674649753266530726030423 140511974629899796089045635)
        ·
          refine ⟨210767961944849694133568453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140511974629899796089045635 210767961944849694133568453)
          ·
            refine ⟨39518992864659317650044085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 210767961944849694133568453 39518992864659317650044085)
            ·
              refine ⟨3704905581061811029691633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39518992864659317650044085 3704905581061811029691633)
              ·
                refine ⟨2778679185796358272268725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3704905581061811029691633 2778679185796358272268725)
                ·
                  refine ⟨260501173668408588025193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2778679185796358272268725 260501173668408588025193)
                  ·
                    rfl

theorem cell22_2282959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 5, 2, 5].length) (baseStart_2282959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282959 prefixEnd_2282959 := by exact prefixLift 2282959
  have htrace : WordTrace (prefixWord ++ tailWord_2282959) baseStart_2282959 baseEnd_2282959 := by
    simpa [prefixWord, tailWord_2282959, baseEnd_2282959] using wordTrace_append hprefix tailTrace_2282959
  have hstable : (prefixWord ++ tailWord_2282959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282959).length < 2 ^ (prefixWord ++ tailWord_2282959).sum := by decide
  have hdescent : baseEnd_2282959 < baseStart_2282959 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282987 : List Nat := [1, 1, 1, 1, 2, 3, 2, 3, 8]
def baseStart_2282987 : Nat := 118140960795 + 2282987 * 2 ^ 59
def prefixEnd_2282987 : Nat := 4983230072969 + 3 ^ 40 * 2282987 * 2
def baseEnd_2282987 : Nat := 260504368659147674791831

theorem tailTrace_2282987 : CollatzResearch.WordTrace tailWord_2282987 prefixEnd_2282987 260504368659147674791831 := by
  unfold tailWord_2282987
  simp only [CollatzResearch.WordTrace]
  refine ⟨83267376580135476982935215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55511584386756984655290143 83267376580135476982935215)
  ·
    refine ⟨124901064870203215474402823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83267376580135476982935215 124901064870203215474402823)
    ·
      refine ⟨187351597305304823211604235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124901064870203215474402823 187351597305304823211604235)
      ·
        refine ⟨281027395957957234817406353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187351597305304823211604235 281027395957957234817406353)
        ·
          refine ⟨210770546968467926113054765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281027395957957234817406353 210770546968467926113054765)
          ·
            refine ⟨79038955113175472292395537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 210770546968467926113054765 79038955113175472292395537)
            ·
              refine ⟨59279216334881604219296653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79038955113175472292395537 59279216334881604219296653)
              ·
                refine ⟨22229706125580601582236245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59279216334881604219296653 22229706125580601582236245)
                ·
                  refine ⟨260504368659147674791831, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22229706125580601582236245 260504368659147674791831)
                  ·
                    rfl

theorem cell22_2282987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 3, 8].length) (baseStart_2282987 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282987 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282987 prefixEnd_2282987 := by exact prefixLift 2282987
  have htrace : WordTrace (prefixWord ++ tailWord_2282987) baseStart_2282987 baseEnd_2282987 := by
    simpa [prefixWord, tailWord_2282987, baseEnd_2282987] using wordTrace_append hprefix tailTrace_2282987
  have hstable : (prefixWord ++ tailWord_2282987).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282987).length < 2 ^ (prefixWord ++ tailWord_2282987).sum := by decide
  have hdescent : baseEnd_2282987 < baseStart_2282987 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2282997 : List Nat := [1, 3, 5, 1, 1, 3, 1, 3, 1, 3]
def baseStart_2282997 : Nat := 118140960795 + 2282997 * 2 ^ 59
def prefixEnd_2282997 : Nat := 4983230072969 + 3 ^ 40 * 2282997 * 2
def baseEnd_2282997 : Nat := 781516529181806331625463

theorem tailTrace_2282997 : CollatzResearch.WordTrace tailWord_2282997 prefixEnd_2282997 781516529181806331625463 := by
  unfold tailWord_2282997
  simp only [CollatzResearch.WordTrace]
  refine ⟨83267741310099248690799245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55511827540066165793866163 83267741310099248690799245)
  ·
    refine ⟨31225402991287218259049717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83267741310099248690799245 31225402991287218259049717)
    ·
      refine ⟨2927381530433176711785911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 31225402991287218259049717 2927381530433176711785911)
      ·
        refine ⟨4391072295649765067678867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2927381530433176711785911 4391072295649765067678867)
        ·
          refine ⟨6586608443474647601518301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4391072295649765067678867 6586608443474647601518301)
          ·
            refine ⟨2469978166302992850569363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6586608443474647601518301 2469978166302992850569363)
            ·
              refine ⟨3704967249454489275854045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2469978166302992850569363 3704967249454489275854045)
              ·
                refine ⟨1389362718545433478445267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3704967249454489275854045 1389362718545433478445267)
                ·
                  refine ⟨2084044077818150217667901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1389362718545433478445267 2084044077818150217667901)
                  ·
                    refine ⟨781516529181806331625463, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2084044077818150217667901 781516529181806331625463)
                    ·
                      rfl

theorem cell22_2282997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_2282997 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2282997 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2282997 prefixEnd_2282997 := by exact prefixLift 2282997
  have htrace : WordTrace (prefixWord ++ tailWord_2282997) baseStart_2282997 baseEnd_2282997 := by
    simpa [prefixWord, tailWord_2282997, baseEnd_2282997] using wordTrace_append hprefix tailTrace_2282997
  have hstable : (prefixWord ++ tailWord_2282997).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2282997).length < 2 ^ (prefixWord ++ tailWord_2282997).sum := by decide
  have hdescent : baseEnd_2282997 < baseStart_2282997 := by decide
  rcases family_descends (prefixWord ++ tailWord_2282997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283014 : List Nat := [6, 2, 1, 1, 2, 2, 1, 1, 3, 3]
def baseStart_2283014 : Nat := 118140960795 + 2283014 * 2 ^ 59
def prefixEnd_2283014 : Nat := 4983230072969 + 3 ^ 40 * 2283014 * 2
def baseEnd_2283014 : Nat := 781522348629223953950411

theorem tailTrace_2283014 : CollatzResearch.WordTrace tailWord_2283014 prefixEnd_2283014 781522348629223953950411 := by
  unfold tailWord_2283014
  simp only [CollatzResearch.WordTrace]
  refine ⟨2602136292219926893567753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55512240900691773729445397 2602136292219926893567753)
  ·
    refine ⟨1951602219164945170175815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2602136292219926893567753 1951602219164945170175815)
    ·
      refine ⟨2927403328747417755263723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1951602219164945170175815 2927403328747417755263723)
      ·
        refine ⟨4391104993121126632895585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2927403328747417755263723 4391104993121126632895585)
        ·
          refine ⟨3293328744840844974671689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4391104993121126632895585 3293328744840844974671689)
          ·
            refine ⟨2469996558630633731003767, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3293328744840844974671689 2469996558630633731003767)
            ·
              refine ⟨3704994837945950596505651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2469996558630633731003767 3704994837945950596505651)
              ·
                refine ⟨5557492256918925894758477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3704994837945950596505651 5557492256918925894758477)
                ·
                  refine ⟨2084059596344597210534429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5557492256918925894758477 2084059596344597210534429)
                  ·
                    refine ⟨781522348629223953950411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2084059596344597210534429 781522348629223953950411)
                    ·
                      rfl

theorem cell22_2283014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 2, 2, 1, 1, 3, 3].length) (baseStart_2283014 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283014 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283014 prefixEnd_2283014 := by exact prefixLift 2283014
  have htrace : WordTrace (prefixWord ++ tailWord_2283014) baseStart_2283014 baseEnd_2283014 := by
    simpa [prefixWord, tailWord_2283014, baseEnd_2283014] using wordTrace_append hprefix tailTrace_2283014
  have hstable : (prefixWord ++ tailWord_2283014).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283014).length < 2 ^ (prefixWord ++ tailWord_2283014).sum := by decide
  have hdescent : baseEnd_2283014 < baseStart_2283014 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283034 : List Nat := [3, 1, 1, 3, 1, 1, 1, 1, 6, 4]
def baseStart_2283034 : Nat := 118140960795 + 2283034 * 2 ^ 59
def prefixEnd_2283034 : Nat := 4983230072969 + 3 ^ 40 * 2283034 * 2
def baseEnd_2283034 : Nat := 781529195037950568450349

theorem tailTrace_2283034 : CollatzResearch.WordTrace tailWord_2283034 prefixEnd_2283034 781529195037950568450349 := by
  unfold tailWord_2283034
  simp only [CollatzResearch.WordTrace]
  refine ⟨20817272702741301002474039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55512727207310136006597437 20817272702741301002474039)
  ·
    refine ⟨31225909054111951503711059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20817272702741301002474039 31225909054111951503711059)
    ·
      refine ⟨46838863581167927255566589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31225909054111951503711059 46838863581167927255566589)
      ·
        refine ⟨17564573842937972720837471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46838863581167927255566589 17564573842937972720837471)
        ·
          refine ⟨26346860764406959081256207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17564573842937972720837471 26346860764406959081256207)
          ·
            refine ⟨39520291146610438621884311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26346860764406959081256207 39520291146610438621884311)
            ·
              refine ⟨59280436719915657932826467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39520291146610438621884311 59280436719915657932826467)
              ·
                refine ⟨88920655079873486899239701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59280436719915657932826467 88920655079873486899239701)
                ·
                  refine ⟨4168155706869069698401861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 88920655079873486899239701 4168155706869069698401861)
                  ·
                    refine ⟨781529195037950568450349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4168155706869069698401861 781529195037950568450349)
                    ·
                      rfl

theorem cell22_2283034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 1, 6, 4].length) (baseStart_2283034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283034 prefixEnd_2283034 := by exact prefixLift 2283034
  have htrace : WordTrace (prefixWord ++ tailWord_2283034) baseStart_2283034 baseEnd_2283034 := by
    simpa [prefixWord, tailWord_2283034, baseEnd_2283034] using wordTrace_append hprefix tailTrace_2283034
  have hstable : (prefixWord ++ tailWord_2283034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283034).length < 2 ^ (prefixWord ++ tailWord_2283034).sum := by decide
  have hdescent : baseEnd_2283034 < baseStart_2283034 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283171 : List Nat := [1, 1, 1, 4, 1, 1, 3, 1, 6, 3]
def baseStart_2283171 : Nat := 118140960795 + 2283171 * 2 ^ 59
def prefixEnd_2283171 : Nat := 4983230072969 + 3 ^ 40 * 2283171 * 2
def baseEnd_2283171 : Nat := 781576092937727877774929

theorem tailTrace_2283171 : CollatzResearch.WordTrace tailWord_2283171 prefixEnd_2283171 781576092937727877774929 := by
  unfold tailWord_2283171
  simp only [CollatzResearch.WordTrace]
  refine ⟨83274087611468876407633367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55516058407645917605088911 83274087611468876407633367)
  ·
    refine ⟨124911131417203314611450051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83274087611468876407633367 124911131417203314611450051)
    ·
      refine ⟨187366697125804971917175077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124911131417203314611450051 187366697125804971917175077)
      ·
        refine ⟨35131255711088432234470327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 187366697125804971917175077 35131255711088432234470327)
        ·
          refine ⟨52696883566632648351705491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35131255711088432234470327 52696883566632648351705491)
          ·
            refine ⟨79045325349948972527558237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52696883566632648351705491 79045325349948972527558237)
            ·
              refine ⟨29641997006230864697834339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79045325349948972527558237 29641997006230864697834339)
              ·
                refine ⟨44462995509346297046751509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29641997006230864697834339 44462995509346297046751509)
                ·
                  refine ⟨2084202914500607674066477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 44462995509346297046751509 2084202914500607674066477)
                  ·
                    refine ⟨781576092937727877774929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2084202914500607674066477 781576092937727877774929)
                    ·
                      rfl

theorem cell22_2283171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 3, 1, 6, 3].length) (baseStart_2283171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283171 prefixEnd_2283171 := by exact prefixLift 2283171
  have htrace : WordTrace (prefixWord ++ tailWord_2283171) baseStart_2283171 baseEnd_2283171 := by
    simpa [prefixWord, tailWord_2283171, baseEnd_2283171] using wordTrace_append hprefix tailTrace_2283171
  have hstable : (prefixWord ++ tailWord_2283171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283171).length < 2 ^ (prefixWord ++ tailWord_2283171).sum := by decide
  have hdescent : baseEnd_2283171 < baseStart_2283171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283173 : List Nat := [1, 3, 1, 2, 1, 2, 5, 3, 4]
def baseStart_2283173 : Nat := 118140960795 + 2283173 * 2 ^ 59
def prefixEnd_2283173 : Nat := 4983230072969 + 3 ^ 40 * 2283173 * 2
def baseEnd_2283173 : Nat := 260525592526200179741641

theorem tailTrace_2283173 : CollatzResearch.WordTrace tailWord_2283173 prefixEnd_2283173 260525592526200179741641 := by
  unfold tailWord_2283173
  simp only [CollatzResearch.WordTrace]
  refine ⟨83274160557461630749206173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55516107038307753832804115 83274160557461630749206173)
  ·
    refine ⟨31227810209048111530952315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83274160557461630749206173 31227810209048111530952315)
    ·
      refine ⟨46841715313572167296428473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31227810209048111530952315 46841715313572167296428473)
      ·
        refine ⟨35131286485179125472321355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46841715313572167296428473 35131286485179125472321355)
        ·
          refine ⟨52696929727768688208482033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35131286485179125472321355 52696929727768688208482033)
          ·
            refine ⟨39522697295826516156361525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52696929727768688208482033 39522697295826516156361525)
            ·
              refine ⟨3705252871483735889658893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39522697295826516156361525 3705252871483735889658893)
              ·
                refine ⟨1389469826806400958622085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3705252871483735889658893 1389469826806400958622085)
                ·
                  refine ⟨260525592526200179741641, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1389469826806400958622085 260525592526200179741641)
                  ·
                    rfl

theorem cell22_2283173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 5, 3, 4].length) (baseStart_2283173 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283173 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283173 prefixEnd_2283173 := by exact prefixLift 2283173
  have htrace : WordTrace (prefixWord ++ tailWord_2283173) baseStart_2283173 baseEnd_2283173 := by
    simpa [prefixWord, tailWord_2283173, baseEnd_2283173] using wordTrace_append hprefix tailTrace_2283173
  have hstable : (prefixWord ++ tailWord_2283173).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283173).length < 2 ^ (prefixWord ++ tailWord_2283173).sum := by decide
  have hdescent : baseEnd_2283173 < baseStart_2283173 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283184 : List Nat := [2, 1, 1, 1, 2, 1, 14]
def baseStart_2283184 : Nat := 118140960795 + 2283184 * 2 ^ 59
def prefixEnd_2283184 : Nat := 4983230072969 + 3 ^ 40 * 2283184 * 2
def baseEnd_2283184 : Nat := 28947427522348154711107

theorem tailTrace_2283184 : CollatzResearch.WordTrace tailWord_2283184 prefixEnd_2283184 28947427522348154711107 := by
  unfold tailWord_2283184
  simp only [CollatzResearch.WordTrace]
  refine ⟨41637280880210889813928303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55516374506947853085237737 41637280880210889813928303)
  ·
    refine ⟨62455921320316334720892455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41637280880210889813928303 62455921320316334720892455)
    ·
      refine ⟨93683881980474502081338683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62455921320316334720892455 93683881980474502081338683)
      ·
        refine ⟨140525822970711753122008025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93683881980474502081338683 140525822970711753122008025)
        ·
          refine ⟨105394367228033814841506019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140525822970711753122008025 105394367228033814841506019)
          ·
            refine ⟨158091550842050722262259029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105394367228033814841506019 158091550842050722262259029)
            ·
              refine ⟨28947427522348154711107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 14 158091550842050722262259029 28947427522348154711107)
              ·
                rfl

theorem cell22_2283184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 14].length) (baseStart_2283184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283184 prefixEnd_2283184 := by exact prefixLift 2283184
  have htrace : WordTrace (prefixWord ++ tailWord_2283184) baseStart_2283184 baseEnd_2283184 := by
    simpa [prefixWord, tailWord_2283184, baseEnd_2283184] using wordTrace_append hprefix tailTrace_2283184
  have hstable : (prefixWord ++ tailWord_2283184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283184).length < 2 ^ (prefixWord ++ tailWord_2283184).sum := by decide
  have hdescent : baseEnd_2283184 < baseStart_2283184 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283186 : List Nat := [3, 2, 1, 1, 1, 2, 3, 1, 4, 4]
def baseStart_2283186 : Nat := 118140960795 + 2283186 * 2 ^ 59
def prefixEnd_2283186 : Nat := 4983230072969 + 3 ^ 40 * 2283186 * 2
def baseEnd_2283186 : Nat := 781581227744272838649883

theorem tailTrace_2283186 : CollatzResearch.WordTrace tailWord_2283186 prefixEnd_2283186 781581227744272838649883 := by
  unfold tailWord_2283186
  simp only [CollatzResearch.WordTrace]
  refine ⟨20818658676603633492357353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55516423137609689312952941 20818658676603633492357353)
  ·
    refine ⟨15613994007452725119268015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20818658676603633492357353 15613994007452725119268015)
    ·
      refine ⟨23420991011179087678902023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15613994007452725119268015 23420991011179087678902023)
      ·
        refine ⟨35131486516768631518353035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23420991011179087678902023 35131486516768631518353035)
        ·
          refine ⟨52697229775152947277529553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35131486516768631518353035 52697229775152947277529553)
          ·
            refine ⟨39522922331364710458147165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52697229775152947277529553 39522922331364710458147165)
            ·
              refine ⟨14821095874261766421805187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39522922331364710458147165 14821095874261766421805187)
              ·
                refine ⟨22231643811392649632707781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14821095874261766421805187 22231643811392649632707781)
                ·
                  refine ⟨4168433214636121806132709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22231643811392649632707781 4168433214636121806132709)
                  ·
                    refine ⟨781581227744272838649883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4168433214636121806132709 781581227744272838649883)
                    ·
                      rfl

theorem cell22_2283186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 3, 1, 4, 4].length) (baseStart_2283186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283186 prefixEnd_2283186 := by exact prefixLift 2283186
  have htrace : WordTrace (prefixWord ++ tailWord_2283186) baseStart_2283186 baseEnd_2283186 := by
    simpa [prefixWord, tailWord_2283186, baseEnd_2283186] using wordTrace_append hprefix tailTrace_2283186
  have hstable : (prefixWord ++ tailWord_2283186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283186).length < 2 ^ (prefixWord ++ tailWord_2283186).sum := by decide
  have hdescent : baseEnd_2283186 < baseStart_2283186 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283190 : List Nat := [5, 1, 3, 1, 1, 1, 3, 1, 6]
def baseStart_2283190 : Nat := 118140960795 + 2283190 * 2 ^ 59
def prefixEnd_2283190 : Nat := 4983230072969 + 3 ^ 40 * 2283190 * 2
def baseEnd_2283190 : Nat := 260527532342006053849957

theorem tailTrace_2283190 : CollatzResearch.WordTrace tailWord_2283190 prefixEnd_2283190 260527532342006053849957 := by
  unfold tailWord_2283190
  simp only [CollatzResearch.WordTrace]
  refine ⟨5204673787400002665785939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55516520398933361768383349 5204673787400002665785939)
  ·
    refine ⟨7807010681100003998678909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5204673787400002665785939 7807010681100003998678909)
    ·
      refine ⟨2927629005412501499504591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7807010681100003998678909 2927629005412501499504591)
      ·
        refine ⟨4391443508118752249256887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2927629005412501499504591 4391443508118752249256887)
        ·
          refine ⟨6587165262178128373885331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4391443508118752249256887 6587165262178128373885331)
          ·
            refine ⟨9880747893267192560827997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6587165262178128373885331 9880747893267192560827997)
            ·
              refine ⟨3705280459975197210310499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9880747893267192560827997 3705280459975197210310499)
              ·
                refine ⟨5557920689962795815465749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3705280459975197210310499 5557920689962795815465749)
                ·
                  refine ⟨260527532342006053849957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5557920689962795815465749 260527532342006053849957)
                  ·
                    rfl

theorem cell22_2283190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 1, 6].length) (baseStart_2283190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283190 prefixEnd_2283190 := by exact prefixLift 2283190
  have htrace : WordTrace (prefixWord ++ tailWord_2283190) baseStart_2283190 baseEnd_2283190 := by
    simpa [prefixWord, tailWord_2283190, baseEnd_2283190] using wordTrace_append hprefix tailTrace_2283190
  have hstable : (prefixWord ++ tailWord_2283190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283190).length < 2 ^ (prefixWord ++ tailWord_2283190).sum := by decide
  have hdescent : baseEnd_2283190 < baseStart_2283190 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283220 : List Nat := [2, 4, 1, 3, 1, 2, 2, 1, 2, 4]
def baseStart_2283220 : Nat := 118140960795 + 2283220 * 2 ^ 59
def prefixEnd_2283220 : Nat := 4983230072969 + 3 ^ 40 * 2283220 * 2
def baseEnd_2283220 : Nat := 781592866639108083299779

theorem tailTrace_2283220 : CollatzResearch.WordTrace tailWord_2283220 prefixEnd_2283220 781592866639108083299779 := by
  unfold tailWord_2283220
  simp only [CollatzResearch.WordTrace]
  refine ⟨41637937394145678888083557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55517249858860905184111409 41637937394145678888083557)
  ·
    refine ⟨7807113261402314791515667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41637937394145678888083557 7807113261402314791515667)
    ·
      refine ⟨11710669892103472187273501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7807113261402314791515667 11710669892103472187273501)
      ·
        refine ⟨4391501209538802070227563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11710669892103472187273501 4391501209538802070227563)
        ·
          refine ⟨6587251814308203105341345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4391501209538802070227563 6587251814308203105341345)
          ·
            refine ⟨4940438860731152329006009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6587251814308203105341345 4940438860731152329006009)
            ·
              refine ⟨3705329145548364246754507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4940438860731152329006009 3705329145548364246754507)
              ·
                refine ⟨5557993718322546370131761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3705329145548364246754507 5557993718322546370131761)
                ·
                  refine ⟨4168495288741909777598821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5557993718322546370131761 4168495288741909777598821)
                  ·
                    refine ⟨781592866639108083299779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4168495288741909777598821 781592866639108083299779)
                    ·
                      rfl

theorem cell22_2283220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 1, 2, 4].length) (baseStart_2283220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283220 prefixEnd_2283220 := by exact prefixLift 2283220
  have htrace : WordTrace (prefixWord ++ tailWord_2283220) baseStart_2283220 baseEnd_2283220 := by
    simpa [prefixWord, tailWord_2283220, baseEnd_2283220] using wordTrace_append hprefix tailTrace_2283220
  have hstable : (prefixWord ++ tailWord_2283220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283220).length < 2 ^ (prefixWord ++ tailWord_2283220).sum := by decide
  have hdescent : baseEnd_2283220 < baseStart_2283220 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283222 : List Nat := [5, 2, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_2283222 : Nat := 118140960795 + 2283222 * 2 ^ 59
def prefixEnd_2283222 : Nat := 4983230072969 + 3 ^ 40 * 2283222 * 2
def baseEnd_2283222 : Nat := 781593551279980744749773

theorem tailTrace_2283222 : CollatzResearch.WordTrace tailWord_2283222 prefixEnd_2283222 781593551279980744749773 := by
  unfold tailWord_2283222
  simp only [CollatzResearch.WordTrace]
  refine ⟨5204746733392757007358745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55517298489522741411826613 5204746733392757007358745)
  ·
    refine ⟨3903560050044567755519059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5204746733392757007358745 3903560050044567755519059)
    ·
      refine ⟨5855340075066851633278589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3903560050044567755519059 5855340075066851633278589)
      ·
        refine ⟨2195752528150069362479471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5855340075066851633278589 2195752528150069362479471)
        ·
          refine ⟨3293628792225104043719207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2195752528150069362479471 3293628792225104043719207)
          ·
            refine ⟨4940443188337656065578811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3293628792225104043719207 4940443188337656065578811)
            ·
              refine ⟨7410664782506484098368217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4940443188337656065578811 7410664782506484098368217)
              ·
                refine ⟨5557998586879863073776163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7410664782506484098368217 5557998586879863073776163)
                ·
                  refine ⟨8336997880319794610664245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5557998586879863073776163 8336997880319794610664245)
                  ·
                    refine ⟨781593551279980744749773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8336997880319794610664245 781593551279980744749773)
                    ·
                      rfl

theorem cell22_2283222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_2283222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283222 prefixEnd_2283222 := by exact prefixLift 2283222
  have htrace : WordTrace (prefixWord ++ tailWord_2283222) baseStart_2283222 baseEnd_2283222 := by
    simpa [prefixWord, tailWord_2283222, baseEnd_2283222] using wordTrace_append hprefix tailTrace_2283222
  have hstable : (prefixWord ++ tailWord_2283222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283222).length < 2 ^ (prefixWord ++ tailWord_2283222).sum := by decide
  have hdescent : baseEnd_2283222 < baseStart_2283222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283252 : List Nat := [2, 6, 1, 1, 1, 3, 1, 7]
def baseStart_2283252 : Nat := 118140960795 + 2283252 * 2 ^ 59
def prefixEnd_2283252 : Nat := 4983230072969 + 3 ^ 40 * 2283252 * 2
def baseEnd_2283252 : Nat := 86844868988118962944409

theorem tailTrace_2283252 : CollatzResearch.WordTrace tailWord_2283252 prefixEnd_2283252 86844868988118962944409 := by
  unfold tailWord_2283252
  simp only [CollatzResearch.WordTrace]
  refine ⟨41638520962087713620666005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55518027949450284827554673 41638520962087713620666005)
  ·
    refine ⟨1951805670097861575968719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 41638520962087713620666005 1951805670097861575968719)
    ·
      refine ⟨2927708505146792363953079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1951805670097861575968719 2927708505146792363953079)
      ·
        refine ⟨4391562757720188545929619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2927708505146792363953079 4391562757720188545929619)
        ·
          refine ⟨6587344136580282818894429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4391562757720188545929619 6587344136580282818894429)
          ·
            refine ⟨2470254051217606057085411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6587344136580282818894429 2470254051217606057085411)
            ·
              refine ⟨3705381076826409085628117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2470254051217606057085411 3705381076826409085628117)
              ·
                refine ⟨86844868988118962944409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3705381076826409085628117 86844868988118962944409)
                ·
                  rfl

theorem cell22_2283252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 3, 1, 7].length) (baseStart_2283252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283252 prefixEnd_2283252 := by exact prefixLift 2283252
  have htrace : WordTrace (prefixWord ++ tailWord_2283252) baseStart_2283252 baseEnd_2283252 := by
    simpa [prefixWord, tailWord_2283252, baseEnd_2283252] using wordTrace_append hprefix tailTrace_2283252
  have hstable : (prefixWord ++ tailWord_2283252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283252).length < 2 ^ (prefixWord ++ tailWord_2283252).sum := by decide
  have hdescent : baseEnd_2283252 < baseStart_2283252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283308 : List Nat := [2, 2, 1, 1, 1, 6, 2, 1, 6]
def baseStart_2283308 : Nat := 118140960795 + 2283308 * 2 ^ 59
def prefixEnd_2283308 : Nat := 4983230072969 + 3 ^ 40 * 2283308 * 2
def baseEnd_2283308 : Nat := 260540996945835062366503

theorem tailTrace_2283308 : CollatzResearch.WordTrace tailWord_2283308 prefixEnd_2283308 260540996945835062366503 := by
  unfold tailWord_2283308
  simp only [CollatzResearch.WordTrace]
  refine ⟨41639542205986274402685289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55519389607981699203580385 41639542205986274402685289)
  ·
    refine ⟨31229656654489705802013967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41639542205986274402685289 31229656654489705802013967)
    ·
      refine ⟨46844484981734558703020951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31229656654489705802013967 46844484981734558703020951)
      ·
        refine ⟨70266727472601838054531427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46844484981734558703020951 70266727472601838054531427)
        ·
          refine ⟨105400091208902757081797141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70266727472601838054531427 105400091208902757081797141)
          ·
            refine ⟨4940629275417316738209241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 105400091208902757081797141 4940629275417316738209241)
            ·
              refine ⟨3705471956562987553656931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4940629275417316738209241 3705471956562987553656931)
              ·
                refine ⟨5558207934844481330485397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3705471956562987553656931 5558207934844481330485397)
                ·
                  refine ⟨260540996945835062366503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5558207934844481330485397 260540996945835062366503)
                  ·
                    rfl

theorem cell22_2283308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 6].length) (baseStart_2283308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283308 prefixEnd_2283308 := by exact prefixLift 2283308
  have htrace : WordTrace (prefixWord ++ tailWord_2283308) baseStart_2283308 baseEnd_2283308 := by
    simpa [prefixWord, tailWord_2283308, baseEnd_2283308] using wordTrace_append hprefix tailTrace_2283308
  have hstable : (prefixWord ++ tailWord_2283308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283308).length < 2 ^ (prefixWord ++ tailWord_2283308).sum := by decide
  have hdescent : baseEnd_2283308 < baseStart_2283308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283338 : List Nat := [3, 1, 2, 1, 1, 1, 4, 3, 2, 4]
def baseStart_2283338 : Nat := 118140960795 + 2283338 * 2 ^ 59
def prefixEnd_2283338 : Nat := 4983230072969 + 3 ^ 40 * 2283338 * 2
def baseEnd_2283338 : Nat := 781633260450595108849417

theorem tailTrace_2283338 : CollatzResearch.WordTrace tailWord_2283338 prefixEnd_2283338 781633260450595108849417 := by
  unfold tailWord_2283338
  simp only [CollatzResearch.WordTrace]
  refine ⟨20820044650465965982240667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55520119067909242619308445 20820044650465965982240667)
  ·
    refine ⟨31230066975698948973361001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20820044650465965982240667 31230066975698948973361001)
    ·
      refine ⟨23422550231774211730020751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31230066975698948973361001 23422550231774211730020751)
      ·
        refine ⟨35133825347661317595031127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23422550231774211730020751 35133825347661317595031127)
        ·
          refine ⟨52700738021491976392546691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35133825347661317595031127 52700738021491976392546691)
          ·
            refine ⟨79051107032237964588820037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52700738021491976392546691 79051107032237964588820037)
            ·
              refine ⟨14822082568544618360403757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79051107032237964588820037 14822082568544618360403757)
              ·
                refine ⟨5558280963204231885151409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14822082568544618360403757 5558280963204231885151409)
                ·
                  refine ⟨4168710722403173913863557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5558280963204231885151409 4168710722403173913863557)
                  ·
                    refine ⟨781633260450595108849417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4168710722403173913863557 781633260450595108849417)
                    ·
                      rfl

theorem cell22_2283338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 4, 3, 2, 4].length) (baseStart_2283338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283338 prefixEnd_2283338 := by exact prefixLift 2283338
  have htrace : WordTrace (prefixWord ++ tailWord_2283338) baseStart_2283338 baseEnd_2283338 := by
    simpa [prefixWord, tailWord_2283338, baseEnd_2283338] using wordTrace_append hprefix tailTrace_2283338
  have hstable : (prefixWord ++ tailWord_2283338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283338).length < 2 ^ (prefixWord ++ tailWord_2283338).sum := by decide
  have hdescent : baseEnd_2283338 < baseStart_2283338 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283374 : List Nat := [4, 1, 2, 3, 1, 1, 4, 1, 2, 3]
def baseStart_2283374 : Nat := 118140960795 + 2283374 * 2 ^ 59
def prefixEnd_2283374 : Nat := 4983230072969 + 3 ^ 40 * 2283374 * 2
def baseEnd_2283374 : Nat := 781645583986303014949307

theorem tailTrace_2283374 : CollatzResearch.WordTrace tailWord_2283374 prefixEnd_2283374 781645583986303014949307 := by
  unfold tailWord_2283374
  simp only [CollatzResearch.WordTrace]
  refine ⟨10410186453716680259659147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55520994419822294718182117 10410186453716680259659147)
  ·
    refine ⟨15615279680575020389488721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10410186453716680259659147 15615279680575020389488721)
    ·
      refine ⟨11711459760431265292116541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15615279680575020389488721 11711459760431265292116541)
      ·
        refine ⟨4391797410161724484543703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11711459760431265292116541 4391797410161724484543703)
        ·
          refine ⟨6587696115242586726815555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4391797410161724484543703 6587696115242586726815555)
          ·
            refine ⟨9881544172863880090223333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6587696115242586726815555 9881544172863880090223333)
            ·
              refine ⟨1852789532411977516916875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9881544172863880090223333 1852789532411977516916875)
              ·
                refine ⟨2779184298617966275375313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1852789532411977516916875 2779184298617966275375313)
                ·
                  refine ⟨2084388223963474706531485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2779184298617966275375313 2084388223963474706531485)
                  ·
                    refine ⟨781645583986303014949307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2084388223963474706531485 781645583986303014949307)
                    ·
                      rfl

theorem cell22_2283374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 4, 1, 2, 3].length) (baseStart_2283374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283374 prefixEnd_2283374 := by exact prefixLift 2283374
  have htrace : WordTrace (prefixWord ++ tailWord_2283374) baseStart_2283374 baseEnd_2283374 := by
    simpa [prefixWord, tailWord_2283374, baseEnd_2283374] using wordTrace_append hprefix tailTrace_2283374
  have hstable : (prefixWord ++ tailWord_2283374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283374).length < 2 ^ (prefixWord ++ tailWord_2283374).sum := by decide
  have hdescent : baseEnd_2283374 < baseStart_2283374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283413 : List Nat := [1, 3, 2, 1, 1, 3, 2, 2, 2, 5]
def baseStart_2283413 : Nat := 118140960795 + 2283413 * 2 ^ 59
def prefixEnd_2283413 : Nat := 4983230072969 + 3 ^ 40 * 2283413 * 2
def baseEnd_2283413 : Nat := 781658934483319913224187

theorem tailTrace_2283413 : CollatzResearch.WordTrace tailWord_2283413 prefixEnd_2283413 781658934483319913224187 := by
  unfold tailWord_2283413
  simp only [CollatzResearch.WordTrace]
  refine ⟨83282914076592151737942893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55521942717728101158628595 83282914076592151737942893)
  ·
    refine ⟨31231092778722056901728585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83282914076592151737942893 31231092778722056901728585)
    ·
      refine ⟨23423319584041542676296439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31231092778722056901728585 23423319584041542676296439)
      ·
        refine ⟨35134979376062314014444659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23423319584041542676296439 35134979376062314014444659)
        ·
          refine ⟨52702469064093471021666989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35134979376062314014444659 52702469064093471021666989)
          ·
            refine ⟨19763425899035051633125121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52702469064093471021666989 19763425899035051633125121)
            ·
              refine ⟨14822569424276288724843841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19763425899035051633125121 14822569424276288724843841)
              ·
                refine ⟨11116927068207216543632881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14822569424276288724843841 11116927068207216543632881)
                ·
                  refine ⟨8337695301155412407724661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11116927068207216543632881 8337695301155412407724661)
                  ·
                    refine ⟨781658934483319913224187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8337695301155412407724661 781658934483319913224187)
                    ·
                      rfl

theorem cell22_2283413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 2, 2, 5].length) (baseStart_2283413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283413 prefixEnd_2283413 := by exact prefixLift 2283413
  have htrace : WordTrace (prefixWord ++ tailWord_2283413) baseStart_2283413 baseEnd_2283413 := by
    simpa [prefixWord, tailWord_2283413, baseEnd_2283413] using wordTrace_append hprefix tailTrace_2283413
  have hstable : (prefixWord ++ tailWord_2283413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283413).length < 2 ^ (prefixWord ++ tailWord_2283413).sum := by decide
  have hdescent : baseEnd_2283413 < baseStart_2283413 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283415 : List Nat := [1, 1, 3, 3, 1, 4, 2, 2, 5]
def baseStart_2283415 : Nat := 118140960795 + 2283415 * 2 ^ 59
def prefixEnd_2283415 : Nat := 4983230072969 + 3 ^ 40 * 2283415 * 2
def baseEnd_2283415 : Nat := 260553206374730858224727

theorem tailTrace_2283415 : CollatzResearch.WordTrace tailWord_2283415 prefixEnd_2283415 260553206374730858224727 := by
  unfold tailWord_2283415
  simp only [CollatzResearch.WordTrace]
  refine ⟨83282987022584906079515699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55521991348389937386343799 83282987022584906079515699)
  ·
    refine ⟨124924480533877359119273549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83282987022584906079515699 124924480533877359119273549)
    ·
      refine ⟨46846680200204009669727581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124924480533877359119273549 46846680200204009669727581)
      ·
        refine ⟨17567505075076503626147843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46846680200204009669727581 17567505075076503626147843)
        ·
          refine ⟨26351257612614755439221765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17567505075076503626147843 26351257612614755439221765)
          ·
            refine ⟨4940860802365266644854081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26351257612614755439221765 4940860802365266644854081)
            ·
              refine ⟨3705645601773949983640561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4940860802365266644854081 3705645601773949983640561)
              ·
                refine ⟨2779234201330462487730421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3705645601773949983640561 2779234201330462487730421)
                ·
                  refine ⟨260553206374730858224727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2779234201330462487730421 260553206374730858224727)
                  ·
                    rfl

theorem cell22_2283415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 4, 2, 2, 5].length) (baseStart_2283415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283415 prefixEnd_2283415 := by exact prefixLift 2283415
  have htrace : WordTrace (prefixWord ++ tailWord_2283415) baseStart_2283415 baseEnd_2283415 := by
    simpa [prefixWord, tailWord_2283415, baseEnd_2283415] using wordTrace_append hprefix tailTrace_2283415
  have hstable : (prefixWord ++ tailWord_2283415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283415).length < 2 ^ (prefixWord ++ tailWord_2283415).sum := by decide
  have hdescent : baseEnd_2283415 < baseStart_2283415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283443 : List Nat := [1, 1, 1, 2, 3, 1, 5, 2, 6]
def baseStart_2283443 : Nat := 118140960795 + 2283443 * 2 ^ 59
def prefixEnd_2283443 : Nat := 4983230072969 + 3 ^ 40 * 2283443 * 2
def baseEnd_2283443 : Nat := 260556401365469944991365

theorem tailTrace_2283443 : CollatzResearch.WordTrace tailWord_2283443 prefixEnd_2283443 260556401365469944991365 := by
  unfold tailWord_2283443
  simp only [CollatzResearch.WordTrace]
  refine ⟨83284008266483466861534983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55522672177655644574356655 83284008266483466861534983)
  ·
    refine ⟨124926012399725200292302475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83284008266483466861534983 124926012399725200292302475)
    ·
      refine ⟨187389018599587800438453713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124926012399725200292302475 187389018599587800438453713)
      ·
        refine ⟨140541763949690850328840285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187389018599587800438453713 140541763949690850328840285)
        ·
          refine ⟨52703161481134068873315107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140541763949690850328840285 52703161481134068873315107)
          ·
            refine ⟨79054742221701103309972661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52703161481134068873315107 79054742221701103309972661)
            ·
              refine ⟨7411382083284478435309937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79054742221701103309972661 7411382083284478435309937)
              ·
                refine ⟨5558536562463358826482453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7411382083284478435309937 5558536562463358826482453)
                ·
                  refine ⟨260556401365469944991365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5558536562463358826482453 260556401365469944991365)
                  ·
                    rfl

theorem cell22_2283443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 2, 6].length) (baseStart_2283443 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283443 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283443 prefixEnd_2283443 := by exact prefixLift 2283443
  have htrace : WordTrace (prefixWord ++ tailWord_2283443) baseStart_2283443 baseEnd_2283443 := by
    simpa [prefixWord, tailWord_2283443, baseEnd_2283443] using wordTrace_append hprefix tailTrace_2283443
  have hstable : (prefixWord ++ tailWord_2283443).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283443).length < 2 ^ (prefixWord ++ tailWord_2283443).sum := by decide
  have hdescent : baseEnd_2283443 < baseStart_2283443 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283445 : List Nat := [1, 3, 3, 2, 1, 2, 2, 1, 3, 4]
def baseStart_2283445 : Nat := 118140960795 + 2283445 * 2 ^ 59
def prefixEnd_2283445 : Nat := 4983230072969 + 3 ^ 40 * 2283445 * 2
def baseEnd_2283445 : Nat := 781669888737282496424089

theorem tailTrace_2283445 : CollatzResearch.WordTrace tailWord_2283445 prefixEnd_2283445 781669888737282496424089 := by
  unfold tailWord_2283445
  simp only [CollatzResearch.WordTrace]
  refine ⟨83284081212476221203107789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55522720808317480802071859 83284081212476221203107789)
  ·
    refine ⟨31231530454678582951165421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83284081212476221203107789 31231530454678582951165421)
    ·
      refine ⟨11711823920504468606687033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31231530454678582951165421 11711823920504468606687033)
      ·
        refine ⟨8783867940378351455015275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11711823920504468606687033 8783867940378351455015275)
        ·
          refine ⟨13175801910567527182522913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8783867940378351455015275 13175801910567527182522913)
          ·
            refine ⟨9881851432925645386892185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13175801910567527182522913 9881851432925645386892185)
            ·
              refine ⟨7411388574694234040169139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9881851432925645386892185 7411388574694234040169139)
              ·
                refine ⟨11117082862041351060253709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7411388574694234040169139 11117082862041351060253709)
                ·
                  refine ⟨4168906073265506647595141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11117082862041351060253709 4168906073265506647595141)
                  ·
                    refine ⟨781669888737282496424089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4168906073265506647595141 781669888737282496424089)
                    ·
                      rfl

theorem cell22_2283445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 2, 1, 3, 4].length) (baseStart_2283445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283445 prefixEnd_2283445 := by exact prefixLift 2283445
  have htrace : WordTrace (prefixWord ++ tailWord_2283445) baseStart_2283445 baseEnd_2283445 := by
    simpa [prefixWord, tailWord_2283445, baseEnd_2283445] using wordTrace_append hprefix tailTrace_2283445
  have hstable : (prefixWord ++ tailWord_2283445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283445).length < 2 ^ (prefixWord ++ tailWord_2283445).sum := by decide
  have hdescent : baseEnd_2283445 < baseStart_2283445 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283477 : List Nat := [1, 3, 2, 3, 2, 1, 2, 4, 4]
def baseStart_2283477 : Nat := 118140960795 + 2283477 * 2 ^ 59
def prefixEnd_2283477 : Nat := 4983230072969 + 3 ^ 40 * 2283477 * 2
def baseEnd_2283477 : Nat := 260560280997081693207997

theorem tailTrace_2283477 : CollatzResearch.WordTrace tailWord_2283477 prefixEnd_2283477 260560280997081693207997 := by
  unfold tailWord_2283477
  simp only [CollatzResearch.WordTrace]
  refine ⟨83285248348360290668272685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55523498898906860445515123 83285248348360290668272685)
  ·
    refine ⟨31231968130635109000602257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83285248348360290668272685 31231968130635109000602257)
    ·
      refine ⟨23423976097976331750451693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31231968130635109000602257 23423976097976331750451693)
      ·
        refine ⟨8783991036741124406419385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23423976097976331750451693 8783991036741124406419385)
        ·
          refine ⟨6587993277555843304814539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8783991036741124406419385 6587993277555843304814539)
          ·
            refine ⟨9881989916333764957221809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6587993277555843304814539 9881989916333764957221809)
            ·
              refine ⟨7411492437250323717916357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9881989916333764957221809 7411492437250323717916357)
              ·
                refine ⟨1389654831984435697109317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7411492437250323717916357 1389654831984435697109317)
                ·
                  refine ⟨260560280997081693207997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1389654831984435697109317 260560280997081693207997)
                  ·
                    rfl

theorem cell22_2283477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4, 4].length) (baseStart_2283477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283477 prefixEnd_2283477 := by exact prefixLift 2283477
  have htrace : WordTrace (prefixWord ++ tailWord_2283477) baseStart_2283477 baseEnd_2283477 := by
    simpa [prefixWord, tailWord_2283477, baseEnd_2283477] using wordTrace_append hprefix tailTrace_2283477
  have hstable : (prefixWord ++ tailWord_2283477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283477).length < 2 ^ (prefixWord ++ tailWord_2283477).sum := by decide
  have hdescent : baseEnd_2283477 < baseStart_2283477 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283503 : List Nat := [1, 1, 2, 1, 4, 2, 1, 1, 2, 7]
def baseStart_2283503 : Nat := 118140960795 + 2283503 * 2 ^ 59
def prefixEnd_2283503 : Nat := 4983230072969 + 3 ^ 40 * 2283503 * 2
def baseEnd_2283503 : Nat := 781689743322589678473911

theorem tailTrace_2283503 : CollatzResearch.WordTrace tailWord_2283503 prefixEnd_2283503 781689743322589678473911 := by
  unfold tailWord_2283503
  simp only [CollatzResearch.WordTrace]
  refine ⟨83286196646266097108719163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55524131097510731405812775 83286196646266097108719163)
  ·
    refine ⟨124929294969399145663078745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83286196646266097108719163 124929294969399145663078745)
    ·
      refine ⟨93696971227049359247309059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124929294969399145663078745 93696971227049359247309059)
      ·
        refine ⟨140545456840574038870963589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93696971227049359247309059 140545456840574038870963589)
        ·
          refine ⟨26352273157607632288305673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140545456840574038870963589 26352273157607632288305673)
          ·
            refine ⟨19764204868205724216229255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26352273157607632288305673 19764204868205724216229255)
            ·
              refine ⟨29646307302308586324343883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19764204868205724216229255 29646307302308586324343883)
              ·
                refine ⟨44469460953462879486515825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29646307302308586324343883 44469460953462879486515825)
                ·
                  refine ⟨33352095715097159614886869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44469460953462879486515825 33352095715097159614886869)
                  ·
                    refine ⟨781689743322589678473911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33352095715097159614886869 781689743322589678473911)
                    ·
                      rfl

theorem cell22_2283503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 1, 1, 2, 7].length) (baseStart_2283503 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283503 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283503 prefixEnd_2283503 := by exact prefixLift 2283503
  have htrace : WordTrace (prefixWord ++ tailWord_2283503) baseStart_2283503 baseEnd_2283503 := by
    simpa [prefixWord, tailWord_2283503, baseEnd_2283503] using wordTrace_append hprefix tailTrace_2283503
  have hstable : (prefixWord ++ tailWord_2283503).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283503).length < 2 ^ (prefixWord ++ tailWord_2283503).sum := by decide
  have hdescent : baseEnd_2283503 < baseStart_2283503 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283505 : List Nat := [1, 2, 2, 2, 5, 1, 1, 8]
def baseStart_2283505 : Nat := 118140960795 + 2283505 * 2 ^ 59
def prefixEnd_2283505 : Nat := 4983230072969 + 3 ^ 40 * 2283505 * 2
def baseEnd_2283505 : Nat := 86854491995940259991545

theorem tailTrace_2283505 : CollatzResearch.WordTrace tailWord_2283505 prefixEnd_2283505 86854491995940259991545 := by
  unfold tailWord_2283505
  simp only [CollatzResearch.WordTrace]
  refine ⟨83286269592258851450291969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55524179728172567633527979 83286269592258851450291969)
  ·
    refine ⟨62464702194194138587718977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83286269592258851450291969 62464702194194138587718977)
    ·
      refine ⟨46848526645645603940789233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62464702194194138587718977 46848526645645603940789233)
      ·
        refine ⟨35136394984234202955591925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46848526645645603940789233 35136394984234202955591925)
        ·
          refine ⟨3294037029771956527086743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35136394984234202955591925 3294037029771956527086743)
          ·
            refine ⟨4941055544657934790630115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3294037029771956527086743 4941055544657934790630115)
            ·
              refine ⟨7411583316986902185945173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4941055544657934790630115 7411583316986902185945173)
              ·
                refine ⟨86854491995940259991545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7411583316986902185945173 86854491995940259991545)
                ·
                  rfl

theorem cell22_2283505_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 5, 1, 1, 8].length) (baseStart_2283505 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283505 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283505 prefixEnd_2283505 := by exact prefixLift 2283505
  have htrace : WordTrace (prefixWord ++ tailWord_2283505) baseStart_2283505 baseEnd_2283505 := by
    simpa [prefixWord, tailWord_2283505, baseEnd_2283505] using wordTrace_append hprefix tailTrace_2283505
  have hstable : (prefixWord ++ tailWord_2283505).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283505).length < 2 ^ (prefixWord ++ tailWord_2283505).sum := by decide
  have hdescent : baseEnd_2283505 < baseStart_2283505 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283505) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283524 : List Nat := [2, 3, 2, 4, 1, 1, 1, 2, 2, 4]
def baseStart_2283524 : Nat := 118140960795 + 2283524 * 2 ^ 59
def prefixEnd_2283524 : Nat := 4983230072969 + 3 ^ 40 * 2283524 * 2
def baseEnd_2283524 : Nat := 781696932051752623698847

theorem tailTrace_2283524 : CollatzResearch.WordTrace tailWord_2283524 prefixEnd_2283524 781696932051752623698847 := by
  unfold tailWord_2283524
  simp only [CollatzResearch.WordTrace]
  refine ⟨41643481289595008847616813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55524641719460011796822417 41643481289595008847616813)
  ·
    refine ⟨15616305483598128317856305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41643481289595008847616813 15616305483598128317856305)
    ·
      refine ⟨11712229112698596238392229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15616305483598128317856305 11712229112698596238392229)
      ·
        refine ⟨2196042958630986794698543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11712229112698596238392229 2196042958630986794698543)
        ·
          refine ⟨3294064437946480192047815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2196042958630986794698543 3294064437946480192047815)
          ·
            refine ⟨4941096656919720288071723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3294064437946480192047815 4941096656919720288071723)
            ·
              refine ⟨7411644985379580432107585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4941096656919720288071723 7411644985379580432107585)
              ·
                refine ⟨5558733739034685324080689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7411644985379580432107585 5558733739034685324080689)
                ·
                  refine ⟨4169050304276013993060517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5558733739034685324080689 4169050304276013993060517)
                  ·
                    refine ⟨781696932051752623698847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4169050304276013993060517 781696932051752623698847)
                    ·
                      rfl

theorem cell22_2283524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 2, 2, 4].length) (baseStart_2283524 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283524 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283524 prefixEnd_2283524 := by exact prefixLift 2283524
  have htrace : WordTrace (prefixWord ++ tailWord_2283524) baseStart_2283524 baseEnd_2283524 := by
    simpa [prefixWord, tailWord_2283524, baseEnd_2283524] using wordTrace_append hprefix tailTrace_2283524
  have hstable : (prefixWord ++ tailWord_2283524).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283524).length < 2 ^ (prefixWord ++ tailWord_2283524).sum := by decide
  have hdescent : baseEnd_2283524 < baseStart_2283524 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283543 : List Nat := [1, 1, 3, 5, 3, 1, 2, 1, 2, 3]
def baseStart_2283543 : Nat := 118140960795 + 2283543 * 2 ^ 59
def prefixEnd_2283543 : Nat := 4983230072969 + 3 ^ 40 * 2283543 * 2
def baseEnd_2283543 : Nat := 781703436140042907473789

theorem tailTrace_2283543 : CollatzResearch.WordTrace tailWord_2283543 prefixEnd_2283543 781703436140042907473789 := by
  unfold tailWord_2283543
  simp only [CollatzResearch.WordTrace]
  refine ⟨83287655566121183940175283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55525103710747455960116855 83287655566121183940175283)
  ·
    refine ⟨124931483349181775910262925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83287655566121183940175283 124931483349181775910262925)
    ·
      refine ⟨46849306255943165966348597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 124931483349181775910262925 46849306255943165966348597)
      ·
        refine ⟨4392122461494671809345181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46849306255943165966348597 4392122461494671809345181)
        ·
          refine ⟨1647045923060501928504443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4392122461494671809345181 1647045923060501928504443)
          ·
            refine ⟨2470568884590752892756665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1647045923060501928504443 2470568884590752892756665)
            ·
              refine ⟨1852926663443064669567499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2470568884590752892756665 1852926663443064669567499)
              ·
                refine ⟨2779389995164597004351249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1852926663443064669567499 2779389995164597004351249)
                ·
                  refine ⟨2084542496373447753263437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2779389995164597004351249 2084542496373447753263437)
                  ·
                    refine ⟨781703436140042907473789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2084542496373447753263437 781703436140042907473789)
                    ·
                      rfl

theorem cell22_2283543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 3, 1, 2, 1, 2, 3].length) (baseStart_2283543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283543 prefixEnd_2283543 := by exact prefixLift 2283543
  have htrace : WordTrace (prefixWord ++ tailWord_2283543) baseStart_2283543 baseEnd_2283543 := by
    simpa [prefixWord, tailWord_2283543, baseEnd_2283543] using wordTrace_append hprefix tailTrace_2283543
  have hstable : (prefixWord ++ tailWord_2283543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283543).length < 2 ^ (prefixWord ++ tailWord_2283543).sum := by decide
  have hdescent : baseEnd_2283543 < baseStart_2283543 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283597 : List Nat := [1, 6, 1, 1, 1, 1, 1, 1, 5, 4]
def baseStart_2283597 : Nat := 118140960795 + 2283597 * 2 ^ 59
def prefixEnd_2283597 : Nat := 4983230072969 + 3 ^ 40 * 2283597 * 2
def baseEnd_2283597 : Nat := 781721921443604766623623

theorem tailTrace_2283597 : CollatzResearch.WordTrace tailWord_2283597 prefixEnd_2283597 781721921443604766623623 := by
  unfold tailWord_2283597
  simp only [CollatzResearch.WordTrace]
  refine ⟨83289625107925551162641045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55526416738617034108427363 83289625107925551162641045)
  ·
    refine ⟨3904201176934010210748799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 83289625107925551162641045 3904201176934010210748799)
    ·
      refine ⟨5856301765401015316123199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3904201176934010210748799 5856301765401015316123199)
      ·
        refine ⟨8784452648101522974184799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5856301765401015316123199 8784452648101522974184799)
        ·
          refine ⟨13176678972152284461277199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8784452648101522974184799 13176678972152284461277199)
          ·
            refine ⟨19765018458228426691915799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13176678972152284461277199 19765018458228426691915799)
            ·
              refine ⟨29647527687342640037873699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19765018458228426691915799 29647527687342640037873699)
              ·
                refine ⟨44471291531013960056810549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29647527687342640037873699 44471291531013960056810549)
                ·
                  refine ⟨4169183581032558755325989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44471291531013960056810549 4169183581032558755325989)
                  ·
                    refine ⟨781721921443604766623623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4169183581032558755325989 781721921443604766623623)
                    ·
                      rfl

theorem cell22_2283597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 1, 1, 5, 4].length) (baseStart_2283597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283597 prefixEnd_2283597 := by exact prefixLift 2283597
  have htrace : WordTrace (prefixWord ++ tailWord_2283597) baseStart_2283597 baseEnd_2283597 := by
    simpa [prefixWord, tailWord_2283597, baseEnd_2283597] using wordTrace_append hprefix tailTrace_2283597
  have hstable : (prefixWord ++ tailWord_2283597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283597).length < 2 ^ (prefixWord ++ tailWord_2283597).sum := by decide
  have hdescent : baseEnd_2283597 < baseStart_2283597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283612 : List Nat := [2, 2, 4, 1, 1, 3, 1, 2, 6]
def baseStart_2283612 : Nat := 118140960795 + 2283612 * 2 ^ 59
def prefixEnd_2283612 : Nat := 4983230072969 + 3 ^ 40 * 2283612 * 2
def baseEnd_2283612 : Nat := 260575685416716575832859

theorem tailTrace_2283612 : CollatzResearch.WordTrace tailWord_2283612 prefixEnd_2283612 260575685416716575832859 := by
  unfold tailWord_2283612
  simp only [CollatzResearch.WordTrace]
  refine ⟨41645086101435604362218545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55526781468580805816291393 41645086101435604362218545)
  ·
    refine ⟨31233814576076703271663909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41645086101435604362218545 31233814576076703271663909)
    ·
      refine ⟨5856340233014381863436983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31233814576076703271663909 5856340233014381863436983)
      ·
        refine ⟨8784510349521572795155475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5856340233014381863436983 8784510349521572795155475)
        ·
          refine ⟨13176765524282359192733213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8784510349521572795155475 13176765524282359192733213)
          ·
            refine ⟨4941287071605884697274955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13176765524282359192733213 4941287071605884697274955)
            ·
              refine ⟨7411930607408827045912433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4941287071605884697274955 7411930607408827045912433)
              ·
                refine ⟨5558947955556620284434325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7411930607408827045912433 5558947955556620284434325)
                ·
                  refine ⟨260575685416716575832859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5558947955556620284434325 260575685416716575832859)
                  ·
                    rfl

theorem cell22_2283612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 6].length) (baseStart_2283612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283612 prefixEnd_2283612 := by exact prefixLift 2283612
  have htrace : WordTrace (prefixWord ++ tailWord_2283612) baseStart_2283612 baseEnd_2283612 := by
    simpa [prefixWord, tailWord_2283612, baseEnd_2283612] using wordTrace_append hprefix tailTrace_2283612
  have hstable : (prefixWord ++ tailWord_2283612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283612).length < 2 ^ (prefixWord ++ tailWord_2283612).sum := by decide
  have hdescent : baseEnd_2283612 < baseStart_2283612 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283625 : List Nat := [1, 2, 1, 1, 1, 5, 3, 1, 1, 6]
def baseStart_2283625 : Nat := 118140960795 + 2283625 * 2 ^ 59
def prefixEnd_2283625 : Nat := 4983230072969 + 3 ^ 40 * 2283625 * 2
def baseEnd_2283625 : Nat := 781731506415822026923537

theorem tailTrace_2283625 : CollatzResearch.WordTrace tailWord_2283625 prefixEnd_2283625 781731506415822026923537 := by
  unfold tailWord_2283625
  simp only [CollatzResearch.WordTrace]
  refine ⟨83290646351824111944660329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55527097567882741296440219 83290646351824111944660329)
  ·
    refine ⟨62467984763868083958495247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83290646351824111944660329 62467984763868083958495247)
    ·
      refine ⟨93701977145802125937742871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62467984763868083958495247 93701977145802125937742871)
      ·
        refine ⟨140552965718703188906614307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93701977145802125937742871 140552965718703188906614307)
        ·
          refine ⟨210829448578054783359921461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140552965718703188906614307 210829448578054783359921461)
          ·
            refine ⟨19765260804192635939992637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 210829448578054783359921461 19765260804192635939992637)
            ·
              refine ⟨7411972801572238477497239, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19765260804192635939992637 7411972801572238477497239)
              ·
                refine ⟨11117959202358357716245859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7411972801572238477497239 11117959202358357716245859)
                ·
                  refine ⟨16676938803537536574368789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11117959202358357716245859 16676938803537536574368789)
                  ·
                    refine ⟨781731506415822026923537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16676938803537536574368789 781731506415822026923537)
                    ·
                      rfl

theorem cell22_2283625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 3, 1, 1, 6].length) (baseStart_2283625 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283625 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283625 prefixEnd_2283625 := by exact prefixLift 2283625
  have htrace : WordTrace (prefixWord ++ tailWord_2283625) baseStart_2283625 baseEnd_2283625 := by
    simpa [prefixWord, tailWord_2283625, baseEnd_2283625] using wordTrace_append hprefix tailTrace_2283625
  have hstable : (prefixWord ++ tailWord_2283625).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283625).length < 2 ^ (prefixWord ++ tailWord_2283625).sum := by decide
  have hdescent : baseEnd_2283625 < baseStart_2283625 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283629 : List Nat := [1, 5, 1, 1, 2, 1, 4, 3, 4]
def baseStart_2283629 : Nat := 118140960795 + 2283629 * 2 ^ 59
def prefixEnd_2283629 : Nat := 4983230072969 + 3 ^ 40 * 2283629 * 2
def baseEnd_2283629 : Nat := 260577625232522449941175

theorem tailTrace_2283629 : CollatzResearch.WordTrace tailWord_2283629 prefixEnd_2283629 260577625232522449941175 := by
  unfold tailWord_2283629
  simp only [CollatzResearch.WordTrace]
  refine ⟨83290792243809620627805941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55527194829206413751870627 83290792243809620627805941)
  ·
    refine ⟨7808511772857151933856807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83290792243809620627805941 7808511772857151933856807)
    ·
      refine ⟨11712767659285727900785211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7808511772857151933856807 11712767659285727900785211)
      ·
        refine ⟨17569151488928591851177817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11712767659285727900785211 17569151488928591851177817)
        ·
          refine ⟨13176863616696443888383363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17569151488928591851177817 13176863616696443888383363)
          ·
            refine ⟨19765295425044665832575045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13176863616696443888383363 19765295425044665832575045)
            ·
              refine ⟨3705992892195874843607821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19765295425044665832575045 3705992892195874843607821)
              ·
                refine ⟨1389747334573453066352933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3705992892195874843607821 1389747334573453066352933)
                ·
                  refine ⟨260577625232522449941175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1389747334573453066352933 260577625232522449941175)
                  ·
                    rfl

theorem cell22_2283629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 1, 4, 3, 4].length) (baseStart_2283629 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283629 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283629 prefixEnd_2283629 := by exact prefixLift 2283629
  have htrace : WordTrace (prefixWord ++ tailWord_2283629) baseStart_2283629 baseEnd_2283629 := by
    simpa [prefixWord, tailWord_2283629, baseEnd_2283629] using wordTrace_append hprefix tailTrace_2283629
  have hstable : (prefixWord ++ tailWord_2283629).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283629).length < 2 ^ (prefixWord ++ tailWord_2283629).sum := by decide
  have hdescent : baseEnd_2283629 < baseStart_2283629 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283644 : List Nat := [2, 2, 2, 1, 1, 4, 3, 2, 2, 3]
def baseStart_2283644 : Nat := 118140960795 + 2283644 * 2 ^ 59
def prefixEnd_2283644 : Nat := 4983230072969 + 3 ^ 40 * 2283644 * 2
def baseEnd_2283644 : Nat := 781738010504112310698479

theorem tailTrace_2283644 : CollatzResearch.WordTrace tailWord_2283644 prefixEnd_2283644 781738010504112310698479 := by
  unfold tailWord_2283644
  simp only [CollatzResearch.WordTrace]
  refine ⟨41645669669377639094800993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55527559559170185459734657 41645669669377639094800993)
  ·
    refine ⟨31234252252033229321100745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41645669669377639094800993 31234252252033229321100745)
    ·
      refine ⟨23425689189024921990825559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31234252252033229321100745 23425689189024921990825559)
      ·
        refine ⟨35138533783537382986238339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23425689189024921990825559 35138533783537382986238339)
        ·
          refine ⟨52707800675306074479357509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35138533783537382986238339 52707800675306074479357509)
          ·
            refine ⟨9882712626619888964879533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52707800675306074479357509 9882712626619888964879533)
            ·
              refine ⟨3706017234982458361829825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9882712626619888964879533 3706017234982458361829825)
              ·
                refine ⟨2779512926236843771372369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3706017234982458361829825 2779512926236843771372369)
                ·
                  refine ⟨2084634694677632828529277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2779512926236843771372369 2084634694677632828529277)
                  ·
                    refine ⟨781738010504112310698479, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2084634694677632828529277 781738010504112310698479)
                    ·
                      rfl

theorem cell22_2283644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_2283644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283644 prefixEnd_2283644 := by exact prefixLift 2283644
  have htrace : WordTrace (prefixWord ++ tailWord_2283644) baseStart_2283644 baseEnd_2283644 := by
    simpa [prefixWord, tailWord_2283644, baseEnd_2283644] using wordTrace_append hprefix tailTrace_2283644
  have hstable : (prefixWord ++ tailWord_2283644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283644).length < 2 ^ (prefixWord ++ tailWord_2283644).sum := by decide
  have hdescent : baseEnd_2283644 < baseStart_2283644 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283685 : List Nat := [1, 3, 1, 2, 1, 3, 1, 1, 9]
def baseStart_2283685 : Nat := 118140960795 + 2283685 * 2 ^ 59
def prefixEnd_2283685 : Nat := 4983230072969 + 3 ^ 40 * 2283685 * 2
def baseEnd_2283685 : Nat := 260584015214000623474451

theorem tailTrace_2283685 : CollatzResearch.WordTrace tailWord_2283685 prefixEnd_2283685 260584015214000623474451 := by
  unfold tailWord_2283685
  simp only [CollatzResearch.WordTrace]
  refine ⟨83292834731606742191844509, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55528556487737828127896339 83292834731606742191844509)
  ·
    refine ⟨31234813024352528321941691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83292834731606742191844509 31234813024352528321941691)
    ·
      refine ⟨46852219536528792482912537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31234813024352528321941691 46852219536528792482912537)
      ·
        refine ⟨35139164652396594362184403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46852219536528792482912537 35139164652396594362184403)
        ·
          refine ⟨52708746978594891543276605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35139164652396594362184403 52708746978594891543276605)
          ·
            refine ⟨19765780116973084328728727, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52708746978594891543276605 19765780116973084328728727)
            ·
              refine ⟨29648670175459626493093091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19765780116973084328728727 29648670175459626493093091)
              ·
                refine ⟨44473005263189439739639637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29648670175459626493093091 44473005263189439739639637)
                ·
                  refine ⟨260584015214000623474451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44473005263189439739639637 260584015214000623474451)
                  ·
                    rfl

theorem cell22_2283685_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 3, 1, 1, 9].length) (baseStart_2283685 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283685 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283685 prefixEnd_2283685 := by exact prefixLift 2283685
  have htrace : WordTrace (prefixWord ++ tailWord_2283685) baseStart_2283685 baseEnd_2283685 := by
    simpa [prefixWord, tailWord_2283685, baseEnd_2283685] using wordTrace_append hprefix tailTrace_2283685
  have hstable : (prefixWord ++ tailWord_2283685).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283685).length < 2 ^ (prefixWord ++ tailWord_2283685).sum := by decide
  have hdescent : baseEnd_2283685 < baseStart_2283685 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283685) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283757 : List Nat := [1, 5, 1, 2, 4, 1, 2, 2, 1, 3]
def baseStart_2283757 : Nat := 118140960795 + 2283757 * 2 ^ 59
def prefixEnd_2283757 : Nat := 4983230072969 + 3 ^ 40 * 2283757 * 2
def baseEnd_2283757 : Nat := 781776692713417682623133

theorem tailTrace_2283757 : CollatzResearch.WordTrace tailWord_2283757 prefixEnd_2283757 781776692713417682623133 := by
  unfold tailWord_2283757
  simp only [CollatzResearch.WordTrace]
  refine ⟨83295460787345898488465525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55530307191563932325643683 83295460787345898488465525)
  ·
    refine ⟨7808949448813677983293643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83295460787345898488465525 7808949448813677983293643)
    ·
      refine ⟨11713424173220516974940465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7808949448813677983293643 11713424173220516974940465)
      ·
        refine ⟨8785068129915387731205349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11713424173220516974940465 8785068129915387731205349)
        ·
          refine ⟨1647200274359135199601003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 8785068129915387731205349 1647200274359135199601003)
          ·
            refine ⟨2470800411538702799401505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1647200274359135199601003 2470800411538702799401505)
            ·
              refine ⟨1853100308654027099551129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2470800411538702799401505 1853100308654027099551129)
              ·
                refine ⟨1389825231490520324663347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1853100308654027099551129 1389825231490520324663347)
                ·
                  refine ⟨2084737847235780486995021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1389825231490520324663347 2084737847235780486995021)
                  ·
                    refine ⟨781776692713417682623133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2084737847235780486995021 781776692713417682623133)
                    ·
                      rfl

theorem cell22_2283757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 2, 2, 1, 3].length) (baseStart_2283757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283757 prefixEnd_2283757 := by exact prefixLift 2283757
  have htrace : WordTrace (prefixWord ++ tailWord_2283757) baseStart_2283757 baseEnd_2283757 := by
    simpa [prefixWord, tailWord_2283757, baseEnd_2283757] using wordTrace_append hprefix tailTrace_2283757
  have hstable : (prefixWord ++ tailWord_2283757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283757).length < 2 ^ (prefixWord ++ tailWord_2283757).sum := by decide
  have hdescent : baseEnd_2283757 < baseStart_2283757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283777 : List Nat := [1, 2, 4, 1, 1, 2, 2, 2, 1, 6]
def baseStart_2283777 : Nat := 118140960795 + 2283777 * 2 ^ 59
def prefixEnd_2283777 : Nat := 4983230072969 + 3 ^ 40 * 2283777 * 2
def baseEnd_2283777 : Nat := 781783539122144297123071

theorem tailTrace_2283777 : CollatzResearch.WordTrace tailWord_2283777 prefixEnd_2283777 781783539122144297123071 := by
  unfold tailWord_2283777
  simp only [CollatzResearch.WordTrace]
  refine ⟨83296190247273441904193585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55530793498182294602795723 83296190247273441904193585)
  ·
    refine ⟨62472142685455081428145189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83296190247273441904193585 62472142685455081428145189)
    ·
      refine ⟨11713526753522827767777223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62472142685455081428145189 11713526753522827767777223)
      ·
        refine ⟨17570290130284241651665835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11713526753522827767777223 17570290130284241651665835)
        ·
          refine ⟨26355435195426362477498753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17570290130284241651665835 26355435195426362477498753)
          ·
            refine ⟨19766576396569771858124065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26355435195426362477498753 19766576396569771858124065)
            ·
              refine ⟨14824932297427328893593049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19766576396569771858124065 14824932297427328893593049)
              ·
                refine ⟨11118699223070496670194787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14824932297427328893593049 11118699223070496670194787)
                ·
                  refine ⟨16678048834605745005292181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11118699223070496670194787 16678048834605745005292181)
                  ·
                    refine ⟨781783539122144297123071, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16678048834605745005292181 781783539122144297123071)
                    ·
                      rfl

theorem cell22_2283777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 1, 6].length) (baseStart_2283777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283777 prefixEnd_2283777 := by exact prefixLift 2283777
  have htrace : WordTrace (prefixWord ++ tailWord_2283777) baseStart_2283777 baseEnd_2283777 := by
    simpa [prefixWord, tailWord_2283777, baseEnd_2283777] using wordTrace_append hprefix tailTrace_2283777
  have hstable : (prefixWord ++ tailWord_2283777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283777).length < 2 ^ (prefixWord ++ tailWord_2283777).sum := by decide
  have hdescent : baseEnd_2283777 < baseStart_2283777 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283779 : List Nat := [1, 1, 1, 3, 2, 3, 1, 5, 2, 3]
def baseStart_2283779 : Nat := 118140960795 + 2283779 * 2 ^ 59
def prefixEnd_2283779 : Nat := 4983230072969 + 3 ^ 40 * 2283779 * 2
def baseEnd_2283779 : Nat := 781784223763016958573065

theorem tailTrace_2283779 : CollatzResearch.WordTrace tailWord_2283779 prefixEnd_2283779 781784223763016958573065 := by
  unfold tailWord_2283779
  simp only [CollatzResearch.WordTrace]
  refine ⟨83296263193266196245766391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55530842128844130830510927 83296263193266196245766391)
  ·
    refine ⟨124944394789899294368649587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83296263193266196245766391 124944394789899294368649587)
    ·
      refine ⟨187416592184848941552974381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124944394789899294368649587 187416592184848941552974381)
      ·
        refine ⟨70281222069318353082365393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187416592184848941552974381 70281222069318353082365393)
        ·
          refine ⟨52710916551988764811774045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70281222069318353082365393 52710916551988764811774045)
          ·
            refine ⟨19766593706995786804415267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52710916551988764811774045 19766593706995786804415267)
            ·
              refine ⟨29649890560493680206622901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19766593706995786804415267 29649890560493680206622901)
              ·
                refine ⟨2779677240046282519370897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29649890560493680206622901 2779677240046282519370897)
                ·
                  refine ⟨2084757930034711889528173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2779677240046282519370897 2084757930034711889528173)
                  ·
                    refine ⟨781784223763016958573065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2084757930034711889528173 781784223763016958573065)
                    ·
                      rfl

theorem cell22_2283779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 1, 5, 2, 3].length) (baseStart_2283779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283779 prefixEnd_2283779 := by exact prefixLift 2283779
  have htrace : WordTrace (prefixWord ++ tailWord_2283779) baseStart_2283779 baseEnd_2283779 := by
    simpa [prefixWord, tailWord_2283779, baseEnd_2283779] using wordTrace_append hprefix tailTrace_2283779
  have hstable : (prefixWord ++ tailWord_2283779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283779).length < 2 ^ (prefixWord ++ tailWord_2283779).sum := by decide
  have hdescent : baseEnd_2283779 < baseStart_2283779 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283813 : List Nat := [1, 3, 1, 2, 5, 2, 1, 2, 2, 3]
def baseStart_2283813 : Nat := 118140960795 + 2283813 * 2 ^ 59
def prefixEnd_2283813 : Nat := 4983230072969 + 3 ^ 40 * 2283813 * 2
def baseEnd_2283813 : Nat := 781795862657852203222961

theorem tailTrace_2283813 : CollatzResearch.WordTrace tailWord_2283813 prefixEnd_2283813 781795862657852203222961 := by
  unfold tailWord_2283813
  simp only [CollatzResearch.WordTrace]
  refine ⟨83297503275143020052504093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55531668850095346701669395 83297503275143020052504093)
  ·
    refine ⟨31236563728178632519689035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83297503275143020052504093 31236563728178632519689035)
    ·
      refine ⟨46854845592267948779533553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31236563728178632519689035 46854845592267948779533553)
      ·
        refine ⟨35141134194200961584650165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46854845592267948779533553 35141134194200961584650165)
        ·
          refine ⟨3294481330706340148560953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 35141134194200961584650165 3294481330706340148560953)
          ·
            refine ⟨2470860998029755111420715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3294481330706340148560953 2470860998029755111420715)
            ·
              refine ⟨3706291497044632667131073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2470860998029755111420715 3706291497044632667131073)
              ·
                refine ⟨2779718622783474500348305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3706291497044632667131073 2779718622783474500348305)
                ·
                  refine ⟨2084788967087605875261229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2779718622783474500348305 2084788967087605875261229)
                  ·
                    refine ⟨781795862657852203222961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2084788967087605875261229 781795862657852203222961)
                    ·
                      rfl

theorem cell22_2283813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 5, 2, 1, 2, 2, 3].length) (baseStart_2283813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283813 prefixEnd_2283813 := by exact prefixLift 2283813
  have htrace : WordTrace (prefixWord ++ tailWord_2283813) baseStart_2283813 baseEnd_2283813 := by
    simpa [prefixWord, tailWord_2283813, baseEnd_2283813] using wordTrace_append hprefix tailTrace_2283813
  have hstable : (prefixWord ++ tailWord_2283813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283813).length < 2 ^ (prefixWord ++ tailWord_2283813).sum := by decide
  have hdescent : baseEnd_2283813 < baseStart_2283813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283858 : List Nat := [3, 2, 2, 1, 1, 1, 5, 3, 1, 3]
def baseStart_2283858 : Nat := 118140960795 + 2283858 * 2 ^ 59
def prefixEnd_2283858 : Nat := 4983230072969 + 3 ^ 40 * 2283858 * 2
def baseEnd_2283858 : Nat := 781811267077487085847823

theorem tailTrace_2283858 : CollatzResearch.WordTrace tailWord_2283858 prefixEnd_2283858 781811267077487085847823 := by
  unfold tailWord_2283858
  simp only [CollatzResearch.WordTrace]
  refine ⟨20824786139994998184473057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55532763039986661825261485 20824786139994998184473057)
  ·
    refine ⟨15618589604996248638354793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20824786139994998184473057 15618589604996248638354793)
    ·
      refine ⟨11713942203747186478766095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15618589604996248638354793 11713942203747186478766095)
      ·
        refine ⟨17570913305620779718149143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11713942203747186478766095 17570913305620779718149143)
        ·
          refine ⟨26356369958431169577223715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17570913305620779718149143 26356369958431169577223715)
          ·
            refine ⟨39534554937646754365835573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26356369958431169577223715 39534554937646754365835573)
            ·
              refine ⟨3706364525404383221797085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39534554937646754365835573 3706364525404383221797085)
              ·
                refine ⟨1389886697026643708173907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3706364525404383221797085 1389886697026643708173907)
                ·
                  refine ⟨2084830045539965562260861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1389886697026643708173907 2084830045539965562260861)
                  ·
                    refine ⟨781811267077487085847823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2084830045539965562260861 781811267077487085847823)
                    ·
                      rfl

theorem cell22_2283858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 1, 5, 3, 1, 3].length) (baseStart_2283858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283858 prefixEnd_2283858 := by exact prefixLift 2283858
  have htrace : WordTrace (prefixWord ++ tailWord_2283858) baseStart_2283858 baseEnd_2283858 := by
    simpa [prefixWord, tailWord_2283858, baseEnd_2283858] using wordTrace_append hprefix tailTrace_2283858
  have hstable : (prefixWord ++ tailWord_2283858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283858).length < 2 ^ (prefixWord ++ tailWord_2283858).sum := by decide
  have hdescent : baseEnd_2283858 < baseStart_2283858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283901 : List Nat := [1, 4, 1, 1, 2, 3, 3, 2, 1, 4]
def baseStart_2283901 : Nat := 118140960795 + 2283901 * 2 ^ 59
def prefixEnd_2283901 : Nat := 4983230072969 + 3 ^ 40 * 2283901 * 2
def baseEnd_2283901 : Nat := 781825986856249307022691

theorem tailTrace_2283901 : CollatzResearch.WordTrace tailWord_2283901 prefixEnd_2283901 781825986856249307022691 := by
  unfold tailWord_2283901
  simp only [CollatzResearch.WordTrace]
  refine ⟨83300712898824211081707557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55533808599216140721138371 83300712898824211081707557)
  ·
    refine ⟨15618883668529539577820167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83300712898824211081707557 15618883668529539577820167)
    ·
      refine ⟨23428325502794309366730251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15618883668529539577820167 23428325502794309366730251)
      ·
        refine ⟨35142488254191464050095377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23428325502794309366730251 35142488254191464050095377)
        ·
          refine ⟨26356866190643598037571533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35142488254191464050095377 26356866190643598037571533)
          ·
            refine ⟨9883824821491349264089325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26356866190643598037571533 9883824821491349264089325)
            ·
              refine ⟨3706434308059255974033497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9883824821491349264089325 3706434308059255974033497)
              ·
                refine ⟨2779825731044441980525123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3706434308059255974033497 2779825731044441980525123)
                ·
                  refine ⟨4169738596566662970787685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2779825731044441980525123 4169738596566662970787685)
                  ·
                    refine ⟨781825986856249307022691, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4169738596566662970787685 781825986856249307022691)
                    ·
                      rfl

theorem cell22_2283901_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 3, 3, 2, 1, 4].length) (baseStart_2283901 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283901 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283901 prefixEnd_2283901 := by exact prefixLift 2283901
  have htrace : WordTrace (prefixWord ++ tailWord_2283901) baseStart_2283901 baseEnd_2283901 := by
    simpa [prefixWord, tailWord_2283901, baseEnd_2283901] using wordTrace_append hprefix tailTrace_2283901
  have hstable : (prefixWord ++ tailWord_2283901).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283901).length < 2 ^ (prefixWord ++ tailWord_2283901).sum := by decide
  have hdescent : baseEnd_2283901 < baseStart_2283901 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283901) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283929 : List Nat := [1, 2, 1, 2, 1, 4, 1, 4, 2, 4]
def baseStart_2283929 : Nat := 118140960795 + 2283929 * 2 ^ 59
def prefixEnd_2283929 : Nat := 4983230072969 + 3 ^ 40 * 2283929 * 2
def baseEnd_2283929 : Nat := 781835571828466567322605

theorem tailTrace_2283929 : CollatzResearch.WordTrace tailWord_2283929 prefixEnd_2283929 781835571828466567322605 := by
  unfold tailWord_2283929
  simp only [CollatzResearch.WordTrace]
  refine ⟨83301734142722771863726841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55534489428481847909151227 83301734142722771863726841)
  ·
    refine ⟨62476300607042078897795131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83301734142722771863726841 62476300607042078897795131)
    ·
      refine ⟨93714450910563118346692697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62476300607042078897795131 93714450910563118346692697)
      ·
        refine ⟨70285838182922338760019523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93714450910563118346692697 70285838182922338760019523)
        ·
          refine ⟨105428757274383508140029285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70285838182922338760019523 105428757274383508140029285)
          ·
            refine ⟨19767891988946907776255491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105428757274383508140029285 19767891988946907776255491)
            ·
              refine ⟨29651837983420361664383237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19767891988946907776255491 29651837983420361664383237)
              ·
                refine ⟨5559719621891317812071857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29651837983420361664383237 5559719621891317812071857)
                ·
                  refine ⟨4169789716418488359053893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5559719621891317812071857 4169789716418488359053893)
                  ·
                    refine ⟨781835571828466567322605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4169789716418488359053893 781835571828466567322605)
                    ·
                      rfl

theorem cell22_2283929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 4, 1, 4, 2, 4].length) (baseStart_2283929 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283929 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283929 prefixEnd_2283929 := by exact prefixLift 2283929
  have htrace : WordTrace (prefixWord ++ tailWord_2283929) baseStart_2283929 baseEnd_2283929 := by
    simpa [prefixWord, tailWord_2283929, baseEnd_2283929] using wordTrace_append hprefix tailTrace_2283929
  have hstable : (prefixWord ++ tailWord_2283929).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283929).length < 2 ^ (prefixWord ++ tailWord_2283929).sum := by decide
  have hdescent : baseEnd_2283929 < baseStart_2283929 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283933 : List Nat := [1, 4, 2, 1, 4, 1, 1, 4, 4]
def baseStart_2283933 : Nat := 118140960795 + 2283933 * 2 ^ 59
def prefixEnd_2283933 : Nat := 4983230072969 + 3 ^ 40 * 2283933 * 2
def baseEnd_2283933 : Nat := 260612313703403963407531

theorem tailTrace_2283933 : CollatzResearch.WordTrace tailWord_2283933 prefixEnd_2283933 260612313703403963407531 := by
  unfold tailWord_2283933
  simp only [CollatzResearch.WordTrace]
  refine ⟨83301880034708280546872453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55534586689805520364581635 83301880034708280546872453)
  ·
    refine ⟨15619102506507802602538585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83301880034708280546872453 15619102506507802602538585)
    ·
      refine ⟨11714326879880851951903939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15619102506507802602538585 11714326879880851951903939)
      ·
        refine ⟨17571490319821277927855909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11714326879880851951903939 17571490319821277927855909)
        ·
          refine ⟨3294654434966489611472983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17571490319821277927855909 3294654434966489611472983)
          ·
            refine ⟨4941981652449734417209475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3294654434966489611472983 4941981652449734417209475)
            ·
              refine ⟨7412972478674601625814213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4941981652449734417209475 7412972478674601625814213)
              ·
                refine ⟨1389932339751487804840165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7412972478674601625814213 1389932339751487804840165)
                ·
                  refine ⟨260612313703403963407531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1389932339751487804840165 260612313703403963407531)
                  ·
                    rfl

theorem cell22_2283933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_2283933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283933 prefixEnd_2283933 := by exact prefixLift 2283933
  have htrace : WordTrace (prefixWord ++ tailWord_2283933) baseStart_2283933 baseEnd_2283933 := by
    simpa [prefixWord, tailWord_2283933, baseEnd_2283933] using wordTrace_append hprefix tailTrace_2283933
  have hstable : (prefixWord ++ tailWord_2283933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283933).length < 2 ^ (prefixWord ++ tailWord_2283933).sum := by decide
  have hdescent : baseEnd_2283933 < baseStart_2283933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283961 : List Nat := [1, 2, 1, 4, 3, 2, 3, 6]
def baseStart_2283961 : Nat := 118140960795 + 2283961 * 2 ^ 59
def prefixEnd_2283961 : Nat := 4983230072969 + 3 ^ 40 * 2283961 * 2
def baseEnd_2283961 : Nat := 86871836231381016724723

theorem tailTrace_2283961 : CollatzResearch.WordTrace tailWord_2283961 prefixEnd_2283961 86871836231381016724723 := by
  unfold tailWord_2283961
  simp only [CollatzResearch.WordTrace]
  refine ⟨83302901278606841328891737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55535267519071227552594491 83302901278606841328891737)
  ·
    refine ⟨62477175958955130996668803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83302901278606841328891737 62477175958955130996668803)
    ·
      refine ⟨93715763938432696495003205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62477175958955130996668803 93715763938432696495003205)
      ·
        refine ⟨17571705738456130592813101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93715763938432696495003205 17571705738456130592813101)
        ·
          refine ⟨6589389651921048972304913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17571705738456130592813101 6589389651921048972304913)
          ·
            refine ⟨4942042238940786729228685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6589389651921048972304913 4942042238940786729228685)
            ·
              refine ⟨1853265839602795023460757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4942042238940786729228685 1853265839602795023460757)
              ·
                refine ⟨86871836231381016724723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1853265839602795023460757 86871836231381016724723)
                ·
                  rfl

theorem cell22_2283961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 3, 6].length) (baseStart_2283961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283961 prefixEnd_2283961 := by exact prefixLift 2283961
  have htrace : WordTrace (prefixWord ++ tailWord_2283961) baseStart_2283961 baseEnd_2283961 := by
    simpa [prefixWord, tailWord_2283961, baseEnd_2283961] using wordTrace_append hprefix tailTrace_2283961
  have hstable : (prefixWord ++ tailWord_2283961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283961).length < 2 ^ (prefixWord ++ tailWord_2283961).sum := by decide
  have hdescent : baseEnd_2283961 < baseStart_2283961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283969 : List Nat := [1, 2, 7, 1, 1, 2, 2, 1, 1, 4]
def baseStart_2283969 : Nat := 118140960795 + 2283969 * 2 ^ 59
def prefixEnd_2283969 : Nat := 4983230072969 + 3 ^ 40 * 2283969 * 2
def baseEnd_2283969 : Nat := 781849264645919796322483

theorem tailTrace_2283969 : CollatzResearch.WordTrace tailWord_2283969 prefixEnd_2283969 781849264645919796322483 := by
  unfold tailWord_2283969
  simp only [CollatzResearch.WordTrace]
  refine ⟨83303193062577858695182961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55535462041718572463455307 83303193062577858695182961)
  ·
    refine ⟨62477394796933394021387221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83303193062577858695182961 62477394796933394021387221)
    ·
      refine ⟨1464313940553126422376263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 62477394796933394021387221 1464313940553126422376263)
      ·
        refine ⟨2196470910829689633564395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1464313940553126422376263 2196470910829689633564395)
        ·
          refine ⟨3294706366244534450346593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2196470910829689633564395 3294706366244534450346593)
          ·
            refine ⟨2471029774683400837759945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3294706366244534450346593 2471029774683400837759945)
            ·
              refine ⟨1853272331012550628319959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2471029774683400837759945 1853272331012550628319959)
              ·
                refine ⟨2779908496518825942479939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1853272331012550628319959 2779908496518825942479939)
                ·
                  refine ⟨4169862744778238913719909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2779908496518825942479939 4169862744778238913719909)
                  ·
                    refine ⟨781849264645919796322483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4169862744778238913719909 781849264645919796322483)
                    ·
                      rfl

theorem cell22_2283969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 2, 1, 1, 4].length) (baseStart_2283969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283969 prefixEnd_2283969 := by exact prefixLift 2283969
  have htrace : WordTrace (prefixWord ++ tailWord_2283969) baseStart_2283969 baseEnd_2283969 := by
    simpa [prefixWord, tailWord_2283969, baseEnd_2283969] using wordTrace_append hprefix tailTrace_2283969
  have hstable : (prefixWord ++ tailWord_2283969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283969).length < 2 ^ (prefixWord ++ tailWord_2283969).sum := by decide
  have hdescent : baseEnd_2283969 < baseStart_2283969 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2283993 : List Nat := [1, 2, 1, 2, 4, 1, 1, 6, 1, 3]
def baseStart_2283993 : Nat := 118140960795 + 2283993 * 2 ^ 59
def prefixEnd_2283993 : Nat := 4983230072969 + 3 ^ 40 * 2283993 * 2
def baseEnd_2283993 : Nat := 781857480336391733722409

theorem tailTrace_2283993 : CollatzResearch.WordTrace tailWord_2283993 prefixEnd_2283993 781857480336391733722409 := by
  unfold tailWord_2283993
  simp only [CollatzResearch.WordTrace]
  refine ⟨83304068414490910794056633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55536045609660607196037755 83304068414490910794056633)
  ·
    refine ⟨62478051310868183095542475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83304068414490910794056633 62478051310868183095542475)
    ·
      refine ⟨93717076966302274643313713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62478051310868183095542475 93717076966302274643313713)
      ·
        refine ⟨70287807724726705982485285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93717076966302274643313713 70287807724726705982485285)
        ·
          refine ⟨13178963948386257371715991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70287807724726705982485285 13178963948386257371715991)
          ·
            refine ⟨19768445922579386057573987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13178963948386257371715991 19768445922579386057573987)
            ·
              refine ⟨29652668883869079086360981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19768445922579386057573987 29652668883869079086360981)
              ·
                refine ⟨1389968853931363082173171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29652668883869079086360981 1389968853931363082173171)
                ·
                  refine ⟨2084953280897044623259757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1389968853931363082173171 2084953280897044623259757)
                  ·
                    refine ⟨781857480336391733722409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2084953280897044623259757 781857480336391733722409)
                    ·
                      rfl

theorem cell22_2283993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 6, 1, 3].length) (baseStart_2283993 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2283993 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2283993 prefixEnd_2283993 := by exact prefixLift 2283993
  have htrace : WordTrace (prefixWord ++ tailWord_2283993) baseStart_2283993 baseEnd_2283993 := by
    simpa [prefixWord, tailWord_2283993, baseEnd_2283993] using wordTrace_append hprefix tailTrace_2283993
  have hstable : (prefixWord ++ tailWord_2283993).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2283993).length < 2 ^ (prefixWord ++ tailWord_2283993).sum := by decide
  have hdescent : baseEnd_2283993 < baseStart_2283993 := by decide
  rcases family_descends (prefixWord ++ tailWord_2283993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284049 : List Nat := [1, 2, 2, 1, 1, 2, 2, 1, 5, 5]
def baseStart_2284049 : Nat := 118140960795 + 2284049 * 2 ^ 59
def prefixEnd_2284049 : Nat := 4983230072969 + 3 ^ 40 * 2284049 * 2
def baseEnd_2284049 : Nat := 781876650280826254322237

theorem tailTrace_2284049 : CollatzResearch.WordTrace tailWord_2284049 prefixEnd_2284049 781876650280826254322237 := by
  unfold tailWord_2284049
  simp only [CollatzResearch.WordTrace]
  refine ⟨83306110902288032358095201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55537407268192021572063467 83306110902288032358095201)
  ·
    refine ⟨62479583176716024268571401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83306110902288032358095201 62479583176716024268571401)
    ·
      refine ⟨46859687382537018201428551, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62479583176716024268571401 46859687382537018201428551)
      ·
        refine ⟨70289531073805527302142827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46859687382537018201428551 70289531073805527302142827)
        ·
          refine ⟨105434296610708290953214241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70289531073805527302142827 105434296610708290953214241)
          ·
            refine ⟨79075722458031218214910681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105434296610708290953214241 79075722458031218214910681)
            ·
              refine ⟨59306791843523413661183011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79075722458031218214910681 59306791843523413661183011)
              ·
                refine ⟨88960187765285120491774517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59306791843523413661183011 88960187765285120491774517)
                ·
                  refine ⟨8340017602995480046103861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 88960187765285120491774517 8340017602995480046103861)
                  ·
                    refine ⟨781876650280826254322237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8340017602995480046103861 781876650280826254322237)
                    ·
                      rfl

theorem cell22_2284049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 5].length) (baseStart_2284049 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284049 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284049 prefixEnd_2284049 := by exact prefixLift 2284049
  have htrace : WordTrace (prefixWord ++ tailWord_2284049) baseStart_2284049 baseEnd_2284049 := by
    simpa [prefixWord, tailWord_2284049, baseEnd_2284049] using wordTrace_append hprefix tailTrace_2284049
  have hstable : (prefixWord ++ tailWord_2284049).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284049).length < 2 ^ (prefixWord ++ tailWord_2284049).sum := by decide
  have hdescent : baseEnd_2284049 < baseStart_2284049 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284066 : List Nat := [3, 3, 1, 1, 1, 1, 1, 5, 1, 5]
def baseStart_2284066 : Nat := 118140960795 + 2284066 * 2 ^ 59
def prefixEnd_2284066 : Nat := 4983230072969 + 3 ^ 40 * 2284066 * 2
def baseEnd_2284066 : Nat := 781882469728243876647185

theorem tailTrace_2284066 : CollatzResearch.WordTrace tailWord_2284066 prefixEnd_2284066 781882469728243876647185 := by
  unfold tailWord_2284066
  simp only [CollatzResearch.WordTrace]
  refine ⟨20826682735806611065366013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55537820628817629507642701 20826682735806611065366013)
  ·
    refine ⟨7810006025927479149512255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20826682735806611065366013 7810006025927479149512255)
    ·
      refine ⟨11715009038891218724268383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7810006025927479149512255 11715009038891218724268383)
      ·
        refine ⟨17572513558336828086402575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11715009038891218724268383 17572513558336828086402575)
        ·
          refine ⟨26358770337505242129603863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17572513558336828086402575 26358770337505242129603863)
          ·
            refine ⟨39538155506257863194405795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26358770337505242129603863 39538155506257863194405795)
            ·
              refine ⟨59307233259386794791608693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39538155506257863194405795 59307233259386794791608693)
              ·
                refine ⟨5560053118067512011713315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59307233259386794791608693 5560053118067512011713315)
                ·
                  refine ⟨8340079677101268017569973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5560053118067512011713315 8340079677101268017569973)
                  ·
                    refine ⟨781882469728243876647185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8340079677101268017569973 781882469728243876647185)
                    ·
                      rfl

theorem cell22_2284066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 1, 1, 5, 1, 5].length) (baseStart_2284066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284066 prefixEnd_2284066 := by exact prefixLift 2284066
  have htrace : WordTrace (prefixWord ++ tailWord_2284066) baseStart_2284066 baseEnd_2284066 := by
    simpa [prefixWord, tailWord_2284066, baseEnd_2284066] using wordTrace_append hprefix tailTrace_2284066
  have hstable : (prefixWord ++ tailWord_2284066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284066).length < 2 ^ (prefixWord ++ tailWord_2284066).sum := by decide
  have hdescent : baseEnd_2284066 < baseStart_2284066 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284081 : List Nat := [1, 2, 2, 3, 1, 1, 3, 3, 2, 4]
def baseStart_2284081 : Nat := 118140960795 + 2284081 * 2 ^ 59
def prefixEnd_2284081 : Nat := 4983230072969 + 3 ^ 40 * 2284081 * 2
def baseEnd_2284081 : Nat := 781887604534788837522139

theorem tailTrace_2284081 : CollatzResearch.WordTrace tailWord_2284081 prefixEnd_2284081 781887604534788837522139 := by
  unfold tailWord_2284081
  simp only [CollatzResearch.WordTrace]
  refine ⟨83307278038172101823260097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55538185358781401215506731 83307278038172101823260097)
  ·
    refine ⟨62480458528629076367445073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83307278038172101823260097 62480458528629076367445073)
    ·
      refine ⟨46860343896471807275583805, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62480458528629076367445073 46860343896471807275583805)
      ·
        refine ⟨17572628961176927728343927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46860343896471807275583805 17572628961176927728343927)
        ·
          refine ⟨26358943441765391592515891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17572628961176927728343927 26358943441765391592515891)
          ·
            refine ⟨39538415162648087388773837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26358943441765391592515891 39538415162648087388773837)
            ·
              refine ⟨14826905685993032770790189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39538415162648087388773837 14826905685993032770790189)
              ·
                refine ⟨5560089632247387289046321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14826905685993032770790189 5560089632247387289046321)
                ·
                  refine ⟨4170067224185540466784741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5560089632247387289046321 4170067224185540466784741)
                  ·
                    refine ⟨781887604534788837522139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4170067224185540466784741 781887604534788837522139)
                    ·
                      rfl

theorem cell22_2284081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 3, 2, 4].length) (baseStart_2284081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284081 prefixEnd_2284081 := by exact prefixLift 2284081
  have htrace : WordTrace (prefixWord ++ tailWord_2284081) baseStart_2284081 baseEnd_2284081 := by
    simpa [prefixWord, tailWord_2284081, baseEnd_2284081] using wordTrace_append hprefix tailTrace_2284081
  have hstable : (prefixWord ++ tailWord_2284081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284081).length < 2 ^ (prefixWord ++ tailWord_2284081).sum := by decide
  have hdescent : baseEnd_2284081 < baseStart_2284081 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284102 : List Nat := [6, 1, 1, 1, 2, 2, 1, 4, 4]
def baseStart_2284102 : Nat := 118140960795 + 2284102 * 2 ^ 59
def prefixEnd_2284102 : Nat := 4983230072969 + 3 ^ 40 * 2284102 * 2
def baseEnd_2284102 : Nat := 260631597754650594249025

theorem tailTrace_2284102 : CollatzResearch.WordTrace tailWord_2284102 prefixEnd_2284102 260631597754650594249025 := by
  unfold tailWord_2284102
  simp only [CollatzResearch.WordTrace]
  refine ⟨2603376374096750700305455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55538695980730681606516373 2603376374096750700305455)
  ·
    refine ⟨3905064561145126050458183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2603376374096750700305455 3905064561145126050458183)
    ·
      refine ⟨5857596841717689075687275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3905064561145126050458183 5857596841717689075687275)
      ·
        refine ⟨8786395262576533613530913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5857596841717689075687275 8786395262576533613530913)
        ·
          refine ⟨6589796446932400210148185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8786395262576533613530913 6589796446932400210148185)
          ·
            refine ⟨4942347335199300157611139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6589796446932400210148185 4942347335199300157611139)
            ·
              refine ⟨7413521002798950236416709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4942347335199300157611139 7413521002798950236416709)
              ·
                refine ⟨1390035188024803169328133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7413521002798950236416709 1390035188024803169328133)
                ·
                  refine ⟨260631597754650594249025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1390035188024803169328133 260631597754650594249025)
                  ·
                    rfl

theorem cell22_2284102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_2284102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284102 prefixEnd_2284102 := by exact prefixLift 2284102
  have htrace : WordTrace (prefixWord ++ tailWord_2284102) baseStart_2284102 baseEnd_2284102 := by
    simpa [prefixWord, tailWord_2284102, baseEnd_2284102] using wordTrace_append hprefix tailTrace_2284102
  have hstable : (prefixWord ++ tailWord_2284102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284102).length < 2 ^ (prefixWord ++ tailWord_2284102).sum := by decide
  have hdescent : baseEnd_2284102 < baseStart_2284102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284156 : List Nat := [2, 2, 2, 1, 1, 2, 3, 2, 2, 5]
def baseStart_2284156 : Nat := 118140960795 + 2284156 * 2 ^ 59
def prefixEnd_2284156 : Nat := 4983230072969 + 3 ^ 40 * 2284156 * 2
def baseEnd_2284156 : Nat := 781913278567513641896909

theorem tailTrace_2284156 : CollatzResearch.WordTrace tailWord_2284156 prefixEnd_2284156 781913278567513641896909 := by
  unfold tailWord_2284156
  simp only [CollatzResearch.WordTrace]
  refine ⟨41655006756450194816120161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55540009008600259754826881 41655006756450194816120161)
  ·
    refine ⟨31241255067337646112090121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41655006756450194816120161 31241255067337646112090121)
    ·
      refine ⟨23430941300503234584067591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31241255067337646112090121 23430941300503234584067591)
      ·
        refine ⟨35146411950754851876101387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23430941300503234584067591 35146411950754851876101387)
        ·
          refine ⟨52719617926132277814152081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35146411950754851876101387 52719617926132277814152081)
          ·
            refine ⟨39539713444599208360614061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52719617926132277814152081 39539713444599208360614061)
            ·
              refine ⟨14827392541724703135230273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39539713444599208360614061 14827392541724703135230273)
              ·
                refine ⟨11120544406293527351422705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14827392541724703135230273 11120544406293527351422705)
                ·
                  refine ⟨8340408304720145513567029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11120544406293527351422705 8340408304720145513567029)
                  ·
                    refine ⟨781913278567513641896909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8340408304720145513567029 781913278567513641896909)
                    ·
                      rfl

theorem cell22_2284156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 3, 2, 2, 5].length) (baseStart_2284156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284156 prefixEnd_2284156 := by exact prefixLift 2284156
  have htrace : WordTrace (prefixWord ++ tailWord_2284156) baseStart_2284156 baseEnd_2284156 := by
    simpa [prefixWord, tailWord_2284156, baseEnd_2284156] using wordTrace_append hprefix tailTrace_2284156
  have hstable : (prefixWord ++ tailWord_2284156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284156).length < 2 ^ (prefixWord ++ tailWord_2284156).sum := by decide
  have hdescent : baseEnd_2284156 < baseStart_2284156 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284171 : List Nat := [1, 1, 1, 1, 4, 1, 2, 4, 3, 4]
def baseStart_2284171 : Nat := 118140960795 + 2284171 * 2 ^ 59
def prefixEnd_2284171 : Nat := 4983230072969 + 3 ^ 40 * 2284171 * 2
def baseEnd_2284171 : Nat := 781918413374058602771863

theorem tailTrace_2284171 : CollatzResearch.WordTrace tailWord_2284171 prefixEnd_2284171 781918413374058602771863 := by
  unfold tailWord_2284171
  simp only [CollatzResearch.WordTrace]
  refine ⟨83310560607846047194036367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55540373738564031462690911 83310560607846047194036367)
  ·
    refine ⟨124965840911769070791054551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83310560607846047194036367 124965840911769070791054551)
    ·
      refine ⟨187448761367653606186581827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124965840911769070791054551 187448761367653606186581827)
      ·
        refine ⟨281173142051480409279872741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187448761367653606186581827 281173142051480409279872741)
        ·
          refine ⟨52719964134652576739976139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 281173142051480409279872741 52719964134652576739976139)
          ·
            refine ⟨79079946201978865109964209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52719964134652576739976139 79079946201978865109964209)
            ·
              refine ⟨59309959651484148832473157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79079946201978865109964209 59309959651484148832473157)
              ·
                refine ⟨11120617434653277906088717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59309959651484148832473157 11120617434653277906088717)
                ·
                  refine ⟨4170231537994979214783269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11120617434653277906088717 4170231537994979214783269)
                  ·
                    refine ⟨781918413374058602771863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4170231537994979214783269 781918413374058602771863)
                    ·
                      rfl

theorem cell22_2284171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 2, 4, 3, 4].length) (baseStart_2284171 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284171 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284171 prefixEnd_2284171 := by exact prefixLift 2284171
  have htrace : WordTrace (prefixWord ++ tailWord_2284171) baseStart_2284171 baseEnd_2284171 := by
    simpa [prefixWord, tailWord_2284171, baseEnd_2284171] using wordTrace_append hprefix tailTrace_2284171
  have hstable : (prefixWord ++ tailWord_2284171).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284171).length < 2 ^ (prefixWord ++ tailWord_2284171).sum := by decide
  have hdescent : baseEnd_2284171 < baseStart_2284171 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284205 : List Nat := [1, 5, 2, 1, 1, 2, 2, 3, 1, 4]
def baseStart_2284205 : Nat := 118140960795 + 2284205 * 2 ^ 59
def prefixEnd_2284205 : Nat := 4983230072969 + 3 ^ 40 * 2284205 * 2
def baseEnd_2284205 : Nat := 781930052268893847421759

theorem tailTrace_2284205 : CollatzResearch.WordTrace tailWord_2284205 prefixEnd_2284205 781930052268893847421759 := by
  unfold tailWord_2284205
  simp only [CollatzResearch.WordTrace]
  refine ⟨83311800689722871000774069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55541200459815247333849379 83311800689722871000774069)
  ·
    refine ⟨7810481314661519156322569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83311800689722871000774069 7810481314661519156322569)
    ·
      refine ⟨5857860985996139367241927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7810481314661519156322569 5857860985996139367241927)
      ·
        refine ⟨8786791478994209050862891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5857860985996139367241927 8786791478994209050862891)
        ·
          refine ⟨13180187218491313576294337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8786791478994209050862891 13180187218491313576294337)
          ·
            refine ⟨9885140413868485182220753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13180187218491313576294337 9885140413868485182220753)
            ·
              refine ⟨7413855310401363886665565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9885140413868485182220753 7413855310401363886665565)
              ·
                refine ⟨2780195741400511457499587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7413855310401363886665565 2780195741400511457499587)
                ·
                  refine ⟨4170293612100767186249381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2780195741400511457499587 4170293612100767186249381)
                  ·
                    refine ⟨781930052268893847421759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4170293612100767186249381 781930052268893847421759)
                    ·
                      rfl

theorem cell22_2284205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 3, 1, 4].length) (baseStart_2284205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284205 prefixEnd_2284205 := by exact prefixLift 2284205
  have htrace : WordTrace (prefixWord ++ tailWord_2284205) baseStart_2284205 baseEnd_2284205 := by
    simpa [prefixWord, tailWord_2284205, baseEnd_2284205] using wordTrace_append hprefix tailTrace_2284205
  have hstable : (prefixWord ++ tailWord_2284205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284205).length < 2 ^ (prefixWord ++ tailWord_2284205).sum := by decide
  have hdescent : baseEnd_2284205 < baseStart_2284205 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284218 : List Nat := [3, 1, 1, 1, 2, 3, 1, 3, 4, 3]
def baseStart_2284218 : Nat := 118140960795 + 2284218 * 2 ^ 59
def prefixEnd_2284218 : Nat := 4983230072969 + 3 ^ 40 * 2284218 * 2
def baseEnd_2284218 : Nat := 781934502434566146846719

theorem tailTrace_2284218 : CollatzResearch.WordTrace tailWord_2284218 prefixEnd_2284218 781934502434566146846719 := by
  unfold tailWord_2284218
  simp only [CollatzResearch.WordTrace]
  refine ⟨20828068709668943555249327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55541516559117182813998205 20828068709668943555249327)
  ·
    refine ⟨31242103064503415332873991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20828068709668943555249327 31242103064503415332873991)
    ·
      refine ⟨46863154596755122999310987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31242103064503415332873991 46863154596755122999310987)
      ·
        refine ⟨70294731895132684498966481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46863154596755122999310987 70294731895132684498966481)
        ·
          refine ⟨52721048921349513374224861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70294731895132684498966481 52721048921349513374224861)
          ·
            refine ⟨19770393345506067515334323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52721048921349513374224861 19770393345506067515334323)
            ·
              refine ⟨29655590018259101273001485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19770393345506067515334323 29655590018259101273001485)
              ·
                refine ⟨11120846256847162977375557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29655590018259101273001485 11120846256847162977375557)
                ·
                  refine ⟨2085158673158843058257917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11120846256847162977375557 2085158673158843058257917)
                  ·
                    refine ⟨781934502434566146846719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2085158673158843058257917 781934502434566146846719)
                    ·
                      rfl

theorem cell22_2284218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 3, 4, 3].length) (baseStart_2284218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284218 prefixEnd_2284218 := by exact prefixLift 2284218
  have htrace : WordTrace (prefixWord ++ tailWord_2284218) baseStart_2284218 baseEnd_2284218 := by
    simpa [prefixWord, tailWord_2284218, baseEnd_2284218] using wordTrace_append hprefix tailTrace_2284218
  have hstable : (prefixWord ++ tailWord_2284218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284218).length < 2 ^ (prefixWord ++ tailWord_2284218).sum := by decide
  have hdescent : baseEnd_2284218 < baseStart_2284218 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284278 : List Nat := [5, 1, 1, 1, 1, 2, 1, 1, 1, 8]
def baseStart_2284278 : Nat := 118140960795 + 2284278 * 2 ^ 59
def prefixEnd_2284278 : Nat := 4983230072969 + 3 ^ 40 * 2284278 * 2
def baseEnd_2284278 : Nat := 781955041660745990346535

theorem tailTrace_2284278 : CollatzResearch.WordTrace tailWord_2284278 prefixEnd_2284278 781955041660745990346535 := by
  unfold tailWord_2284278
  simp only [CollatzResearch.WordTrace]
  refine ⟨5207153951153650279261343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55542975478972269645454325 5207153951153650279261343)
  ·
    refine ⟨7810730926730475418892015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5207153951153650279261343 7810730926730475418892015)
    ·
      refine ⟨11716096390095713128338023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7810730926730475418892015 11716096390095713128338023)
      ·
        refine ⟨17574144585143569692507035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11716096390095713128338023 17574144585143569692507035)
        ·
          refine ⟨26361216877715354538760553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17574144585143569692507035 26361216877715354538760553)
          ·
            refine ⟨19770912658286515904070415, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26361216877715354538760553 19770912658286515904070415)
            ·
              refine ⟨29656368987429773856105623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19770912658286515904070415 29656368987429773856105623)
              ·
                refine ⟨44484553481144660784158435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29656368987429773856105623 44484553481144660784158435)
                ·
                  refine ⟨66726830221716991176237653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44484553481144660784158435 66726830221716991176237653)
                  ·
                    refine ⟨781955041660745990346535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66726830221716991176237653 781955041660745990346535)
                    ·
                      rfl

theorem cell22_2284278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_2284278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284278 prefixEnd_2284278 := by exact prefixLift 2284278
  have htrace : WordTrace (prefixWord ++ tailWord_2284278) baseStart_2284278 baseEnd_2284278 := by
    simpa [prefixWord, tailWord_2284278, baseEnd_2284278] using wordTrace_append hprefix tailTrace_2284278
  have hstable : (prefixWord ++ tailWord_2284278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284278).length < 2 ^ (prefixWord ++ tailWord_2284278).sum := by decide
  have hdescent : baseEnd_2284278 < baseStart_2284278 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284368 : List Nat := [2, 1, 1, 1, 1, 4, 4, 1, 1, 6]
def baseStart_2284368 : Nat := 118140960795 + 2284368 * 2 ^ 59
def prefixEnd_2284368 : Nat := 4983230072969 + 3 ^ 40 * 2284368 * 2
def baseEnd_2284368 : Nat := 781985850500015755596259

theorem tailTrace_2284368 : CollatzResearch.WordTrace tailWord_2284368 prefixEnd_2284368 781985850500015755596259 := by
  unfold tailWord_2284368
  simp only [CollatzResearch.WordTrace]
  refine ⟨41658872894066174919478879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55545163858754899892638505 41658872894066174919478879)
  ·
    refine ⟨62488309341099262379218319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41658872894066174919478879 62488309341099262379218319)
    ·
      refine ⟨93732464011648893568827479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62488309341099262379218319 93732464011648893568827479)
      ·
        refine ⟨140598696017473340353241219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93732464011648893568827479 140598696017473340353241219)
        ·
          refine ⟨210898044026210010529861829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140598696017473340353241219 210898044026210010529861829)
          ·
            refine ⟨39543383254914376974349093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 210898044026210010529861829 39543383254914376974349093)
            ·
              refine ⟨7414384360296445682690455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39543383254914376974349093 7414384360296445682690455)
              ·
                refine ⟨11121576540444668524035683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7414384360296445682690455 11121576540444668524035683)
                ·
                  refine ⟨16682364810667002786053525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11121576540444668524035683 16682364810667002786053525)
                  ·
                    refine ⟨781985850500015755596259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16682364810667002786053525 781985850500015755596259)
                    ·
                      rfl

theorem cell22_2284368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 1, 6].length) (baseStart_2284368 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284368 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284368 prefixEnd_2284368 := by exact prefixLift 2284368
  have htrace : WordTrace (prefixWord ++ tailWord_2284368) baseStart_2284368 baseEnd_2284368 := by
    simpa [prefixWord, tailWord_2284368, baseEnd_2284368] using wordTrace_append hprefix tailTrace_2284368
  have hstable : (prefixWord ++ tailWord_2284368).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284368).length < 2 ^ (prefixWord ++ tailWord_2284368).sum := by decide
  have hdescent : baseEnd_2284368 < baseStart_2284368 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284370 : List Nat := [3, 2, 2, 1, 1, 2, 1, 1, 6, 3]
def baseStart_2284370 : Nat := 118140960795 + 2284370 * 2 ^ 59
def prefixEnd_2284370 : Nat := 4983230072969 + 3 ^ 40 * 2284370 * 2
def baseEnd_2284370 : Nat := 781986535140888417046253

theorem tailTrace_2284370 : CollatzResearch.WordTrace tailWord_2284370 prefixEnd_2284370 781986535140888417046253 := by
  unfold tailWord_2284370
  simp only [CollatzResearch.WordTrace]
  refine ⟨20829454683531276045132641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55545212489416736120353709 20829454683531276045132641)
  ·
    refine ⟨15622091012648457033849481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20829454683531276045132641 15622091012648457033849481)
    ·
      refine ⟨11716568259486342775387111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15622091012648457033849481 11716568259486342775387111)
      ·
        refine ⟨17574852389229514163080667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11716568259486342775387111 17574852389229514163080667)
        ·
          refine ⟨26362278583844271244621001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17574852389229514163080667 26362278583844271244621001)
          ·
            refine ⟨19771708937883203433465751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26362278583844271244621001 19771708937883203433465751)
            ·
              refine ⟨29657563406824805150198627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19771708937883203433465751 29657563406824805150198627)
              ·
                refine ⟨44486345110237207725297941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29657563406824805150198627 44486345110237207725297941)
                ·
                  refine ⟨2085297427042369112123341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 44486345110237207725297941 2085297427042369112123341)
                  ·
                    refine ⟨781986535140888417046253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2085297427042369112123341 781986535140888417046253)
                    ·
                      rfl

theorem cell22_2284370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 2, 1, 1, 6, 3].length) (baseStart_2284370 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284370 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284370 prefixEnd_2284370 := by exact prefixLift 2284370
  have htrace : WordTrace (prefixWord ++ tailWord_2284370) baseStart_2284370 baseEnd_2284370 := by
    simpa [prefixWord, tailWord_2284370, baseEnd_2284370] using wordTrace_append hprefix tailTrace_2284370
  have hstable : (prefixWord ++ tailWord_2284370).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284370).length < 2 ^ (prefixWord ++ tailWord_2284370).sum := by decide
  have hdescent : baseEnd_2284370 < baseStart_2284370 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284415 : List Nat := [1, 1, 2, 2, 1, 1, 4, 4, 3, 3]
def baseStart_2284415 : Nat := 118140960795 + 2284415 * 2 ^ 59
def prefixEnd_2284415 : Nat := 4983230072969 + 3 ^ 40 * 2284415 * 2
def baseEnd_2284415 : Nat := 782001939560523299671115

theorem tailTrace_2284415 : CollatzResearch.WordTrace tailWord_2284415 prefixEnd_2284415 782001939560523299671115 := by
  unfold tailWord_2284415
  simp only [CollatzResearch.WordTrace]
  refine ⟨83319460018962076865918699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55546306679308051243945799 83319460018962076865918699)
  ·
    refine ⟨124979190028443115298878049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83319460018962076865918699 124979190028443115298878049)
    ·
      refine ⟨93734392521332336474158537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 124979190028443115298878049 93734392521332336474158537)
      ·
        refine ⟨70300794390999252355618903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93734392521332336474158537 70300794390999252355618903)
        ·
          refine ⟨105451191586498878533428355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70300794390999252355618903 105451191586498878533428355)
          ·
            refine ⟨158176787379748317800142533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105451191586498878533428355 158176787379748317800142533)
            ·
              refine ⟨29658147633702809587526725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 158176787379748317800142533 29658147633702809587526725)
              ·
                refine ⟨5560902681319276797661261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29658147633702809587526725 5560902681319276797661261)
                ·
                  refine ⟨2085338505494728799122973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5560902681319276797661261 2085338505494728799122973)
                  ·
                    refine ⟨782001939560523299671115, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2085338505494728799122973 782001939560523299671115)
                    ·
                      rfl

theorem cell22_2284415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 4, 4, 3, 3].length) (baseStart_2284415 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284415 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284415 prefixEnd_2284415 := by exact prefixLift 2284415
  have htrace : WordTrace (prefixWord ++ tailWord_2284415) baseStart_2284415 baseEnd_2284415 := by
    simpa [prefixWord, tailWord_2284415, baseEnd_2284415] using wordTrace_append hprefix tailTrace_2284415
  have hstable : (prefixWord ++ tailWord_2284415).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284415).length < 2 ^ (prefixWord ++ tailWord_2284415).sum := by decide
  have hdescent : baseEnd_2284415 < baseStart_2284415 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284428 : List Nat := [2, 2, 1, 2, 1, 2, 2, 1, 9]
def baseStart_2284428 : Nat := 118140960795 + 2284428 * 2 ^ 59
def prefixEnd_2284428 : Nat := 4983230072969 + 3 ^ 40 * 2284428 * 2
def baseEnd_2284428 : Nat := 260668796575398533032025

theorem tailTrace_2284428 : CollatzResearch.WordTrace tailWord_2284428 prefixEnd_2284428 260668796575398533032025 := by
  unfold tailWord_2284428
  simp only [CollatzResearch.WordTrace]
  refine ⟨41659967083957490043070969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55546622778609986724094625 41659967083957490043070969)
  ·
    refine ⟨31244975312968117532303227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41659967083957490043070969 31244975312968117532303227)
    ·
      refine ⟨46867462969452176298454841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31244975312968117532303227 46867462969452176298454841)
      ·
        refine ⟨35150597227089132223841131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46867462969452176298454841 35150597227089132223841131)
        ·
          refine ⟨52725895840633698335761697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35150597227089132223841131 52725895840633698335761697)
          ·
            refine ⟨39544421880475273751821273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52725895840633698335761697 39544421880475273751821273)
            ·
              refine ⟨29658316410356455313865955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39544421880475273751821273 29658316410356455313865955)
              ·
                refine ⟨44487474615534682970798933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29658316410356455313865955 44487474615534682970798933)
                ·
                  refine ⟨260668796575398533032025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44487474615534682970798933 260668796575398533032025)
                  ·
                    rfl

theorem cell22_2284428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 9].length) (baseStart_2284428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284428 prefixEnd_2284428 := by exact prefixLift 2284428
  have htrace : WordTrace (prefixWord ++ tailWord_2284428) baseStart_2284428 baseEnd_2284428 := by
    simpa [prefixWord, tailWord_2284428, baseEnd_2284428] using wordTrace_append hprefix tailTrace_2284428
  have hstable : (prefixWord ++ tailWord_2284428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284428).length < 2 ^ (prefixWord ++ tailWord_2284428).sum := by decide
  have hdescent : baseEnd_2284428 < baseStart_2284428 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284438 : List Nat := [5, 3, 1, 1, 1, 2, 2, 2, 2, 3]
def baseStart_2284438 : Nat := 118140960795 + 2284438 * 2 ^ 59
def prefixEnd_2284438 : Nat := 4983230072969 + 3 ^ 40 * 2284438 * 2
def baseEnd_2284438 : Nat := 782009812930558906346045

theorem tailTrace_2284438 : CollatzResearch.WordTrace tailWord_2284438 prefixEnd_2284438 782009812930558906346045 := by
  unfold tailWord_2284438
  simp only [CollatzResearch.WordTrace]
  refine ⟨5207518681117421987125373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55546865931919167862670645 5207518681117421987125373)
  ·
    refine ⟨1952819505419033245172015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5207518681117421987125373 1952819505419033245172015)
    ·
      refine ⟨2929229258128549867758023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1952819505419033245172015 2929229258128549867758023)
      ·
        refine ⟨4393843887192824801637035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2929229258128549867758023 4393843887192824801637035)
        ·
          refine ⟨6590765830789237202455553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4393843887192824801637035 6590765830789237202455553)
          ·
            refine ⟨4943074373091927901841665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6590765830789237202455553 4943074373091927901841665)
            ·
              refine ⟨3707305779818945926381249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4943074373091927901841665 3707305779818945926381249)
              ·
                refine ⟨2780479334864209444785937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3707305779818945926381249 2780479334864209444785937)
                ·
                  refine ⟨2085359501148157083589453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2780479334864209444785937 2085359501148157083589453)
                  ·
                    refine ⟨782009812930558906346045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2085359501148157083589453 782009812930558906346045)
                    ·
                      rfl

theorem cell22_2284438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 2, 2, 2, 2, 3].length) (baseStart_2284438 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284438 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284438 prefixEnd_2284438 := by exact prefixLift 2284438
  have htrace : WordTrace (prefixWord ++ tailWord_2284438) baseStart_2284438 baseEnd_2284438 := by
    simpa [prefixWord, tailWord_2284438, baseEnd_2284438] using wordTrace_append hprefix tailTrace_2284438
  have hstable : (prefixWord ++ tailWord_2284438).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284438).length < 2 ^ (prefixWord ++ tailWord_2284438).sum := by decide
  have hdescent : baseEnd_2284438 < baseStart_2284438 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284470 : List Nat := [5, 1, 4, 1, 2, 1, 1, 1, 2, 4]
def baseStart_2284470 : Nat := 118140960795 + 2284470 * 2 ^ 59
def prefixEnd_2284470 : Nat := 4983230072969 + 3 ^ 40 * 2284470 * 2
def baseEnd_2284470 : Nat := 782020767184521489545947

theorem tailTrace_2284470 : CollatzResearch.WordTrace tailWord_2284470 prefixEnd_2284470 782020767184521489545947 := by
  unfold tailWord_2284470
  simp only [CollatzResearch.WordTrace]
  refine ⟨5207591627110176328698179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55547644022508547506113909 5207591627110176328698179)
  ·
    refine ⟨7811387440665264493047269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5207591627110176328698179 7811387440665264493047269)
    ·
      refine ⟨1464635145124737092446363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 7811387440665264493047269 1464635145124737092446363)
      ·
        refine ⟨2196952717687105638669545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1464635145124737092446363 2196952717687105638669545)
        ·
          refine ⟨1647714538265329229002159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2196952717687105638669545 1647714538265329229002159)
          ·
            refine ⟨2471571807397993843503239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1647714538265329229002159 2471571807397993843503239)
            ·
              refine ⟨3707357711096990765254859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2471571807397993843503239 3707357711096990765254859)
              ·
                refine ⟨5561036566645486147882289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3707357711096990765254859 5561036566645486147882289)
                ·
                  refine ⟨4170777424984114610911717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5561036566645486147882289 4170777424984114610911717)
                  ·
                    refine ⟨782020767184521489545947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4170777424984114610911717 782020767184521489545947)
                    ·
                      rfl

theorem cell22_2284470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_2284470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284470 prefixEnd_2284470 := by exact prefixLift 2284470
  have htrace : WordTrace (prefixWord ++ tailWord_2284470) baseStart_2284470 baseEnd_2284470 := by
    simpa [prefixWord, tailWord_2284470, baseEnd_2284470] using wordTrace_append hprefix tailTrace_2284470
  have hstable : (prefixWord ++ tailWord_2284470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284470).length < 2 ^ (prefixWord ++ tailWord_2284470).sum := by decide
  have hdescent : baseEnd_2284470 < baseStart_2284470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284492 : List Nat := [2, 2, 1, 4, 1, 1, 3, 3, 1, 4]
def baseStart_2284492 : Nat := 118140960795 + 2284492 * 2 ^ 59
def prefixEnd_2284492 : Nat := 4983230072969 + 3 ^ 40 * 2284492 * 2
def baseEnd_2284492 : Nat := 782028298234120765495879

theorem tailTrace_2284492 : CollatzResearch.WordTrace tailWord_2284492 prefixEnd_2284492 782028298234120765495879 := by
  unfold tailWord_2284492
  simp only [CollatzResearch.WordTrace]
  refine ⟨41661134219841559508235865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55548178959788746010981153 41661134219841559508235865)
  ·
    refine ⟨31245850664881169631176899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41661134219841559508235865 31245850664881169631176899)
    ·
      refine ⟨46868775997321754446765349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31245850664881169631176899 46868775997321754446765349)
      ·
        refine ⟨8787895499497828958768503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46868775997321754446765349 8787895499497828958768503)
        ·
          refine ⟨13181843249246743438152755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8787895499497828958768503 13181843249246743438152755)
          ·
            refine ⟨19772764873870115157229133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13181843249246743438152755 19772764873870115157229133)
            ·
              refine ⟨7414786827701293183960925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19772764873870115157229133 7414786827701293183960925)
              ·
                refine ⟨2780545060387984943985347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7414786827701293183960925 2780545060387984943985347)
                ·
                  refine ⟨4170817590581977415978021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2780545060387984943985347 4170817590581977415978021)
                  ·
                    refine ⟨782028298234120765495879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4170817590581977415978021 782028298234120765495879)
                    ·
                      rfl

theorem cell22_2284492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 3, 1, 4].length) (baseStart_2284492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284492 prefixEnd_2284492 := by exact prefixLift 2284492
  have htrace : WordTrace (prefixWord ++ tailWord_2284492) baseStart_2284492 baseEnd_2284492 := by
    simpa [prefixWord, tailWord_2284492, baseEnd_2284492] using wordTrace_append hprefix tailTrace_2284492
  have hstable : (prefixWord ++ tailWord_2284492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284492).length < 2 ^ (prefixWord ++ tailWord_2284492).sum := by decide
  have hdescent : baseEnd_2284492 < baseStart_2284492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284520 : List Nat := [2, 1, 4, 1, 1, 1, 3, 2, 1, 6]
def baseStart_2284520 : Nat := 118140960795 + 2284520 * 2 ^ 59
def prefixEnd_2284520 : Nat := 4983230072969 + 3 ^ 40 * 2284520 * 2
def baseEnd_2284520 : Nat := 782037883206338025795793

theorem tailTrace_2284520 : CollatzResearch.WordTrace tailWord_2284520 prefixEnd_2284520 782037883206338025795793 := by
  unfold tailWord_2284520
  simp only [CollatzResearch.WordTrace]
  refine ⟨41661644841790839899245507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55548859789054453198994009 41661644841790839899245507)
  ·
    refine ⟨62492467262686259848868261, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41661644841790839899245507 62492467262686259848868261)
    ·
      refine ⟨11717337611753673721662799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62492467262686259848868261 11717337611753673721662799)
      ·
        refine ⟨17576006417630510582494199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11717337611753673721662799 17576006417630510582494199)
        ·
          refine ⟨26364009626445765873741299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17576006417630510582494199 26364009626445765873741299)
          ·
            refine ⟨39546014439668648810611949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26364009626445765873741299 39546014439668648810611949)
            ·
              refine ⟨14829755414875743303979481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39546014439668648810611949 14829755414875743303979481)
              ·
                refine ⟨11122316561156807477984611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14829755414875743303979481 11122316561156807477984611)
                ·
                  refine ⟨16683474841735211216976917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11122316561156807477984611 16683474841735211216976917)
                  ·
                    refine ⟨782037883206338025795793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16683474841735211216976917 782037883206338025795793)
                    ·
                      rfl

theorem cell22_2284520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 3, 2, 1, 6].length) (baseStart_2284520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284520 prefixEnd_2284520 := by exact prefixLift 2284520
  have htrace : WordTrace (prefixWord ++ tailWord_2284520) baseStart_2284520 baseEnd_2284520 := by
    simpa [prefixWord, tailWord_2284520, baseEnd_2284520] using wordTrace_append hprefix tailTrace_2284520
  have hstable : (prefixWord ++ tailWord_2284520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284520).length < 2 ^ (prefixWord ++ tailWord_2284520).sum := by decide
  have hdescent : baseEnd_2284520 < baseStart_2284520 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284522 : List Nat := [3, 1, 3, 1, 2, 2, 3, 1, 1, 5]
def baseStart_2284522 : Nat := 118140960795 + 2284522 * 2 ^ 59
def prefixEnd_2284522 : Nat := 4983230072969 + 3 ^ 40 * 2284522 * 2
def baseEnd_2284522 : Nat := 782038567847210687245787

theorem tailTrace_2284522 : CollatzResearch.WordTrace tailWord_2284522 prefixEnd_2284522 782038567847210687245787 := by
  unfold tailWord_2284522
  simp only [CollatzResearch.WordTrace]
  refine ⟨20830840657393608535015955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55548908419716289426709213 20830840657393608535015955)
  ·
    refine ⟨31246260986090412802523933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20830840657393608535015955 31246260986090412802523933)
    ·
      refine ⟨11717347869783904800946475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31246260986090412802523933 11717347869783904800946475)
      ·
        refine ⟨17576021804675857201419713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11717347869783904800946475 17576021804675857201419713)
        ·
          refine ⟨13182016353506892901064785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17576021804675857201419713 13182016353506892901064785)
          ·
            refine ⟨9886512265130169675798589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13182016353506892901064785 9886512265130169675798589)
            ·
              refine ⟨3707442099423813628424471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9886512265130169675798589 3707442099423813628424471)
              ·
                refine ⟨5561163149135720442636707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3707442099423813628424471 5561163149135720442636707)
                ·
                  refine ⟨8341744723703580663955061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5561163149135720442636707 8341744723703580663955061)
                  ·
                    refine ⟨782038567847210687245787, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8341744723703580663955061 782038567847210687245787)
                    ·
                      rfl

theorem cell22_2284522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 2, 3, 1, 1, 5].length) (baseStart_2284522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284522 prefixEnd_2284522 := by exact prefixLift 2284522
  have htrace : WordTrace (prefixWord ++ tailWord_2284522) baseStart_2284522 baseEnd_2284522 := by
    simpa [prefixWord, tailWord_2284522, baseEnd_2284522] using wordTrace_append hprefix tailTrace_2284522
  have hstable : (prefixWord ++ tailWord_2284522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284522).length < 2 ^ (prefixWord ++ tailWord_2284522).sum := by decide
  have hdescent : baseEnd_2284522 < baseStart_2284522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284573 : List Nat := [1, 4, 2, 2, 3, 2, 2, 1, 2, 3]
def baseStart_2284573 : Nat := 118140960795 + 2284573 * 2 ^ 59
def prefixEnd_2284573 : Nat := 4983230072969 + 3 ^ 40 * 2284573 * 2
def baseEnd_2284573 : Nat := 782056026189463554220631

theorem tailTrace_2284573 : CollatzResearch.WordTrace tailWord_2284573 prefixEnd_2284573 782056026189463554220631 := by
  unfold tailWord_2284573
  simp only [CollatzResearch.WordTrace]
  refine ⟨83325222752389669850170373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55550148501593113233446915 83325222752389669850170373)
  ·
    refine ⟨15623479266073063096906945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83325222752389669850170373 15623479266073063096906945)
    ·
      refine ⟨11717609449554797322680209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15623479266073063096906945 11717609449554797322680209)
      ·
        refine ⟨8788207087166097992010157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11717609449554797322680209 8788207087166097992010157)
        ·
          refine ⟨3295577657687286747003809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8788207087166097992010157 3295577657687286747003809)
          ·
            refine ⟨2471683243265465060252857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3295577657687286747003809 2471683243265465060252857)
            ·
              refine ⟨1853762432449098795189643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2471683243265465060252857 1853762432449098795189643)
              ·
                refine ⟨2780643648673648192784465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1853762432449098795189643 2780643648673648192784465)
                ·
                  refine ⟨2085482736505236144588349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2780643648673648192784465 2085482736505236144588349)
                  ·
                    refine ⟨782056026189463554220631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2085482736505236144588349 782056026189463554220631)
                    ·
                      rfl

theorem cell22_2284573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 2, 1, 2, 3].length) (baseStart_2284573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284573 prefixEnd_2284573 := by exact prefixLift 2284573
  have htrace : WordTrace (prefixWord ++ tailWord_2284573) baseStart_2284573 baseEnd_2284573 := by
    simpa [prefixWord, tailWord_2284573, baseEnd_2284573] using wordTrace_append hprefix tailTrace_2284573
  have hstable : (prefixWord ++ tailWord_2284573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284573).length < 2 ^ (prefixWord ++ tailWord_2284573).sum := by decide
  have hdescent : baseEnd_2284573 < baseStart_2284573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284595 : List Nat := [1, 1, 1, 2, 4, 1, 1, 2, 4, 5]
def baseStart_2284595 : Nat := 118140960795 + 2284595 * 2 ^ 59
def prefixEnd_2284595 : Nat := 4983230072969 + 3 ^ 40 * 2284595 * 2
def baseEnd_2284595 : Nat := 782063557239062830170563

theorem tailTrace_2284595 : CollatzResearch.WordTrace tailWord_2284595 prefixEnd_2284595 782063557239062830170563 := by
  unfold tailWord_2284595
  simp only [CollatzResearch.WordTrace]
  refine ⟨83326025158309967607471239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55550683438873311738314159 83326025158309967607471239)
  ·
    refine ⟨124989037737464951411206859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83326025158309967607471239 124989037737464951411206859)
    ·
      refine ⟨187483556606197427116810289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 124989037737464951411206859 187483556606197427116810289)
      ·
        refine ⟨140612667454648070337607717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187483556606197427116810289 140612667454648070337607717)
        ·
          refine ⟨26364875147746513188301447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 140612667454648070337607717 26364875147746513188301447)
          ·
            refine ⟨39547312721619769782452171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26364875147746513188301447 39547312721619769782452171)
            ·
              refine ⟨59320969082429654673678257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39547312721619769782452171 59320969082429654673678257)
              ·
                refine ⟨44490726811822241005258693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59320969082429654673678257 44490726811822241005258693)
                ·
                  refine ⟨8342011277216670188486005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44490726811822241005258693 8342011277216670188486005)
                  ·
                    refine ⟨782063557239062830170563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8342011277216670188486005 782063557239062830170563)
                    ·
                      rfl

theorem cell22_2284595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 1, 2, 4, 5].length) (baseStart_2284595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284595 prefixEnd_2284595 := by exact prefixLift 2284595
  have htrace : WordTrace (prefixWord ++ tailWord_2284595) baseStart_2284595 baseEnd_2284595 := by
    simpa [prefixWord, tailWord_2284595, baseEnd_2284595] using wordTrace_append hprefix tailTrace_2284595
  have hstable : (prefixWord ++ tailWord_2284595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284595).length < 2 ^ (prefixWord ++ tailWord_2284595).sum := by decide
  have hdescent : baseEnd_2284595 < baseStart_2284595 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284672 : List Nat := [2, 1, 1, 2, 1, 3, 2, 4, 2, 4]
def baseStart_2284672 : Nat := 118140960795 + 2284672 * 2 ^ 59
def prefixEnd_2284672 : Nat := 4983230072969 + 3 ^ 40 * 2284672 * 2
def baseEnd_2284672 : Nat := 782089915912660295995327

theorem tailTrace_2284672 : CollatzResearch.WordTrace tailWord_2284672 prefixEnd_2284672 782089915912660295995327 := by
  unfold tailWord_2284672
  simp only [CollatzResearch.WordTrace]
  refine ⟨41664416789515504879012135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55552555719354006505349513 41664416789515504879012135)
  ·
    refine ⟨62496625184273257318518203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41664416789515504879012135 62496625184273257318518203)
    ·
      refine ⟨93744937776409885977777305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62496625184273257318518203 93744937776409885977777305)
      ·
        refine ⟨70308703332307414483332979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93744937776409885977777305 70308703332307414483332979)
        ·
          refine ⟨105463054998461121724999469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70308703332307414483332979 105463054998461121724999469)
          ·
            refine ⟨39548645624422920646874801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105463054998461121724999469 39548645624422920646874801)
            ·
              refine ⟨29661484218317190485156101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39548645624422920646874801 29661484218317190485156101)
              ·
                refine ⟨5561528290934473215966769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29661484218317190485156101 5561528290934473215966769)
                ·
                  refine ⟨4171146218200854911975077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5561528290934473215966769 4171146218200854911975077)
                  ·
                    refine ⟨782089915912660295995327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4171146218200854911975077 782089915912660295995327)
                    ·
                      rfl

theorem cell22_2284672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 4, 2, 4].length) (baseStart_2284672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284672 prefixEnd_2284672 := by exact prefixLift 2284672
  have htrace : WordTrace (prefixWord ++ tailWord_2284672) baseStart_2284672 baseEnd_2284672 := by
    simpa [prefixWord, tailWord_2284672, baseEnd_2284672] using wordTrace_append hprefix tailTrace_2284672
  have hstable : (prefixWord ++ tailWord_2284672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284672).length < 2 ^ (prefixWord ++ tailWord_2284672).sum := by decide
  have hdescent : baseEnd_2284672 < baseStart_2284672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284738 : List Nat := [3, 5, 1, 1, 2, 1, 2, 7]
def baseStart_2284738 : Nat := 118140960795 + 2284738 * 2 ^ 59
def prefixEnd_2284738 : Nat := 4983230072969 + 3 ^ 40 * 2284738 * 2
def baseEnd_2284738 : Nat := 86901389895717569316125

theorem tailTrace_2284738 : CollatzResearch.WordTrace tailWord_2284738 prefixEnd_2284738 86901389895717569316125 := by
  unfold tailWord_2284738
  simp only [CollatzResearch.WordTrace]
  refine ⟨20832810199197975757481717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55554160531194602019951245 20832810199197975757481717)
  ·
    refine ⟨1953075956174810227263911, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 20832810199197975757481717 1953075956174810227263911)
    ·
      refine ⟨2929613934262215340895867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1953075956174810227263911 2929613934262215340895867)
      ·
        refine ⟨4394420901393323011343801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2929613934262215340895867 4394420901393323011343801)
        ·
          refine ⟨3295815676044992258507851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4394420901393323011343801 3295815676044992258507851)
          ·
            refine ⟨4943723514067488387761777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3295815676044992258507851 4943723514067488387761777)
            ·
              refine ⟨3707792635550616290821333, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4943723514067488387761777 3707792635550616290821333)
              ·
                refine ⟨86901389895717569316125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3707792635550616290821333 86901389895717569316125)
                ·
                  rfl

theorem cell22_2284738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 2, 7].length) (baseStart_2284738 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284738 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284738 prefixEnd_2284738 := by exact prefixLift 2284738
  have htrace : WordTrace (prefixWord ++ tailWord_2284738) baseStart_2284738 baseEnd_2284738 := by
    simpa [prefixWord, tailWord_2284738, baseEnd_2284738] using wordTrace_append hprefix tailTrace_2284738
  have hstable : (prefixWord ++ tailWord_2284738).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284738).length < 2 ^ (prefixWord ++ tailWord_2284738).sum := by decide
  have hdescent : baseEnd_2284738 < baseStart_2284738 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284742 : List Nat := [6, 1, 2, 2, 1, 1, 1, 3, 2, 3]
def baseStart_2284742 : Nat := 118140960795 + 2284742 * 2 ^ 59
def prefixEnd_2284742 : Nat := 4983230072969 + 3 ^ 40 * 2284742 * 2
def baseEnd_2284742 : Nat := 782113878343203446745113

theorem tailTrace_2284742 : CollatzResearch.WordTrace tailWord_2284742 prefixEnd_2284742 782113878343203446745113 := by
  unfold tailWord_2284742
  simp only [CollatzResearch.WordTrace]
  refine ⟨2604105834024294116033515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55554257792518274475381653 2604105834024294116033515)
  ·
    refine ⟨3906158751036441174050273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2604105834024294116033515 3906158751036441174050273)
    ·
      refine ⟨2929619063277330880537705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3906158751036441174050273 2929619063277330880537705)
      ·
        refine ⟨2197214297457998160403279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2929619063277330880537705 2197214297457998160403279)
        ·
          refine ⟨3295821446186997240604919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2197214297457998160403279 3295821446186997240604919)
          ·
            refine ⟨4943732169280495860907379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3295821446186997240604919 4943732169280495860907379)
            ·
              refine ⟨7415598253920743791361069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4943732169280495860907379 7415598253920743791361069)
              ·
                refine ⟨2780849345220278921760401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7415598253920743791361069 2780849345220278921760401)
                ·
                  refine ⟨2085637008915209191320301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2780849345220278921760401 2085637008915209191320301)
                  ·
                    refine ⟨782113878343203446745113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2085637008915209191320301 782113878343203446745113)
                    ·
                      rfl

theorem cell22_2284742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 2, 1, 1, 1, 3, 2, 3].length) (baseStart_2284742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284742 prefixEnd_2284742 := by exact prefixLift 2284742
  have htrace : WordTrace (prefixWord ++ tailWord_2284742) baseStart_2284742 baseEnd_2284742 := by
    simpa [prefixWord, tailWord_2284742, baseEnd_2284742] using wordTrace_append hprefix tailTrace_2284742
  have hstable : (prefixWord ++ tailWord_2284742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284742).length < 2 ^ (prefixWord ++ tailWord_2284742).sum := by decide
  have hdescent : baseEnd_2284742 < baseStart_2284742 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284809 : List Nat := [1, 2, 1, 1, 3, 3, 4, 1, 1, 5]
def baseStart_2284809 : Nat := 118140960795 + 2284809 * 2 ^ 59
def prefixEnd_2284809 : Nat := 4983230072969 + 3 ^ 40 * 2284809 * 2
def baseEnd_2284809 : Nat := 782136813812437605319907

theorem tailTrace_2284809 : CollatzResearch.WordTrace tailWord_2284809 prefixEnd_2284809 782136813812437605319907 := by
  unfold tailWord_2284809
  simp only [CollatzResearch.WordTrace]
  refine ⟨83333830379534682155761481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55555886919689788103840987 83333830379534682155761481)
  ·
    refine ⟨62500372784651011616821111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83333830379534682155761481 62500372784651011616821111)
    ·
      refine ⟨93750559176976517425231667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62500372784651011616821111 93750559176976517425231667)
      ·
        refine ⟨140625838765464776137847501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93750559176976517425231667 140625838765464776137847501)
        ·
          refine ⟨52734689537049291051692813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140625838765464776137847501 52734689537049291051692813)
          ·
            refine ⟨19775508576393484144384805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52734689537049291051692813 19775508576393484144384805)
            ·
              refine ⟨3707907858073778277072151, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19775508576393484144384805 3707907858073778277072151)
              ·
                refine ⟨5561861787110667415608227, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3707907858073778277072151 5561861787110667415608227)
                ·
                  refine ⟨8342792680666001123412341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5561861787110667415608227 8342792680666001123412341)
                  ·
                    refine ⟨782136813812437605319907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8342792680666001123412341 782136813812437605319907)
                    ·
                      rfl

theorem cell22_2284809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 3, 4, 1, 1, 5].length) (baseStart_2284809 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284809 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284809 prefixEnd_2284809 := by exact prefixLift 2284809
  have htrace : WordTrace (prefixWord ++ tailWord_2284809) baseStart_2284809 baseEnd_2284809 := by
    simpa [prefixWord, tailWord_2284809, baseEnd_2284809] using wordTrace_append hprefix tailTrace_2284809
  have hstable : (prefixWord ++ tailWord_2284809).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284809).length < 2 ^ (prefixWord ++ tailWord_2284809).sum := by decide
  have hdescent : baseEnd_2284809 < baseStart_2284809 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284824 : List Nat := [2, 1, 2, 3, 1, 4, 1, 1, 1, 6]
def baseStart_2284824 : Nat := 118140960795 + 2284824 * 2 ^ 59
def prefixEnd_2284824 : Nat := 4983230072969 + 3 ^ 40 * 2284824 * 2
def baseEnd_2284824 : Nat := 782141948618982566194861

theorem tailTrace_2284824 : CollatzResearch.WordTrace tailWord_2284824 prefixEnd_2284824 782141948618982566194861 := by
  unfold tailWord_2284824
  simp only [CollatzResearch.WordTrace]
  refine ⟨41667188737240169858778763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55556251649653559811705017 41667188737240169858778763)
  ·
    refine ⟨62500783105860254788168145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41667188737240169858778763 62500783105860254788168145)
    ·
      refine ⟨46875587329395191091126109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62500783105860254788168145 46875587329395191091126109)
      ·
        refine ⟨17578345248523196659172291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46875587329395191091126109 17578345248523196659172291)
        ·
          refine ⟨26367517872784794988758437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17578345248523196659172291 26367517872784794988758437)
          ·
            refine ⟨4943909601147149060392207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26367517872784794988758437 4943909601147149060392207)
            ·
              refine ⟨7415864401720723590588311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4943909601147149060392207 7415864401720723590588311)
              ·
                refine ⟨11123796602581085385882467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7415864401720723590588311 11123796602581085385882467)
                ·
                  refine ⟨16685694903871628078823701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11123796602581085385882467 16685694903871628078823701)
                  ·
                    refine ⟨782141948618982566194861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16685694903871628078823701 782141948618982566194861)
                    ·
                      rfl

theorem cell22_2284824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 4, 1, 1, 1, 6].length) (baseStart_2284824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284824 prefixEnd_2284824 := by exact prefixLift 2284824
  have htrace : WordTrace (prefixWord ++ tailWord_2284824) baseStart_2284824 baseEnd_2284824 := by
    simpa [prefixWord, tailWord_2284824, baseEnd_2284824] using wordTrace_append hprefix tailTrace_2284824
  have hstable : (prefixWord ++ tailWord_2284824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284824).length < 2 ^ (prefixWord ++ tailWord_2284824).sum := by decide
  have hdescent : baseEnd_2284824 < baseStart_2284824 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284830 : List Nat := [4, 3, 2, 1, 2, 1, 1, 3, 1, 4]
def baseStart_2284830 : Nat := 118140960795 + 2284830 * 2 ^ 59
def prefixEnd_2284830 : Nat := 4983230072969 + 3 ^ 40 * 2284830 * 2
def baseEnd_2284830 : Nat := 782144002541600550544843

theorem tailTrace_2284830 : CollatzResearch.WordTrace tailWord_2284830 prefixEnd_2284830 782144002541600550544843 := by
  unfold tailWord_2284830
  simp only [CollatzResearch.WordTrace]
  refine ⟨10416824539057325342784493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55556397541639068494850629 10416824539057325342784493)
  ·
    refine ⟨3906309202146497003544185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10416824539057325342784493 3906309202146497003544185)
    ·
      refine ⟨2929731901609872752658139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3906309202146497003544185 2929731901609872752658139)
      ·
        refine ⟨4394597852414809128987209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2929731901609872752658139 4394597852414809128987209)
        ·
          refine ⟨3295948389311106846740407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4394597852414809128987209 3295948389311106846740407)
          ·
            refine ⟨4943922583966660270110611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3295948389311106846740407 4943922583966660270110611)
            ·
              refine ⟨7415883875949990405165917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4943922583966660270110611 7415883875949990405165917)
              ·
                refine ⟨2780956453481246401937219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7415883875949990405165917 2780956453481246401937219)
                ·
                  refine ⟨4171434680221869602905829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2780956453481246401937219 4171434680221869602905829)
                  ·
                    refine ⟨782144002541600550544843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4171434680221869602905829 782144002541600550544843)
                    ·
                      rfl

theorem cell22_2284830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 3, 1, 4].length) (baseStart_2284830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284830 prefixEnd_2284830 := by exact prefixLift 2284830
  have htrace : WordTrace (prefixWord ++ tailWord_2284830) baseStart_2284830 baseEnd_2284830 := by
    simpa [prefixWord, tailWord_2284830, baseEnd_2284830] using wordTrace_append hprefix tailTrace_2284830
  have hstable : (prefixWord ++ tailWord_2284830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284830).length < 2 ^ (prefixWord ++ tailWord_2284830).sum := by decide
  have hdescent : baseEnd_2284830 < baseStart_2284830 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284871 : List Nat := [1, 1, 4, 1, 2, 3, 2, 2, 3, 3]
def baseStart_2284871 : Nat := 118140960795 + 2284871 * 2 ^ 59
def prefixEnd_2284871 : Nat := 4983230072969 + 3 ^ 40 * 2284871 * 2
def baseEnd_2284871 : Nat := 782158037679490110269717

theorem tailTrace_2284871 : CollatzResearch.WordTrace tailWord_2284871 prefixEnd_2284871 782158037679490110269717 := by
  unfold tailWord_2284871
  simp only [CollatzResearch.WordTrace]
  refine ⟨83336091705310066744518467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55557394470206711163012311 83336091705310066744518467)
  ·
    refine ⟨125004137557965100116777701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83336091705310066744518467 125004137557965100116777701)
    ·
      refine ⟨23438275792118456271895819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125004137557965100116777701 23438275792118456271895819)
      ·
        refine ⟨35157413688177684407843729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23438275792118456271895819 35157413688177684407843729)
        ·
          refine ⟨26368060266133263305882797, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35157413688177684407843729 26368060266133263305882797)
          ·
            refine ⟨9888022599799973739706049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26368060266133263305882797 9888022599799973739706049)
            ·
              refine ⟨7416016949849980304779537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9888022599799973739706049 7416016949849980304779537)
              ·
                refine ⟨5562012712387485228584653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7416016949849980304779537 5562012712387485228584653)
                ·
                  refine ⟨2085754767145306960719245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5562012712387485228584653 2085754767145306960719245)
                  ·
                    refine ⟨782158037679490110269717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2085754767145306960719245 782158037679490110269717)
                    ·
                      rfl

theorem cell22_2284871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_2284871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284871 prefixEnd_2284871 := by exact prefixLift 2284871
  have htrace : WordTrace (prefixWord ++ tailWord_2284871) baseStart_2284871 baseEnd_2284871 := by
    simpa [prefixWord, tailWord_2284871, baseEnd_2284871] using wordTrace_append hprefix tailTrace_2284871
  have hstable : (prefixWord ++ tailWord_2284871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284871).length < 2 ^ (prefixWord ++ tailWord_2284871).sum := by decide
  have hdescent : baseEnd_2284871 < baseStart_2284871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284884 : List Nat := [2, 4, 1, 1, 2, 1, 1, 1, 9]
def baseStart_2284884 : Nat := 118140960795 + 2284884 * 2 ^ 59
def prefixEnd_2284884 : Nat := 4983230072969 + 3 ^ 40 * 2284884 * 2
def baseEnd_2284884 : Nat := 260720829281720803231559

theorem tailTrace_2284884 : CollatzResearch.WordTrace tailWord_2284884 prefixEnd_2284884 260720829281720803231559 := by
  unfold tailWord_2284884
  simp only [CollatzResearch.WordTrace]
  refine ⟨41668282927131484982370853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55557710569508646643161137 41668282927131484982370853)
  ·
    refine ⟨7812803048837153434194535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41668282927131484982370853 7812803048837153434194535)
    ·
      refine ⟨11719204573255730151291803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7812803048837153434194535 11719204573255730151291803)
      ·
        refine ⟨17578806859883595226937705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11719204573255730151291803 17578806859883595226937705)
        ·
          refine ⟨13184105144912696420203279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17578806859883595226937705 13184105144912696420203279)
          ·
            refine ⟨19776157717369044630304919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13184105144912696420203279 19776157717369044630304919)
            ·
              refine ⟨29664236576053566945457379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19776157717369044630304919 29664236576053566945457379)
              ·
                refine ⟨44496354864080350418186069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29664236576053566945457379 44496354864080350418186069)
                ·
                  refine ⟨260720829281720803231559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 44496354864080350418186069 260720829281720803231559)
                  ·
                    rfl

theorem cell22_2284884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 9].length) (baseStart_2284884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284884 prefixEnd_2284884 := by exact prefixLift 2284884
  have htrace : WordTrace (prefixWord ++ tailWord_2284884) baseStart_2284884 baseEnd_2284884 := by
    simpa [prefixWord, tailWord_2284884, baseEnd_2284884] using wordTrace_append hprefix tailTrace_2284884
  have hstable : (prefixWord ++ tailWord_2284884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284884).length < 2 ^ (prefixWord ++ tailWord_2284884).sum := by decide
  have hdescent : baseEnd_2284884 < baseStart_2284884 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284931 : List Nat := [1, 1, 1, 3, 5, 2, 1, 1, 3, 4]
def baseStart_2284931 : Nat := 118140960795 + 2284931 * 2 ^ 59
def prefixEnd_2284931 : Nat := 4983230072969 + 3 ^ 40 * 2284931 * 2
def baseEnd_2284931 : Nat := 782178576905669953769533

theorem tailTrace_2284931 : CollatzResearch.WordTrace tailWord_2284931 prefixEnd_2284931 782178576905669953769533 := by
  unfold tailWord_2284931
  simp only [CollatzResearch.WordTrace]
  refine ⟨83338280085092696991702647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55558853390061797994468431 83338280085092696991702647)
  ·
    refine ⟨125007420127639045487553971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83338280085092696991702647 125007420127639045487553971)
    ·
      refine ⟨187511130191458568231330957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125007420127639045487553971 187511130191458568231330957)
      ·
        refine ⟨70316673821796963086749109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187511130191458568231330957 70316673821796963086749109)
        ·
          refine ⟨6592188170793465289382729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 70316673821796963086749109 6592188170793465289382729)
          ·
            refine ⟨4944141128095098967037047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6592188170793465289382729 4944141128095098967037047)
            ·
              refine ⟨7416211692142648450555571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4944141128095098967037047 7416211692142648450555571)
              ·
                refine ⟨11124317538213972675833357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7416211692142648450555571 11124317538213972675833357)
                ·
                  refine ⟨4171619076830239753437509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11124317538213972675833357 4171619076830239753437509)
                  ·
                    refine ⟨782178576905669953769533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4171619076830239753437509 782178576905669953769533)
                    ·
                      rfl

theorem cell22_2284931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 1, 1, 3, 4].length) (baseStart_2284931 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284931 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284931 prefixEnd_2284931 := by exact prefixLift 2284931
  have htrace : WordTrace (prefixWord ++ tailWord_2284931) baseStart_2284931 baseEnd_2284931 := by
    simpa [prefixWord, tailWord_2284931, baseEnd_2284931] using wordTrace_append hprefix tailTrace_2284931
  have hstable : (prefixWord ++ tailWord_2284931).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284931).length < 2 ^ (prefixWord ++ tailWord_2284931).sum := by decide
  have hdescent : baseEnd_2284931 < baseStart_2284931 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2284956 : List Nat := [2, 2, 3, 4, 2, 1, 2, 2, 1, 3]
def baseStart_2284956 : Nat := 118140960795 + 2284956 * 2 ^ 59
def prefixEnd_2284956 : Nat := 4983230072969 + 3 ^ 40 * 2284956 * 2
def baseEnd_2284956 : Nat := 782187134916578221894457

theorem tailTrace_2284956 : CollatzResearch.WordTrace tailWord_2284956 prefixEnd_2284956 782187134916578221894457 := by
  unfold tailWord_2284956
  simp only [CollatzResearch.WordTrace]
  refine ⟨41669595955001063130681361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55559461273334750840908481 41669595955001063130681361)
  ·
    refine ⟨31252196966250797348011021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41669595955001063130681361 31252196966250797348011021)
    ·
      refine ⟨11719573862344049005504133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31252196966250797348011021 11719573862344049005504133)
      ·
        refine ⟨2197420099189509188532025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 11719573862344049005504133 2197420099189509188532025)
        ·
          refine ⟨1648065074392131891399019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2197420099189509188532025 1648065074392131891399019)
          ·
            refine ⟨2472097611588197837098529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1648065074392131891399019 2472097611588197837098529)
            ·
              refine ⟨1854073208691148377823897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2472097611588197837098529 1854073208691148377823897)
              ·
                refine ⟨1390554906518361283367923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1854073208691148377823897 1390554906518361283367923)
                ·
                  refine ⟨2085832359777541925051885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1390554906518361283367923 2085832359777541925051885)
                  ·
                    refine ⟨782187134916578221894457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2085832359777541925051885 782187134916578221894457)
                    ·
                      rfl

theorem cell22_2284956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 2, 1, 2, 2, 1, 3].length) (baseStart_2284956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2284956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2284956 prefixEnd_2284956 := by exact prefixLift 2284956
  have htrace : WordTrace (prefixWord ++ tailWord_2284956) baseStart_2284956 baseEnd_2284956 := by
    simpa [prefixWord, tailWord_2284956, baseEnd_2284956] using wordTrace_append hprefix tailTrace_2284956
  have hstable : (prefixWord ++ tailWord_2284956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2284956).length < 2 ^ (prefixWord ++ tailWord_2284956).sum := by decide
  have hdescent : baseEnd_2284956 < baseStart_2284956 := by decide
  rcases family_descends (prefixWord ++ tailWord_2284956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285012 : List Nat := [2, 4, 1, 2, 3, 2, 1, 2, 2, 3]
def baseStart_2285012 : Nat := 118140960795 + 2285012 * 2 ^ 59
def prefixEnd_2285012 : Nat := 4983230072969 + 3 ^ 40 * 2285012 * 2
def baseEnd_2285012 : Nat := 782206304861012742494285

theorem tailTrace_2285012 : CollatzResearch.WordTrace tailWord_2285012 prefixEnd_2285012 782206304861012742494285 := by
  unfold tailWord_2285012
  simp only [CollatzResearch.WordTrace]
  refine ⟨41670617198899623912700645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55560822931866165216934193 41670617198899623912700645)
  ·
    refine ⟨7813240724793679483631371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41670617198899623912700645 7813240724793679483631371)
    ·
      refine ⟨11719861087190519225447057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7813240724793679483631371 11719861087190519225447057)
      ·
        refine ⟨8789895815392889419085293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11719861087190519225447057 8789895815392889419085293)
        ·
          refine ⟨3296210930772333532156985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8789895815392889419085293 3296210930772333532156985)
          ·
            refine ⟨2472158198079250149117739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3296210930772333532156985 2472158198079250149117739)
            ·
              refine ⟨3708237297118875223676609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2472158198079250149117739 3708237297118875223676609)
              ·
                refine ⟨2781177972839156417757457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3708237297118875223676609 2781177972839156417757457)
                ·
                  refine ⟨2085883479629367313318093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2781177972839156417757457 2085883479629367313318093)
                  ·
                    refine ⟨782206304861012742494285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2085883479629367313318093 782206304861012742494285)
                    ·
                      rfl

theorem cell22_2285012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 2, 1, 2, 2, 3].length) (baseStart_2285012 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285012 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285012 prefixEnd_2285012 := by exact prefixLift 2285012
  have htrace : WordTrace (prefixWord ++ tailWord_2285012) baseStart_2285012 baseEnd_2285012 := by
    simpa [prefixWord, tailWord_2285012, baseEnd_2285012] using wordTrace_append hprefix tailTrace_2285012
  have hstable : (prefixWord ++ tailWord_2285012).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285012).length < 2 ^ (prefixWord ++ tailWord_2285012).sum := by decide
  have hdescent : baseEnd_2285012 < baseStart_2285012 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285023 : List Nat := [1, 1, 2, 3, 3, 1, 4, 1, 3, 3]
def baseStart_2285023 : Nat := 118140960795 + 2285023 * 2 ^ 59
def prefixEnd_2285023 : Nat := 4983230072969 + 3 ^ 40 * 2285023 * 2
def baseEnd_2285023 : Nat := 782210070385812380469251

theorem tailTrace_2285023 : CollatzResearch.WordTrace tailWord_2285023 prefixEnd_2285023 782210070385812380469251 := by
  unfold tailWord_2285023
  simp only [CollatzResearch.WordTrace]
  refine ⟨83341635600759396704051723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55561090400506264469367815 83341635600759396704051723)
  ·
    refine ⟨125012453401139095056077585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83341635600759396704051723 125012453401139095056077585)
    ·
      refine ⟨93759340050854321292058189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125012453401139095056077585 93759340050854321292058189)
      ·
        refine ⟨35159752519070370484521821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93759340050854321292058189 35159752519070370484521821)
        ·
          refine ⟨13184907194651388931695683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35159752519070370484521821 13184907194651388931695683)
          ·
            refine ⟨19777360791977083397543525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13184907194651388931695683 19777360791977083397543525)
            ·
              refine ⟨3708255148495703137039411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19777360791977083397543525 3708255148495703137039411)
              ·
                refine ⟨5562382722743554705559117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3708255148495703137039411 5562382722743554705559117)
                ·
                  refine ⟨2085893521028833014584669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5562382722743554705559117 2085893521028833014584669)
                  ·
                    refine ⟨782210070385812380469251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2085893521028833014584669 782210070385812380469251)
                    ·
                      rfl

theorem cell22_2285023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 4, 1, 3, 3].length) (baseStart_2285023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285023 prefixEnd_2285023 := by exact prefixLift 2285023
  have htrace : WordTrace (prefixWord ++ tailWord_2285023) baseStart_2285023 baseEnd_2285023 := by
    simpa [prefixWord, tailWord_2285023, baseEnd_2285023] using wordTrace_append hprefix tailTrace_2285023
  have hstable : (prefixWord ++ tailWord_2285023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285023).length < 2 ^ (prefixWord ++ tailWord_2285023).sum := by decide
  have hdescent : baseEnd_2285023 < baseStart_2285023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285113 : List Nat := [1, 2, 1, 5, 1, 3, 1, 2, 1, 5]
def baseStart_2285113 : Nat := 118140960795 + 2285113 * 2 ^ 59
def prefixEnd_2285113 : Nat := 4983230072969 + 3 ^ 40 * 2285113 * 2
def baseEnd_2285113 : Nat := 782240879225082145718975

theorem tailTrace_2285113 : CollatzResearch.WordTrace tailWord_2285113 prefixEnd_2285113 782240879225082145718975 := by
  unfold tailWord_2285113
  simp only [CollatzResearch.WordTrace]
  refine ⟨83344918170433342074827993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55563278780288894716551995 83344918170433342074827993)
  ·
    refine ⟨62508688627825006556120995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83344918170433342074827993 62508688627825006556120995)
    ·
      refine ⟨93763032941737509834181493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62508688627825006556120995 93763032941737509834181493)
      ·
        refine ⟨8790284338287891546954515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93763032941737509834181493 8790284338287891546954515)
        ·
          refine ⟨13185426507431837320431773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8790284338287891546954515 13185426507431837320431773)
          ·
            refine ⟨4944534940286938995161915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13185426507431837320431773 4944534940286938995161915)
            ·
              refine ⟨7416802410430408492742873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4944534940286938995161915 7416802410430408492742873)
              ·
                refine ⟨5562601807822806369557155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7416802410430408492742873 5562601807822806369557155)
                ·
                  refine ⟨8343902711734209554335733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5562601807822806369557155 8343902711734209554335733)
                  ·
                    refine ⟨782240879225082145718975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8343902711734209554335733 782240879225082145718975)
                    ·
                      rfl

theorem cell22_2285113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 3, 1, 2, 1, 5].length) (baseStart_2285113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285113 prefixEnd_2285113 := by exact prefixLift 2285113
  have htrace : WordTrace (prefixWord ++ tailWord_2285113) baseStart_2285113 baseEnd_2285113 := by
    simpa [prefixWord, tailWord_2285113, baseEnd_2285113] using wordTrace_append hprefix tailTrace_2285113
  have hstable : (prefixWord ++ tailWord_2285113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285113).length < 2 ^ (prefixWord ++ tailWord_2285113).sum := by decide
  have hdescent : baseEnd_2285113 < baseStart_2285113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285117 : List Nat := [1, 4, 1, 3, 3, 1, 3, 1, 1, 4]
def baseStart_2285117 : Nat := 118140960795 + 2285117 * 2 ^ 59
def prefixEnd_2285117 : Nat := 4983230072969 + 3 ^ 40 * 2285117 * 2
def baseEnd_2285117 : Nat := 782242248506827468618963

theorem tailTrace_2285117 : CollatzResearch.WordTrace tailWord_2285117 prefixEnd_2285117 782242248506827468618963 := by
  unfold tailWord_2285117
  simp only [CollatzResearch.WordTrace]
  refine ⟨83345064062418850757973605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55563376041612567171982403 83345064062418850757973605)
  ·
    refine ⟨15627199511703534517120051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83345064062418850757973605 15627199511703534517120051)
    ·
      refine ⟨23440799267555301775680077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15627199511703534517120051 23440799267555301775680077)
      ·
        refine ⟨8790299725333238165880029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23440799267555301775680077 8790299725333238165880029)
        ·
          refine ⟨3296362396999964312205011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8790299725333238165880029 3296362396999964312205011)
          ·
            refine ⟨4944543595499946468307517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3296362396999964312205011 4944543595499946468307517)
            ·
              refine ⟨1854203848312479925615319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4944543595499946468307517 1854203848312479925615319)
              ·
                refine ⟨2781305772468719888422979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1854203848312479925615319 2781305772468719888422979)
                ·
                  refine ⟨4171958658703079832634469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2781305772468719888422979 4171958658703079832634469)
                  ·
                    refine ⟨782242248506827468618963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4171958658703079832634469 782242248506827468618963)
                    ·
                      rfl

theorem cell22_2285117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 3, 1, 1, 4].length) (baseStart_2285117 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285117 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285117 prefixEnd_2285117 := by exact prefixLift 2285117
  have htrace : WordTrace (prefixWord ++ tailWord_2285117) baseStart_2285117 baseEnd_2285117 := by
    simpa [prefixWord, tailWord_2285117, baseEnd_2285117] using wordTrace_append hprefix tailTrace_2285117
  have hstable : (prefixWord ++ tailWord_2285117).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285117).length < 2 ^ (prefixWord ++ tailWord_2285117).sum := by decide
  have hdescent : baseEnd_2285117 < baseStart_2285117 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285130 : List Nat := [3, 1, 2, 1, 1, 3, 4, 2, 2, 3]
def baseStart_2285130 : Nat := 118140960795 + 2285130 * 2 ^ 59
def prefixEnd_2285130 : Nat := 4983230072969 + 3 ^ 40 * 2285130 * 2
def baseEnd_2285130 : Nat := 782246698672499768043923

theorem tailTrace_2285130 : CollatzResearch.WordTrace tailWord_2285130 prefixEnd_2285130 782246698672499768043923 := by
  unfold tailWord_2285130
  simp only [CollatzResearch.WordTrace]
  refine ⟨20836384552842938494549211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55563692140914502652131229 20836384552842938494549211)
  ·
    refine ⟨31254576829264407741823817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20836384552842938494549211 31254576829264407741823817)
    ·
      refine ⟨23440932621948305806367863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31254576829264407741823817 23440932621948305806367863)
      ·
        refine ⟨35161398932922458709551795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23440932621948305806367863 35161398932922458709551795)
        ·
          refine ⟨52742098399383688064327693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35161398932922458709551795 52742098399383688064327693)
          ·
            refine ⟨19778286899768883024122885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52742098399383688064327693 19778286899768883024122885)
            ·
              refine ⟨3708428793706665567023041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19778286899768883024122885 3708428793706665567023041)
              ·
                refine ⟨2781321595279999175267281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3708428793706665567023041 2781321595279999175267281)
                ·
                  refine ⟨2085991196459999381450461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2781321595279999175267281 2085991196459999381450461)
                  ·
                    refine ⟨782246698672499768043923, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2085991196459999381450461 782246698672499768043923)
                    ·
                      rfl

theorem cell22_2285130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 4, 2, 2, 3].length) (baseStart_2285130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285130 prefixEnd_2285130 := by exact prefixLift 2285130
  have htrace : WordTrace (prefixWord ++ tailWord_2285130) baseStart_2285130 baseEnd_2285130 := by
    simpa [prefixWord, tailWord_2285130, baseEnd_2285130] using wordTrace_append hprefix tailTrace_2285130
  have hstable : (prefixWord ++ tailWord_2285130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285130).length < 2 ^ (prefixWord ++ tailWord_2285130).sum := by decide
  have hdescent : baseEnd_2285130 < baseStart_2285130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285132 : List Nat := [2, 2, 1, 3, 1, 5, 2, 2, 4]
def baseStart_2285132 : Nat := 118140960795 + 2285132 * 2 ^ 59
def prefixEnd_2285132 : Nat := 4983230072969 + 3 ^ 40 * 2285132 * 2
def baseEnd_2285132 : Nat := 260749127771124143164639

theorem tailTrace_2285132 : CollatzResearch.WordTrace tailWord_2285132 prefixEnd_2285132 260749127771124143164639 := by
  unfold tailWord_2285132
  simp only [CollatzResearch.WordTrace]
  refine ⟨41672805578682254159884825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55563740771576338879846433 41672805578682254159884825)
  ·
    refine ⟨31254604184011690619913619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41672805578682254159884825 31254604184011690619913619)
    ·
      refine ⟨46881906276017535929870429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31254604184011690619913619 46881906276017535929870429)
      ·
        refine ⟨17580714853506575973701411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46881906276017535929870429 17580714853506575973701411)
        ·
          refine ⟨26371072280259863960552117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17580714853506575973701411 26371072280259863960552117)
          ·
            refine ⟨2472288026274362246301761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26371072280259863960552117 2472288026274362246301761)
            ·
              refine ⟨1854216019705771684726321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2472288026274362246301761 1854216019705771684726321)
              ·
                refine ⟨1390662014779328763544741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1854216019705771684726321 1390662014779328763544741)
                ·
                  refine ⟨260749127771124143164639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1390662014779328763544741 260749127771124143164639)
                  ·
                    rfl

theorem cell22_2285132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 5, 2, 2, 4].length) (baseStart_2285132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285132 prefixEnd_2285132 := by exact prefixLift 2285132
  have htrace : WordTrace (prefixWord ++ tailWord_2285132) baseStart_2285132 baseEnd_2285132 := by
    simpa [prefixWord, tailWord_2285132, baseEnd_2285132] using wordTrace_append hprefix tailTrace_2285132
  have hstable : (prefixWord ++ tailWord_2285132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285132).length < 2 ^ (prefixWord ++ tailWord_2285132).sum := by decide
  have hdescent : baseEnd_2285132 < baseStart_2285132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285141 : List Nat := [1, 3, 2, 2, 1, 1, 1, 2, 2, 7]
def baseStart_2285141 : Nat := 118140960795 + 2285141 * 2 ^ 59
def prefixEnd_2285141 : Nat := 4983230072969 + 3 ^ 40 * 2285141 * 2
def baseEnd_2285141 : Nat := 782250464197299406018889

theorem tailTrace_2285141 : CollatzResearch.WordTrace tailWord_2285141 prefixEnd_2285141 782250464197299406018889 := by
  unfold tailWord_2285141
  simp only [CollatzResearch.WordTrace]
  refine ⟨83345939414331902856847277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55563959609554601904564851 83345939414331902856847277)
  ·
    refine ⟨31254727280374463571317729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83345939414331902856847277 31254727280374463571317729)
    ·
      refine ⟨23441045460280847678488297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31254727280374463571317729 23441045460280847678488297)
      ·
        refine ⟨17580784095210635758866223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23441045460280847678488297 17580784095210635758866223)
        ·
          refine ⟨26371176142815953638299335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17580784095210635758866223 26371176142815953638299335)
          ·
            refine ⟨39556764214223930457449003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26371176142815953638299335 39556764214223930457449003)
            ·
              refine ⟨59335146321335895686173505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39556764214223930457449003 59335146321335895686173505)
              ·
                refine ⟨44501359741001921764630129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59335146321335895686173505 44501359741001921764630129)
                ·
                  refine ⟨33376019805751441323472597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44501359741001921764630129 33376019805751441323472597)
                  ·
                    refine ⟨782250464197299406018889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33376019805751441323472597 782250464197299406018889)
                    ·
                      rfl

theorem cell22_2285141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 1, 2, 2, 7].length) (baseStart_2285141 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285141 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285141 prefixEnd_2285141 := by exact prefixLift 2285141
  have htrace : WordTrace (prefixWord ++ tailWord_2285141) baseStart_2285141 baseEnd_2285141 := by
    simpa [prefixWord, tailWord_2285141, baseEnd_2285141] using wordTrace_append hprefix tailTrace_2285141
  have hstable : (prefixWord ++ tailWord_2285141).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285141).length < 2 ^ (prefixWord ++ tailWord_2285141).sum := by decide
  have hdescent : baseEnd_2285141 < baseStart_2285141 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285143 : List Nat := [1, 1, 3, 2, 2, 5, 1, 7]
def baseStart_2285143 : Nat := 118140960795 + 2285143 * 2 ^ 59
def prefixEnd_2285143 : Nat := 4983230072969 + 3 ^ 40 * 2285143 * 2
def baseEnd_2285143 : Nat := 86916794315352451940987

theorem tailTrace_2285143 : CollatzResearch.WordTrace tailWord_2285143 prefixEnd_2285143 86916794315352451940987 := by
  unfold tailWord_2285143
  simp only [CollatzResearch.WordTrace]
  refine ⟨83346012360324657198420083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55564008240216438132280055 83346012360324657198420083)
  ·
    refine ⟨125019018540486985797630125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83346012360324657198420083 125019018540486985797630125)
    ·
      refine ⟨46882131952682619674111297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125019018540486985797630125 46882131952682619674111297)
      ·
        refine ⟨35161598964511964755583473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46882131952682619674111297 35161598964511964755583473)
        ·
          refine ⟨26371199223383973566687605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35161598964511964755583473 26371199223383973566687605)
          ·
            refine ⟨2472299927192247521876963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 26371199223383973566687605 2472299927192247521876963)
            ·
              refine ⟨3708449890788371282815445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2472299927192247521876963 3708449890788371282815445)
              ·
                refine ⟨86916794315352451940987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3708449890788371282815445 86916794315352451940987)
                ·
                  rfl

theorem cell22_2285143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 7].length) (baseStart_2285143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285143 prefixEnd_2285143 := by exact prefixLift 2285143
  have htrace : WordTrace (prefixWord ++ tailWord_2285143) baseStart_2285143 baseEnd_2285143 := by
    simpa [prefixWord, tailWord_2285143, baseEnd_2285143] using wordTrace_append hprefix tailTrace_2285143
  have hstable : (prefixWord ++ tailWord_2285143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285143).length < 2 ^ (prefixWord ++ tailWord_2285143).sum := by decide
  have hdescent : baseEnd_2285143 < baseStart_2285143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285160 : List Nat := [2, 1, 4, 3, 1, 2, 3, 6]
def baseStart_2285160 : Nat := 118140960795 + 2285160 * 2 ^ 59
def prefixEnd_2285160 : Nat := 4983230072969 + 3 ^ 40 * 2285160 * 2
def baseEnd_2285160 : Nat := 86917440920621076643759

theorem tailTrace_2285160 : CollatzResearch.WordTrace tailWord_2285160 prefixEnd_2285160 86917440920621076643759 := by
  unfold tailWord_2285160
  simp only [CollatzResearch.WordTrace]
  refine ⟨41673316200631534550894467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55564421600842046067859289 41673316200631534550894467)
  ·
    refine ⟨62509974300947301826341701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41673316200631534550894467 62509974300947301826341701)
    ·
      refine ⟨11720620181427619092439069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62509974300947301826341701 11720620181427619092439069)
      ·
        refine ⟨4395232568035357159664651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11720620181427619092439069 4395232568035357159664651)
        ·
          refine ⟨6592848852053035739496977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4395232568035357159664651 6592848852053035739496977)
          ·
            refine ⟨4944636639039776804622733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6592848852053035739496977 4944636639039776804622733)
            ·
              refine ⟨1854238739639916301733525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4944636639039776804622733 1854238739639916301733525)
              ·
                refine ⟨86917440920621076643759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1854238739639916301733525 86917440920621076643759)
                ·
                  rfl

theorem cell22_2285160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 3, 6].length) (baseStart_2285160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285160 prefixEnd_2285160 := by exact prefixLift 2285160
  have htrace : WordTrace (prefixWord ++ tailWord_2285160) baseStart_2285160 baseEnd_2285160 := by
    simpa [prefixWord, tailWord_2285160, baseEnd_2285160] using wordTrace_append hprefix tailTrace_2285160
  have hstable : (prefixWord ++ tailWord_2285160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285160).length < 2 ^ (prefixWord ++ tailWord_2285160).sum := by decide
  have hdescent : baseEnd_2285160 < baseStart_2285160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285201 : List Nat := [1, 2, 2, 1, 1, 1, 1, 3, 2, 8]
def baseStart_2285201 : Nat := 118140960795 + 2285201 * 2 ^ 59
def prefixEnd_2285201 : Nat := 4983230072969 + 3 ^ 40 * 2285201 * 2
def baseEnd_2285201 : Nat := 782271003423479249518705

theorem tailTrace_2285201 : CollatzResearch.WordTrace tailWord_2285201 prefixEnd_2285201 782271003423479249518705 := by
  unfold tailWord_2285201
  simp only [CollatzResearch.WordTrace]
  refine ⟨83348127794114533104031457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55565418529409688736020971 83348127794114533104031457)
  ·
    refine ⟨62511095845585899828023593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83348127794114533104031457 62511095845585899828023593)
    ·
      refine ⟨46883321884189424871017695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62511095845585899828023593 46883321884189424871017695)
      ·
        refine ⟨70324982826284137306526543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46883321884189424871017695 70324982826284137306526543)
        ·
          refine ⟨105487474239426205959789815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70324982826284137306526543 105487474239426205959789815)
          ·
            refine ⟨158231211359139308939684723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105487474239426205959789815 158231211359139308939684723)
            ·
              refine ⟨237346817038708963409527085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 158231211359139308939684723 237346817038708963409527085)
              ·
                refine ⟨89005056389515861278572657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 237346817038708963409527085 89005056389515861278572657)
                ·
                  refine ⟨66753792292136895958929493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 89005056389515861278572657 66753792292136895958929493)
                  ·
                    refine ⟨782271003423479249518705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66753792292136895958929493 782271003423479249518705)
                    ·
                      rfl

theorem cell22_2285201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 8].length) (baseStart_2285201 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285201 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285201 prefixEnd_2285201 := by exact prefixLift 2285201
  have htrace : WordTrace (prefixWord ++ tailWord_2285201) baseStart_2285201 baseEnd_2285201 := by
    simpa [prefixWord, tailWord_2285201, baseEnd_2285201] using wordTrace_append hprefix tailTrace_2285201
  have hstable : (prefixWord ++ tailWord_2285201).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285201).length < 2 ^ (prefixWord ++ tailWord_2285201).sum := by decide
  have hdescent : baseEnd_2285201 < baseStart_2285201 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285308 : List Nat := [2, 2, 2, 1, 3, 1, 1, 1, 1, 8]
def baseStart_2285308 : Nat := 118140960795 + 2285308 * 2 ^ 59
def prefixEnd_2285308 : Nat := 4983230072969 + 3 ^ 40 * 2285308 * 2
def baseEnd_2285308 : Nat := 782307631710166637093377

theorem tailTrace_2285308 : CollatzResearch.WordTrace tailWord_2285308 prefixEnd_2285308 782307631710166637093377 := by
  unfold tailWord_2285308
  simp only [CollatzResearch.WordTrace]
  refine ⟨41676015202363445189088289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55568020269817926918784385 41676015202363445189088289)
  ·
    refine ⟨31257011401772583891816217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41676015202363445189088289 31257011401772583891816217)
    ·
      refine ⟨23442758551329437918862163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31257011401772583891816217 23442758551329437918862163)
      ·
        refine ⟨35164137826994156878293245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23442758551329437918862163 35164137826994156878293245)
        ·
          refine ⟨13186551685122808829359967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35164137826994156878293245 13186551685122808829359967)
          ·
            refine ⟨19779827527684213244039951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13186551685122808829359967 19779827527684213244039951)
            ·
              refine ⟨29669741291526319866059927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19779827527684213244039951 29669741291526319866059927)
              ·
                refine ⟨44504611937289479799089891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29669741291526319866059927 44504611937289479799089891)
                ·
                  refine ⟨66756917905934219698634837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44504611937289479799089891 66756917905934219698634837)
                  ·
                    refine ⟨782307631710166637093377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66756917905934219698634837 782307631710166637093377)
                    ·
                      rfl

theorem cell22_2285308_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 1, 1, 1, 8].length) (baseStart_2285308 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285308 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285308 prefixEnd_2285308 := by exact prefixLift 2285308
  have htrace : WordTrace (prefixWord ++ tailWord_2285308) baseStart_2285308 baseEnd_2285308 := by
    simpa [prefixWord, tailWord_2285308, baseEnd_2285308] using wordTrace_append hprefix tailTrace_2285308
  have hstable : (prefixWord ++ tailWord_2285308).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285308).length < 2 ^ (prefixWord ++ tailWord_2285308).sum := by decide
  have hdescent : baseEnd_2285308 < baseStart_2285308 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285308) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285318 : List Nat := [6, 2, 2, 1, 1, 1, 1, 2, 6]
def baseStart_2285318 : Nat := 118140960795 + 2285318 * 2 ^ 59
def prefixEnd_2285318 : Nat := 4983230072969 + 3 ^ 40 * 2285318 * 2
def baseEnd_2285318 : Nat := 260770351638176648114449

theorem tailTrace_2285318 : CollatzResearch.WordTrace tailWord_2285318 prefixEnd_2285318 260770351638176648114449 := by
  unfold tailWord_2285318
  simp only [CollatzResearch.WordTrace]
  refine ⟨2604762347959083190188769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55568263423127108057360405 2604762347959083190188769)
  ·
    refine ⟨1953571760969312392641577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 2604762347959083190188769 1953571760969312392641577)
    ·
      refine ⟨1465178820726984294481183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1953571760969312392641577 1465178820726984294481183)
      ·
        refine ⟨2197768231090476441721775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1465178820726984294481183 2197768231090476441721775)
        ·
          refine ⟨3296652346635714662582663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2197768231090476441721775 3296652346635714662582663)
          ·
            refine ⟨4944978519953571993873995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3296652346635714662582663 4944978519953571993873995)
            ·
              refine ⟨7417467779930357990810993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4944978519953571993873995 7417467779930357990810993)
              ·
                refine ⟨5563100834947768493108245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7417467779930357990810993 5563100834947768493108245)
                ·
                  refine ⟨260770351638176648114449, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5563100834947768493108245 260770351638176648114449)
                  ·
                    rfl

theorem cell22_2285318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 2, 6].length) (baseStart_2285318 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285318 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285318 prefixEnd_2285318 := by exact prefixLift 2285318
  have htrace : WordTrace (prefixWord ++ tailWord_2285318) baseStart_2285318 baseEnd_2285318 := by
    simpa [prefixWord, tailWord_2285318, baseEnd_2285318] using wordTrace_append hprefix tailTrace_2285318
  have hstable : (prefixWord ++ tailWord_2285318).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285318).length < 2 ^ (prefixWord ++ tailWord_2285318).sum := by decide
  have hdescent : baseEnd_2285318 < baseStart_2285318 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285344 : List Nat := [2, 1, 1, 5, 1, 1, 4, 3, 1, 3]
def baseStart_2285344 : Nat := 118140960795 + 2285344 * 2 ^ 59
def prefixEnd_2285344 : Nat := 4983230072969 + 3 ^ 40 * 2285344 * 2
def baseEnd_2285344 : Nat := 782319955245874543193267

theorem tailTrace_2285344 : CollatzResearch.WordTrace tailWord_2285344 prefixEnd_2285344 782319955245874543193267 := by
  unfold tailWord_2285344
  simp only [CollatzResearch.WordTrace]
  refine ⟨41676671716298234263243543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55568895621730979017658057 41676671716298234263243543)
  ·
    refine ⟨62515007574447351394865315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41676671716298234263243543 62515007574447351394865315)
    ·
      refine ⟨93772511361671027092297973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62515007574447351394865315 93772511361671027092297973)
      ·
        refine ⟨8791172940156658789902935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93772511361671027092297973 8791172940156658789902935)
        ·
          refine ⟨13186759410234988184854403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8791172940156658789902935 13186759410234988184854403)
          ·
            refine ⟨19780139115352482277281605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13186759410234988184854403 19780139115352482277281605)
            ·
              refine ⟨3708776084128590426990301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19780139115352482277281605 3708776084128590426990301)
              ·
                refine ⟨1390791031548221410121363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3708776084128590426990301 1390791031548221410121363)
                ·
                  refine ⟨2086186547322332115182045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1390791031548221410121363 2086186547322332115182045)
                  ·
                    refine ⟨782319955245874543193267, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2086186547322332115182045 782319955245874543193267)
                    ·
                      rfl

theorem cell22_2285344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 1, 4, 3, 1, 3].length) (baseStart_2285344 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285344 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285344 prefixEnd_2285344 := by exact prefixLift 2285344
  have htrace : WordTrace (prefixWord ++ tailWord_2285344) baseStart_2285344 baseEnd_2285344 := by
    simpa [prefixWord, tailWord_2285344, baseEnd_2285344] using wordTrace_append hprefix tailTrace_2285344
  have hstable : (prefixWord ++ tailWord_2285344).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285344).length < 2 ^ (prefixWord ++ tailWord_2285344).sum := by decide
  have hdescent : baseEnd_2285344 < baseStart_2285344 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285374 : List Nat := [4, 2, 1, 2, 2, 2, 3, 1, 5]
def baseStart_2285374 : Nat := 118140960795 + 2285374 * 2 ^ 59
def prefixEnd_2285374 : Nat := 4983230072969 + 3 ^ 40 * 2285374 * 2
def baseEnd_2285374 : Nat := 260776741619654821647725

theorem tailTrace_2285374 : CollatzResearch.WordTrace tailWord_2285374 prefixEnd_2285374 260776741619654821647725 := by
  unfold tailWord_2285374
  simp only [CollatzResearch.WordTrace]
  refine ⟨10419304702810972956259897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55569625081658522433386117 10419304702810972956259897)
  ·
    refine ⟨7814478527108229717194923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10419304702810972956259897 7814478527108229717194923)
    ·
      refine ⟨11721717790662344575792385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7814478527108229717194923 11721717790662344575792385)
      ·
        refine ⟨8791288342996758431844289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11721717790662344575792385 8791288342996758431844289)
        ·
          refine ⟨6593466257247568823883217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8791288342996758431844289 6593466257247568823883217)
          ·
            refine ⟨4945099692935676617912413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6593466257247568823883217 4945099692935676617912413)
            ·
              refine ⟨1854412384850878731717155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4945099692935676617912413 1854412384850878731717155)
              ·
                refine ⟨2781618577276318097575733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1854412384850878731717155 2781618577276318097575733)
                ·
                  refine ⟨260776741619654821647725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2781618577276318097575733 260776741619654821647725)
                  ·
                    rfl

theorem cell22_2285374_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 3, 1, 5].length) (baseStart_2285374 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285374 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285374 prefixEnd_2285374 := by exact prefixLift 2285374
  have htrace : WordTrace (prefixWord ++ tailWord_2285374) baseStart_2285374 baseEnd_2285374 := by
    simpa [prefixWord, tailWord_2285374, baseEnd_2285374] using wordTrace_append hprefix tailTrace_2285374
  have hstable : (prefixWord ++ tailWord_2285374).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285374).length < 2 ^ (prefixWord ++ tailWord_2285374).sum := by decide
  have hdescent : baseEnd_2285374 < baseStart_2285374 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285374) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285434 : List Nat := [3, 1, 1, 1, 1, 1, 8, 1, 2, 3]
def baseStart_2285434 : Nat := 118140960795 + 2285434 * 2 ^ 59
def prefixEnd_2285434 : Nat := 4983230072969 + 3 ^ 40 * 2285434 * 2
def baseEnd_2285434 : Nat := 782350764085144308442991

theorem tailTrace_2285434 : CollatzResearch.WordTrace tailWord_2285434 prefixEnd_2285434 782350764085144308442991 := by
  unfold tailWord_2285434
  simp only [CollatzResearch.WordTrace]
  refine ⟨20839156500567603474315839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55571084001513609264842237 20839156500567603474315839)
  ·
    refine ⟨31258734750851405211473759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20839156500567603474315839 31258734750851405211473759)
    ·
      refine ⟨46888102126277107817210639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31258734750851405211473759 46888102126277107817210639)
      ·
        refine ⟨70332153189415661725815959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46888102126277107817210639 70332153189415661725815959)
        ·
          refine ⟨105498229784123492588723939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70332153189415661725815959 105498229784123492588723939)
          ·
            refine ⟨158247344676185238883085909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 105498229784123492588723939 158247344676185238883085909)
            ·
              refine ⟨1854461070424045768161163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 158247344676185238883085909 1854461070424045768161163)
              ·
                refine ⟨2781691605636068652241745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1854461070424045768161163 2781691605636068652241745)
                ·
                  refine ⟨2086268704227051489181309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2781691605636068652241745 2086268704227051489181309)
                  ·
                    refine ⟨782350764085144308442991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2086268704227051489181309 782350764085144308442991)
                    ·
                      rfl

theorem cell22_2285434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 8, 1, 2, 3].length) (baseStart_2285434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285434 prefixEnd_2285434 := by exact prefixLift 2285434
  have htrace : WordTrace (prefixWord ++ tailWord_2285434) baseStart_2285434 baseEnd_2285434 := by
    simpa [prefixWord, tailWord_2285434, baseEnd_2285434] using wordTrace_append hprefix tailTrace_2285434
  have hstable : (prefixWord ++ tailWord_2285434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285434).length < 2 ^ (prefixWord ++ tailWord_2285434).sum := by decide
  have hdescent : baseEnd_2285434 < baseStart_2285434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285470 : List Nat := [4, 3, 1, 3, 1, 2, 2, 2, 4]
def baseStart_2285470 : Nat := 118140960795 + 2285470 * 2 ^ 59
def prefixEnd_2285470 : Nat := 4983230072969 + 3 ^ 40 * 2285470 * 2
def baseEnd_2285470 : Nat := 260787695873617404847627

theorem tailTrace_2285470 : CollatzResearch.WordTrace tailWord_2285470 prefixEnd_2285470 260787695873617404847627 := by
  unfold tailWord_2285470
  simp only [CollatzResearch.WordTrace]
  refine ⟨10419742378767499005696733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55571959353426661363715909 10419742378767499005696733)
  ·
    refine ⟨3907403392037812127136275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10419742378767499005696733 3907403392037812127136275)
    ·
      refine ⟨5861105088056718190704413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3907403392037812127136275 5861105088056718190704413)
      ·
        refine ⟨2197914408021269321514155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5861105088056718190704413 2197914408021269321514155)
        ·
          refine ⟨3296871612031903982271233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2197914408021269321514155 3296871612031903982271233)
          ·
            refine ⟨2472653709023927986703425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3296871612031903982271233 2472653709023927986703425)
            ·
              refine ⟨1854490281767945990027569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2472653709023927986703425 1854490281767945990027569)
              ·
                refine ⟨1390867711325959492520677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1854490281767945990027569 1390867711325959492520677)
                ·
                  refine ⟨260787695873617404847627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1390867711325959492520677 260787695873617404847627)
                  ·
                    rfl

theorem cell22_2285470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 2, 2, 2, 4].length) (baseStart_2285470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285470 prefixEnd_2285470 := by exact prefixLift 2285470
  have htrace : WordTrace (prefixWord ++ tailWord_2285470) baseStart_2285470 baseEnd_2285470 := by
    simpa [prefixWord, tailWord_2285470, baseEnd_2285470] using wordTrace_append hprefix tailTrace_2285470
  have hstable : (prefixWord ++ tailWord_2285470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285470).length < 2 ^ (prefixWord ++ tailWord_2285470).sum := by decide
  have hdescent : baseEnd_2285470 < baseStart_2285470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285552 : List Nat := [2, 1, 1, 1, 3, 2, 5, 1, 1, 5]
def baseStart_2285552 : Nat := 118140960795 + 2285552 * 2 ^ 59
def prefixEnd_2285552 : Nat := 4983230072969 + 3 ^ 40 * 2285552 * 2
def baseEnd_2285552 : Nat := 782391157896631333992629

theorem tailTrace_2285552 : CollatzResearch.WordTrace tailWord_2285552 prefixEnd_2285552 782391157896631333992629 := by
  unfold tailWord_2285552
  simp only [CollatzResearch.WordTrace]
  refine ⟨41680464907921460025029455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55573953210561946700039273 41680464907921460025029455)
  ·
    refine ⟨62520697361882190037544183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41680464907921460025029455 62520697361882190037544183)
    ·
      refine ⟨93781046042823285056316275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62520697361882190037544183 93781046042823285056316275)
      ·
        refine ⟨140671569064234927584474413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93781046042823285056316275 140671569064234927584474413)
        ·
          refine ⟨52751838399088097844177905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140671569064234927584474413 52751838399088097844177905)
          ·
            refine ⟨39563878799316073383133429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52751838399088097844177905 39563878799316073383133429)
            ·
              refine ⟨3709113637435881879668759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39563878799316073383133429 3709113637435881879668759)
              ·
                refine ⟨5563670456153822819503139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3709113637435881879668759 5563670456153822819503139)
                ·
                  refine ⟨8345505684230734229254709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5563670456153822819503139 8345505684230734229254709)
                  ·
                    refine ⟨782391157896631333992629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8345505684230734229254709 782391157896631333992629)
                    ·
                      rfl

theorem cell22_2285552_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 2, 5, 1, 1, 5].length) (baseStart_2285552 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285552 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285552 prefixEnd_2285552 := by exact prefixLift 2285552
  have htrace : WordTrace (prefixWord ++ tailWord_2285552) baseStart_2285552 baseEnd_2285552 := by
    simpa [prefixWord, tailWord_2285552, baseEnd_2285552] using wordTrace_append hprefix tailTrace_2285552
  have hstable : (prefixWord ++ tailWord_2285552).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285552).length < 2 ^ (prefixWord ++ tailWord_2285552).sum := by decide
  have hdescent : baseEnd_2285552 < baseStart_2285552 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285552) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285588 : List Nat := [2, 4, 3, 2, 1, 2, 1, 1, 6]
def baseStart_2285588 : Nat := 118140960795 + 2285588 * 2 ^ 59
def prefixEnd_2285588 : Nat := 4983230072969 + 3 ^ 40 * 2285588 * 2
def baseEnd_2285588 : Nat := 260801160477446413364173

theorem tailTrace_2285588 : CollatzResearch.WordTrace tailWord_2285588 prefixEnd_2285588 260801160477446413364173 := by
  unfold tailWord_2285588
  simp only [CollatzResearch.WordTrace]
  refine ⟨41681121421856249099184709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55574828562474998798912945 41681121421856249099184709)
  ·
    refine ⟨7815210266598046706097133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41681121421856249099184709 7815210266598046706097133)
    ·
      refine ⟨2930703849974267514786425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7815210266598046706097133 2930703849974267514786425)
      ·
        refine ⟨2198027887480700636089819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2930703849974267514786425 2198027887480700636089819)
        ·
          refine ⟨3297041831221050954134729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2198027887480700636089819 3297041831221050954134729)
          ·
            refine ⟨2472781373415788215601047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3297041831221050954134729 2472781373415788215601047)
            ·
              refine ⟨3709172060123682323401571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2472781373415788215601047 3709172060123682323401571)
              ·
                refine ⟨5563758090185523485102357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3709172060123682323401571 5563758090185523485102357)
                ·
                  refine ⟨260801160477446413364173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5563758090185523485102357 260801160477446413364173)
                  ·
                    rfl

theorem cell22_2285588_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 1, 6].length) (baseStart_2285588 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285588 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285588 prefixEnd_2285588 := by exact prefixLift 2285588
  have htrace : WordTrace (prefixWord ++ tailWord_2285588) baseStart_2285588 baseEnd_2285588 := by
    simpa [prefixWord, tailWord_2285588, baseEnd_2285588] using wordTrace_append hprefix tailTrace_2285588
  have hstable : (prefixWord ++ tailWord_2285588).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285588).length < 2 ^ (prefixWord ++ tailWord_2285588).sum := by decide
  have hdescent : baseEnd_2285588 < baseStart_2285588 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285588) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285642 : List Nat := [3, 1, 2, 1, 1, 2, 1, 4, 2, 5]
def baseStart_2285642 : Nat := 118140960795 + 2285642 * 2 ^ 59
def prefixEnd_2285642 : Nat := 4983230072969 + 3 ^ 40 * 2285642 * 2
def baseEnd_2285642 : Nat := 782421966735901099242353

theorem tailTrace_2285642 : CollatzResearch.WordTrace tailWord_2285642 prefixEnd_2285642 782421966735901099242353 := by
  unfold tailWord_2285642
  simp only [CollatzResearch.WordTrace]
  refine ⟨20841053096379216355208795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55576141590344576947223453 20841053096379216355208795)
  ·
    refine ⟨31261579644568824532813193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20841053096379216355208795 31261579644568824532813193)
    ·
      refine ⟨23446184733426618399609895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31261579644568824532813193 23446184733426618399609895)
      ·
        refine ⟨35169277100139927599414843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23446184733426618399609895 35169277100139927599414843)
        ·
          refine ⟨52753915650209891399122265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35169277100139927599414843 52753915650209891399122265)
          ·
            refine ⟨39565436737657418549341699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52753915650209891399122265 39565436737657418549341699)
            ·
              refine ⟨59348155106486127824012549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39565436737657418549341699 59348155106486127824012549)
              ·
                refine ⟨11127779082466148967002353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 59348155106486127824012549 11127779082466148967002353)
                ·
                  refine ⟨8345834311849611725251765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11127779082466148967002353 8345834311849611725251765)
                  ·
                    refine ⟨782421966735901099242353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8345834311849611725251765 782421966735901099242353)
                    ·
                      rfl

theorem cell22_2285642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_2285642 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285642 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285642 prefixEnd_2285642 := by exact prefixLift 2285642
  have htrace : WordTrace (prefixWord ++ tailWord_2285642) baseStart_2285642 baseEnd_2285642 := by
    simpa [prefixWord, tailWord_2285642, baseEnd_2285642] using wordTrace_append hprefix tailTrace_2285642
  have hstable : (prefixWord ++ tailWord_2285642).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285642).length < 2 ^ (prefixWord ++ tailWord_2285642).sum := by decide
  have hdescent : baseEnd_2285642 < baseStart_2285642 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285657 : List Nat := [1, 2, 1, 2, 2, 1, 3, 1, 5, 4]
def baseStart_2285657 : Nat := 118140960795 + 2285657 * 2 ^ 59
def prefixEnd_2285657 : Nat := 4983230072969 + 3 ^ 40 * 2285657 * 2
def baseEnd_2285657 : Nat := 782427101542446060117307

theorem tailTrace_2285657 : CollatzResearch.WordTrace tailWord_2285657 prefixEnd_2285657 782427101542446060117307 := by
  unfold tailWord_2285657
  simp only [CollatzResearch.WordTrace]
  refine ⟨83364759480462522982631225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55576506320308348655087483 83364759480462522982631225)
  ·
    refine ⟨62523569610346892236973419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83364759480462522982631225 62523569610346892236973419)
    ·
      refine ⟨93785354415520338355460129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62523569610346892236973419 93785354415520338355460129)
      ·
        refine ⟨70339015811640253766595097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93785354415520338355460129 70339015811640253766595097)
        ·
          refine ⟨52754261858730190324946323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70339015811640253766595097 52754261858730190324946323)
          ·
            refine ⟨79131392788095285487419485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52754261858730190324946323 79131392788095285487419485)
            ·
              refine ⟨29674272295535732057782307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79131392788095285487419485 29674272295535732057782307)
              ·
                refine ⟨44511408443303598086673461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29674272295535732057782307 44511408443303598086673461)
                ·
                  refine ⟨4172944541559712320625637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44511408443303598086673461 4172944541559712320625637)
                  ·
                    refine ⟨782427101542446060117307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4172944541559712320625637 782427101542446060117307)
                    ·
                      rfl

theorem cell22_2285657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 3, 1, 5, 4].length) (baseStart_2285657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285657 prefixEnd_2285657 := by exact prefixLift 2285657
  have htrace : WordTrace (prefixWord ++ tailWord_2285657) baseStart_2285657 baseEnd_2285657 := by
    simpa [prefixWord, tailWord_2285657, baseEnd_2285657] using wordTrace_append hprefix tailTrace_2285657
  have hstable : (prefixWord ++ tailWord_2285657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285657).length < 2 ^ (prefixWord ++ tailWord_2285657).sum := by decide
  have hdescent : baseEnd_2285657 < baseStart_2285657 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285661 : List Nat := [1, 4, 4, 1, 1, 1, 2, 3, 5]
def baseStart_2285661 : Nat := 118140960795 + 2285661 * 2 ^ 59
def prefixEnd_2285661 : Nat := 4983230072969 + 3 ^ 40 * 2285661 * 2
def baseEnd_2285661 : Nat := 260809490274730461005765

theorem tailTrace_2285661 : CollatzResearch.WordTrace tailWord_2285661 prefixEnd_2285661 260809490274730461005765 := by
  unfold tailWord_2285661
  simp only [CollatzResearch.WordTrace]
  refine ⟨83364905372448031665776837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55576603581632021110517891 83364905372448031665776837)
  ·
    refine ⟨15630919757334005937333157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83364905372448031665776837 15630919757334005937333157)
    ·
      refine ⟨2930797454500126113249967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15630919757334005937333157 2930797454500126113249967)
      ·
        refine ⟨4396196181750189169874951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2930797454500126113249967 4396196181750189169874951)
        ·
          refine ⟨6594294272625283754812427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4396196181750189169874951 6594294272625283754812427)
          ·
            refine ⟨9891441408937925632218641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6594294272625283754812427 9891441408937925632218641)
            ·
              refine ⟨7418581056703444224163981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9891441408937925632218641 7418581056703444224163981)
              ·
                refine ⟨2781967896263791584061493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7418581056703444224163981 2781967896263791584061493)
                ·
                  refine ⟨260809490274730461005765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2781967896263791584061493 260809490274730461005765)
                  ·
                    rfl

theorem cell22_2285661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_2285661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285661 prefixEnd_2285661 := by exact prefixLift 2285661
  have htrace : WordTrace (prefixWord ++ tailWord_2285661) baseStart_2285661 baseEnd_2285661 := by
    simpa [prefixWord, tailWord_2285661, baseEnd_2285661] using wordTrace_append hprefix tailTrace_2285661
  have hstable : (prefixWord ++ tailWord_2285661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285661).length < 2 ^ (prefixWord ++ tailWord_2285661).sum := by decide
  have hdescent : baseEnd_2285661 < baseStart_2285661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285706 : List Nat := [3, 1, 2, 3, 1, 2, 2, 4, 4]
def baseStart_2285706 : Nat := 118140960795 + 2285706 * 2 ^ 59
def prefixEnd_2285706 : Nat := 4983230072969 + 3 ^ 40 * 2285706 * 2
def baseEnd_2285706 : Nat := 260814625081275421880719

theorem tailTrace_2285706 : CollatzResearch.WordTrace tailWord_2285706 prefixEnd_2285706 260814625081275421880719 := by
  unfold tailWord_2285706
  simp only [CollatzResearch.WordTrace]
  refine ⟨20841636664321251087791243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55577697771523336234109981 20841636664321251087791243)
  ·
    refine ⟨31262454996481876631686865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20841636664321251087791243 31262454996481876631686865)
    ·
      refine ⟨23446841247361407473765149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31262454996481876631686865 23446841247361407473765149)
      ·
        refine ⟨8792565467760527802661931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23446841247361407473765149 8792565467760527802661931)
        ·
          refine ⟨13188848201640791703992897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8792565467760527802661931 13188848201640791703992897)
          ·
            refine ⟨9891636151230593777994673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13188848201640791703992897 9891636151230593777994673)
            ·
              refine ⟨7418727113422945333496005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9891636151230593777994673 7418727113422945333496005)
              ·
                refine ⟨1391011333766802250030501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7418727113422945333496005 1391011333766802250030501)
                ·
                  refine ⟨260814625081275421880719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1391011333766802250030501 260814625081275421880719)
                  ·
                    rfl

theorem cell22_2285706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4, 4].length) (baseStart_2285706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285706 prefixEnd_2285706 := by exact prefixLift 2285706
  have htrace : WordTrace (prefixWord ++ tailWord_2285706) baseStart_2285706 baseEnd_2285706 := by
    simpa [prefixWord, tailWord_2285706, baseEnd_2285706] using wordTrace_append hprefix tailTrace_2285706
  have hstable : (prefixWord ++ tailWord_2285706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285706).length < 2 ^ (prefixWord ++ tailWord_2285706).sum := by decide
  have hdescent : baseEnd_2285706 < baseStart_2285706 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285717 : List Nat := [1, 3, 2, 1, 1, 1, 4, 9]
def baseStart_2285717 : Nat := 118140960795 + 2285717 * 2 ^ 59
def prefixEnd_2285717 : Nat := 4983230072969 + 3 ^ 40 * 2285717 * 2
def baseEnd_2285717 : Nat := 86938626752069544846347

theorem tailTrace_2285717 : CollatzResearch.WordTrace tailWord_2285717 prefixEnd_2285717 86938626752069544846347 := by
  unfold tailWord_2285717
  simp only [CollatzResearch.WordTrace]
  refine ⟨83366947860245153229815405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55577965240163435486543603 83366947860245153229815405)
  ·
    refine ⟨31262605447591932461180777, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83366947860245153229815405 31262605447591932461180777)
    ·
      refine ⟨23446954085693949345885583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31262605447591932461180777 23446954085693949345885583)
      ·
        refine ⟨35170431128540924018828375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23446954085693949345885583 35170431128540924018828375)
        ·
          refine ⟨52755646692811386028242563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35170431128540924018828375 52755646692811386028242563)
          ·
            refine ⟨79133470039217079042363845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52755646692811386028242563 79133470039217079042363845)
            ·
              refine ⟨14837525632353202320443221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79133470039217079042363845 14837525632353202320443221)
              ·
                refine ⟨86938626752069544846347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14837525632353202320443221 86938626752069544846347)
                ·
                  rfl

theorem cell22_2285717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 9].length) (baseStart_2285717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285717 prefixEnd_2285717 := by exact prefixLift 2285717
  have htrace : WordTrace (prefixWord ++ tailWord_2285717) baseStart_2285717 baseEnd_2285717 := by
    simpa [prefixWord, tailWord_2285717, baseEnd_2285717] using wordTrace_append hprefix tailTrace_2285717
  have hstable : (prefixWord ++ tailWord_2285717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285717).length < 2 ^ (prefixWord ++ tailWord_2285717).sum := by decide
  have hdescent : baseEnd_2285717 < baseStart_2285717 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285747 : List Nat := [1, 1, 1, 2, 3, 2, 1, 2, 1, 8]
def baseStart_2285747 : Nat := 118140960795 + 2285747 * 2 ^ 59
def prefixEnd_2285747 : Nat := 4983230072969 + 3 ^ 40 * 2285747 * 2
def baseEnd_2285747 : Nat := 782457910381715825367031

theorem tailTrace_2285747 : CollatzResearch.WordTrace tailWord_2285747 prefixEnd_2285747 782457910381715825367031 := by
  unfold tailWord_2285747
  simp only [CollatzResearch.WordTrace]
  refine ⟨83368042050136468353407495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55578694700090978902271663 83368042050136468353407495)
  ·
    refine ⟨125052063075204702530111243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83368042050136468353407495 125052063075204702530111243)
    ·
      refine ⟨187578094612807053795166865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125052063075204702530111243 187578094612807053795166865)
      ·
        refine ⟨140683570959605290346375149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187578094612807053795166865 140683570959605290346375149)
        ·
          refine ⟨52756339109851983879890681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140683570959605290346375149 52756339109851983879890681)
          ·
            refine ⟨39567254332388987909918011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52756339109851983879890681 39567254332388987909918011)
            ·
              refine ⟨59350881498583481864877017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39567254332388987909918011 59350881498583481864877017)
              ·
                refine ⟨44513161123937611398657763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59350881498583481864877017 44513161123937611398657763)
                ·
                  refine ⟨66769741685906417097986645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 44513161123937611398657763 66769741685906417097986645)
                  ·
                    refine ⟨782457910381715825367031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66769741685906417097986645 782457910381715825367031)
                    ·
                      rfl

theorem cell22_2285747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 2, 1, 8].length) (baseStart_2285747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285747 prefixEnd_2285747 := by exact prefixLift 2285747
  have htrace : WordTrace (prefixWord ++ tailWord_2285747) baseStart_2285747 baseEnd_2285747 := by
    simpa [prefixWord, tailWord_2285747, baseEnd_2285747] using wordTrace_append hprefix tailTrace_2285747
  have hstable : (prefixWord ++ tailWord_2285747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285747).length < 2 ^ (prefixWord ++ tailWord_2285747).sum := by decide
  have hdescent : baseEnd_2285747 < baseStart_2285747 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285772 : List Nat := [2, 2, 1, 6, 1, 2, 2, 1, 2, 3]
def baseStart_2285772 : Nat := 118140960795 + 2285772 * 2 ^ 59
def prefixEnd_2285772 : Nat := 4983230072969 + 3 ^ 40 * 2285772 * 2
def baseEnd_2285772 : Nat := 782466468392624093491955

theorem tailTrace_2285772 : CollatzResearch.WordTrace tailWord_2285772 prefixEnd_2285772 782466468392624093491955 := by
  unfold tailWord_2285772
  simp only [CollatzResearch.WordTrace]
  refine ⟨41684476937522948811533785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55579302583363931748711713 41684476937522948811533785)
  ·
    refine ⟨31263357703142211608650339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41684476937522948811533785 31263357703142211608650339)
    ·
      refine ⟨46895036554713317412975509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31263357703142211608650339 46895036554713317412975509)
      ·
        refine ⟨2198204838502186753733227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 46895036554713317412975509 2198204838502186753733227)
        ·
          refine ⟨3297307257753280130599841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2198204838502186753733227 3297307257753280130599841)
          ·
            refine ⟨2472980443314960097949881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3297307257753280130599841 2472980443314960097949881)
            ·
              refine ⟨1854735332486220073462411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2472980443314960097949881 1854735332486220073462411)
              ·
                refine ⟨2782102998729330110193617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1854735332486220073462411 2782102998729330110193617)
                ·
                  refine ⟨2086577249046997582645213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2782102998729330110193617 2086577249046997582645213)
                  ·
                    refine ⟨782466468392624093491955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2086577249046997582645213 782466468392624093491955)
                    ·
                      rfl

theorem cell22_2285772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 2, 1, 2, 3].length) (baseStart_2285772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285772 prefixEnd_2285772 := by exact prefixLift 2285772
  have htrace : WordTrace (prefixWord ++ tailWord_2285772) baseStart_2285772 baseEnd_2285772 := by
    simpa [prefixWord, tailWord_2285772, baseEnd_2285772] using wordTrace_append hprefix tailTrace_2285772
  have hstable : (prefixWord ++ tailWord_2285772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285772).length < 2 ^ (prefixWord ++ tailWord_2285772).sum := by decide
  have hdescent : baseEnd_2285772 < baseStart_2285772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285856 : List Nat := [2, 1, 1, 5, 2, 1, 2, 2, 1, 5]
def baseStart_2285856 : Nat := 118140960795 + 2285856 * 2 ^ 59
def prefixEnd_2285856 : Nat := 4983230072969 + 3 ^ 40 * 2285856 * 2
def baseEnd_2285856 : Nat := 782495223309275874391697

theorem tailTrace_2285856 : CollatzResearch.WordTrace tailWord_2285856 prefixEnd_2285856 782495223309275874391697 := by
  unfold tailWord_2285856
  simp only [CollatzResearch.WordTrace]
  refine ⟨41686008803370789984562711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55581345071161053312750281 41686008803370789984562711)
  ·
    refine ⟨62529013205056184976844067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41686008803370789984562711 62529013205056184976844067)
    ·
      refine ⟨93793519807584277465266101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62529013205056184976844067 93793519807584277465266101)
      ·
        refine ⟨8793142481961026012368697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 93793519807584277465266101 8793142481961026012368697)
        ·
          refine ⟨6594856861470769509276523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8793142481961026012368697 6594856861470769509276523)
          ·
            refine ⟨9892285292206154263914785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6594856861470769509276523 9892285292206154263914785)
            ·
              refine ⟨7419213969154615697936089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9892285292206154263914785 7419213969154615697936089)
              ·
                refine ⟨5564410476865961773452067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7419213969154615697936089 5564410476865961773452067)
                ·
                  refine ⟨8346615715298942660178101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5564410476865961773452067 8346615715298942660178101)
                  ·
                    refine ⟨782495223309275874391697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8346615715298942660178101 782495223309275874391697)
                    ·
                      rfl

theorem cell22_2285856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 2, 1, 2, 2, 1, 5].length) (baseStart_2285856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285856 prefixEnd_2285856 := by exact prefixLift 2285856
  have htrace : WordTrace (prefixWord ++ tailWord_2285856) baseStart_2285856 baseEnd_2285856 := by
    simpa [prefixWord, tailWord_2285856, baseEnd_2285856] using wordTrace_append hprefix tailTrace_2285856
  have hstable : (prefixWord ++ tailWord_2285856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285856).length < 2 ^ (prefixWord ++ tailWord_2285856).sum := by decide
  have hdescent : baseEnd_2285856 < baseStart_2285856 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285858 : List Nat := [3, 3, 1, 1, 3, 1, 1, 5, 4]
def baseStart_2285858 : Nat := 118140960795 + 2285858 * 2 ^ 59
def prefixEnd_2285858 : Nat := 4983230072969 + 3 ^ 40 * 2285858 * 2
def baseEnd_2285858 : Nat := 260831969316716178613897

theorem tailTrace_2285858 : CollatzResearch.WordTrace tailWord_2285858 prefixEnd_2285858 260831969316716178613897 := by
  unfold tailWord_2285858
  simp only [CollatzResearch.WordTrace]
  refine ⟨20843022638183583577674557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55581393701822889540465485 20843022638183583577674557)
  ·
    refine ⟨7816133489318843841627959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20843022638183583577674557 7816133489318843841627959)
    ·
      refine ⟨11724200233978265762441939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7816133489318843841627959 11724200233978265762441939)
      ·
        refine ⟨17586300350967398643662909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11724200233978265762441939 17586300350967398643662909)
        ·
          refine ⟨6594862631612774491373591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17586300350967398643662909 6594862631612774491373591)
          ·
            refine ⟨9892293947419161737060387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6594862631612774491373591 9892293947419161737060387)
            ·
              refine ⟨14838440921128742605590581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9892293947419161737060387 14838440921128742605590581)
              ·
                refine ⟨1391103836355819619274117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14838440921128742605590581 1391103836355819619274117)
                ·
                  refine ⟨260831969316716178613897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1391103836355819619274117 260831969316716178613897)
                  ·
                    rfl

theorem cell22_2285858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 1, 1, 5, 4].length) (baseStart_2285858 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285858 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285858 prefixEnd_2285858 := by exact prefixLift 2285858
  have htrace : WordTrace (prefixWord ++ tailWord_2285858) baseStart_2285858 baseEnd_2285858 := by
    simpa [prefixWord, tailWord_2285858, baseEnd_2285858] using wordTrace_append hprefix tailTrace_2285858
  have hstable : (prefixWord ++ tailWord_2285858).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285858).length < 2 ^ (prefixWord ++ tailWord_2285858).sum := by decide
  have hdescent : baseEnd_2285858 < baseStart_2285858 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285860 : List Nat := [2, 3, 1, 3, 1, 4, 2, 1, 1, 4]
def baseStart_2285860 : Nat := 118140960795 + 2285860 * 2 ^ 59
def prefixEnd_2285860 : Nat := 4983230072969 + 3 ^ 40 * 2285860 * 2
def baseEnd_2285860 : Nat := 782496592591021197291685

theorem tailTrace_2285860 : CollatzResearch.WordTrace tailWord_2285860 prefixEnd_2285860 782496592591021197291685 := by
  unfold tailWord_2285860
  simp only [CollatzResearch.WordTrace]
  refine ⟨41686081749363544326135517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55581442332484725768180689 41686081749363544326135517)
  ·
    refine ⟨15632280656011329122300819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41686081749363544326135517 15632280656011329122300819)
    ·
      refine ⟨23448420984016993683451229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15632280656011329122300819 23448420984016993683451229)
      ·
        refine ⟨8793157869006372631294211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23448420984016993683451229 8793157869006372631294211)
        ·
          refine ⟨13189736803509558946941317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8793157869006372631294211 13189736803509558946941317)
          ·
            refine ⟨2473075650658042302551497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 13189736803509558946941317 2473075650658042302551497)
            ·
              refine ⟨1854806737993531726913623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2473075650658042302551497 1854806737993531726913623)
              ·
                refine ⟨2782210106990297590370435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1854806737993531726913623 2782210106990297590370435)
                ·
                  refine ⟨4173315160485446385555653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2782210106990297590370435 4173315160485446385555653)
                  ·
                    refine ⟨782496592591021197291685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4173315160485446385555653 782496592591021197291685)
                    ·
                      rfl

theorem cell22_2285860_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 4, 2, 1, 1, 4].length) (baseStart_2285860 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285860 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285860 prefixEnd_2285860 := by exact prefixLift 2285860
  have htrace : WordTrace (prefixWord ++ tailWord_2285860) baseStart_2285860 baseEnd_2285860 := by
    simpa [prefixWord, tailWord_2285860, baseEnd_2285860] using wordTrace_append hprefix tailTrace_2285860
  have hstable : (prefixWord ++ tailWord_2285860).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285860).length < 2 ^ (prefixWord ++ tailWord_2285860).sum := by decide
  have hdescent : baseEnd_2285860 < baseStart_2285860 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285860) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2285873 : List Nat := [1, 2, 2, 3, 4, 1, 1, 1, 4, 3]
def baseStart_2285873 : Nat := 118140960795 + 2285873 * 2 ^ 59
def prefixEnd_2285873 : Nat := 4983230072969 + 3 ^ 40 * 2285873 * 2
def baseEnd_2285873 : Nat := 782501042756693496716645

theorem tailTrace_2285873 : CollatzResearch.WordTrace tailWord_2285873 prefixEnd_2285873 782501042756693496716645 := by
  unfold tailWord_2285873
  simp only [CollatzResearch.WordTrace]
  refine ⟨83372637647679991872494273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55581758431786661248329515 83372637647679991872494273)
  ·
    refine ⟨62529478235759993904370705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83372637647679991872494273 62529478235759993904370705)
    ·
      refine ⟨46897108676819995428278029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62529478235759993904370705 46897108676819995428278029)
      ·
        refine ⟨17586415753807498285604261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46897108676819995428278029 17586415753807498285604261)
        ·
          refine ⟨3297452953838905928550799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17586415753807498285604261 3297452953838905928550799)
          ·
            refine ⟨4946179430758358892826199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3297452953838905928550799 4946179430758358892826199)
            ·
              refine ⟨7419269146137538339239299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4946179430758358892826199 7419269146137538339239299)
              ·
                refine ⟨11128903719206307508858949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7419269146137538339239299 11128903719206307508858949)
                ·
                  refine ⟨2086669447351182657911053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11128903719206307508858949 2086669447351182657911053)
                  ·
                    refine ⟨782501042756693496716645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2086669447351182657911053 782501042756693496716645)
                    ·
                      rfl

theorem cell22_2285873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 4, 1, 1, 1, 4, 3].length) (baseStart_2285873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2285873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2285873 prefixEnd_2285873 := by exact prefixLift 2285873
  have htrace : WordTrace (prefixWord ++ tailWord_2285873) baseStart_2285873 baseEnd_2285873 := by
    simpa [prefixWord, tailWord_2285873, baseEnd_2285873] using wordTrace_append hprefix tailTrace_2285873
  have hstable : (prefixWord ++ tailWord_2285873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2285873).length < 2 ^ (prefixWord ++ tailWord_2285873).sum := by decide
  have hdescent : baseEnd_2285873 < baseStart_2285873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2285873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286023 : List Nat := [1, 1, 4, 1, 1, 4, 3, 1, 2, 4]
def baseStart_2286023 : Nat := 118140960795 + 2286023 * 2 ^ 59
def prefixEnd_2286023 : Nat := 4983230072969 + 3 ^ 40 * 2286023 * 2
def baseEnd_2286023 : Nat := 782552390822143105466185

theorem tailTrace_2286023 : CollatzResearch.WordTrace tailWord_2286023 prefixEnd_2286023 782552390822143105466185 := by
  unfold tailWord_2286023
  simp only [CollatzResearch.WordTrace]
  refine ⟨83378108597136567490454723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55585405731424378326969815 83378108597136567490454723)
  ·
    refine ⟨125067162895704851235682085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83378108597136567490454723 125067162895704851235682085)
    ·
      refine ⟨23450093042944659606690391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125067162895704851235682085 23450093042944659606690391)
      ·
        refine ⟨35175139564416989410035587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23450093042944659606690391 35175139564416989410035587)
        ·
          refine ⟨52762709346625484115053381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35175139564416989410035587 52762709346625484115053381)
          ·
            refine ⟨9893008002492278271572509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52762709346625484115053381 9893008002492278271572509)
            ·
              refine ⟨3709878000934604351839691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9893008002492278271572509 3709878000934604351839691)
              ·
                refine ⟨5564817001401906527759537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3709878000934604351839691 5564817001401906527759537)
                ·
                  refine ⟨4173612751051429895819653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5564817001401906527759537 4173612751051429895819653)
                  ·
                    refine ⟨782552390822143105466185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4173612751051429895819653 782552390822143105466185)
                    ·
                      rfl

theorem cell22_2286023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_2286023 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286023 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286023 prefixEnd_2286023 := by exact prefixLift 2286023
  have htrace : WordTrace (prefixWord ++ tailWord_2286023) baseStart_2286023 baseEnd_2286023 := by
    simpa [prefixWord, tailWord_2286023, baseEnd_2286023] using wordTrace_append hprefix tailTrace_2286023
  have hstable : (prefixWord ++ tailWord_2286023).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286023).length < 2 ^ (prefixWord ++ tailWord_2286023).sum := by decide
  have hdescent : baseEnd_2286023 < baseStart_2286023 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286038 : List Nat := [5, 2, 1, 1, 1, 1, 11]
def baseStart_2286038 : Nat := 118140960795 + 2286038 * 2 ^ 59
def prefixEnd_2286038 : Nat := 4983230072969 + 3 ^ 40 * 2286038 * 2
def baseEnd_2286038 : Nat := 28983612060321780234857

theorem tailTrace_2286038 : CollatzResearch.WordTrace tailWord_2286038 prefixEnd_2286038 28983612060321780234857 := by
  unfold tailWord_2286038
  simp only [CollatzResearch.WordTrace]
  refine ⟨5211165980755139065765673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55585770461388150034833845 5211165980755139065765673)
  ·
    refine ⟨3908374485566354299324255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5211165980755139065765673 3908374485566354299324255)
    ·
      refine ⟨5862561728349531448986383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3908374485566354299324255 5862561728349531448986383)
      ·
        refine ⟨8793842592524297173479575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5862561728349531448986383 8793842592524297173479575)
        ·
          refine ⟨13190763888786445760219363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8793842592524297173479575 13190763888786445760219363)
          ·
            refine ⟨19786145833179668640329045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13190763888786445760219363 19786145833179668640329045)
            ·
              refine ⟨28983612060321780234857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19786145833179668640329045 28983612060321780234857)
              ·
                rfl

theorem cell22_2286038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 11].length) (baseStart_2286038 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286038 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286038 prefixEnd_2286038 := by exact prefixLift 2286038
  have htrace : WordTrace (prefixWord ++ tailWord_2286038) baseStart_2286038 baseEnd_2286038 := by
    simpa [prefixWord, tailWord_2286038, baseEnd_2286038] using wordTrace_append hprefix tailTrace_2286038
  have hstable : (prefixWord ++ tailWord_2286038).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286038).length < 2 ^ (prefixWord ++ tailWord_2286038).sum := by decide
  have hdescent : baseEnd_2286038 < baseStart_2286038 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286070 : List Nat := [5, 1, 1, 1, 2, 1, 1, 4, 3, 3]
def baseStart_2286070 : Nat := 118140960795 + 2286070 * 2 ^ 59
def prefixEnd_2286070 : Nat := 4983230072969 + 3 ^ 40 * 2286070 * 2
def baseEnd_2286070 : Nat := 782568479882650649541041

theorem tailTrace_2286070 : CollatzResearch.WordTrace tailWord_2286070 prefixEnd_2286070 782568479882650649541041 := by
  unfold tailWord_2286070
  simp only [CollatzResearch.WordTrace]
  refine ⟨5211238926747893407338479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55586548551977529678277109 5211238926747893407338479)
  ·
    refine ⟨7816858390121840111007719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5211238926747893407338479 7816858390121840111007719)
    ·
      refine ⟨11725287585182760166511579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7816858390121840111007719 11725287585182760166511579)
      ·
        refine ⟨17587931377774140249767369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11725287585182760166511579 17587931377774140249767369)
        ·
          refine ⟨13190948533330605187325527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17587931377774140249767369 13190948533330605187325527)
          ·
            refine ⟨19786422799995907780988291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13190948533330605187325527 19786422799995907780988291)
            ·
              refine ⟨29679634199993861671482437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19786422799995907780988291 29679634199993861671482437)
              ·
                refine ⟨5564931412498849063402957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29679634199993861671482437 5564931412498849063402957)
                ·
                  refine ⟨2086849279687068398776109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5564931412498849063402957 2086849279687068398776109)
                  ·
                    refine ⟨782568479882650649541041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2086849279687068398776109 782568479882650649541041)
                    ·
                      rfl

theorem cell22_2286070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_2286070 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286070 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286070 prefixEnd_2286070 := by exact prefixLift 2286070
  have htrace : WordTrace (prefixWord ++ tailWord_2286070) baseStart_2286070 baseEnd_2286070 := by
    simpa [prefixWord, tailWord_2286070, baseEnd_2286070] using wordTrace_append hprefix tailTrace_2286070
  have hstable : (prefixWord ++ tailWord_2286070).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286070).length < 2 ^ (prefixWord ++ tailWord_2286070).sum := by decide
  have hdescent : baseEnd_2286070 < baseStart_2286070 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286100 : List Nat := [2, 4, 3, 1, 1, 1, 2, 1, 7]
def baseStart_2286100 : Nat := 118140960795 + 2286100 * 2 ^ 59
def prefixEnd_2286100 : Nat := 4983230072969 + 3 ^ 40 * 2286100 * 2
def baseEnd_2286100 : Nat := 260859583165246857096983

theorem tailTrace_2286100 : CollatzResearch.WordTrace tailWord_2286100 prefixEnd_2286100 260859583165246857096983 := by
  unfold tailWord_2286100
  simp only [CollatzResearch.WordTrace]
  refine ⟨41690458508928804820503877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55587278011905073094005169 41690458508928804820503877)
  ·
    refine ⟨7816960970424150903844477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41690458508928804820503877 7816960970424150903844477)
    ·
      refine ⟨2931360363909056588941679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7816960970424150903844477 2931360363909056588941679)
      ·
        refine ⟨4397040545863584883412519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2931360363909056588941679 4397040545863584883412519)
        ·
          refine ⟨6595560818795377325118779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4397040545863584883412519 6595560818795377325118779)
          ·
            refine ⟨9893341228193065987678169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6595560818795377325118779 9893341228193065987678169)
            ·
              refine ⟨7420005921144799490758627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9893341228193065987678169 7420005921144799490758627)
              ·
                refine ⟨11130008881717199236137941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7420005921144799490758627 11130008881717199236137941)
                ·
                  refine ⟨260859583165246857096983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11130008881717199236137941 260859583165246857096983)
                  ·
                    rfl

theorem cell22_2286100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 2, 1, 7].length) (baseStart_2286100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286100 prefixEnd_2286100 := by exact prefixLift 2286100
  have htrace : WordTrace (prefixWord ++ tailWord_2286100) baseStart_2286100 baseEnd_2286100 := by
    simpa [prefixWord, tailWord_2286100, baseEnd_2286100] using wordTrace_append hprefix tailTrace_2286100
  have hstable : (prefixWord ++ tailWord_2286100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286100).length < 2 ^ (prefixWord ++ tailWord_2286100).sum := by decide
  have hdescent : baseEnd_2286100 < baseStart_2286100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286104 : List Nat := [2, 1, 2, 3, 3, 2, 3, 2, 1, 3]
def baseStart_2286104 : Nat := 118140960795 + 2286104 * 2 ^ 59
def prefixEnd_2286104 : Nat := 4983230072969 + 3 ^ 40 * 2286104 * 2
def baseEnd_2286104 : Nat := 782580118777485894190937

theorem tailTrace_2286104 : CollatzResearch.WordTrace tailWord_2286104 prefixEnd_2286104 782580118777485894190937 := by
  unfold tailWord_2286104
  simp only [CollatzResearch.WordTrace]
  refine ⟨41690531454921559162076683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55587375273228745549435577 41690531454921559162076683)
  ·
    refine ⟨62535797182382338743115025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41690531454921559162076683 62535797182382338743115025)
    ·
      refine ⟨46901847886786754057336269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62535797182382338743115025 46901847886786754057336269)
      ·
        refine ⟨17588192957545032771501101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46901847886786754057336269 17588192957545032771501101)
        ·
          refine ⟨6595572359079387289312913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17588192957545032771501101 6595572359079387289312913)
          ·
            refine ⟨4946679269309540466984685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6595572359079387289312913 4946679269309540466984685)
            ·
              refine ⟨1855004725991077675119257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4946679269309540466984685 1855004725991077675119257)
              ·
                refine ⟨1391253544493308256339443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1855004725991077675119257 1391253544493308256339443)
                ·
                  refine ⟨2086880316739962384509165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1391253544493308256339443 2086880316739962384509165)
                  ·
                    refine ⟨782580118777485894190937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2086880316739962384509165 782580118777485894190937)
                    ·
                      rfl

theorem cell22_2286104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 3, 2, 1, 3].length) (baseStart_2286104 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286104 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286104 prefixEnd_2286104 := by exact prefixLift 2286104
  have htrace : WordTrace (prefixWord ++ tailWord_2286104) baseStart_2286104 baseEnd_2286104 := by
    simpa [prefixWord, tailWord_2286104, baseEnd_2286104] using wordTrace_append hprefix tailTrace_2286104
  have hstable : (prefixWord ++ tailWord_2286104).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286104).length < 2 ^ (prefixWord ++ tailWord_2286104).sum := by decide
  have hdescent : baseEnd_2286104 < baseStart_2286104 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286113 : List Nat := [1, 2, 3, 2, 2, 1, 2, 2, 3, 4]
def baseStart_2286113 : Nat := 118140960795 + 2286113 * 2 ^ 59
def prefixEnd_2286113 : Nat := 4983230072969 + 3 ^ 40 * 2286113 * 2
def baseEnd_2286113 : Nat := 782583199661412870715909

theorem tailTrace_2286113 : CollatzResearch.WordTrace tailWord_2286113 prefixEnd_2286113 782583199661412870715909 := by
  unfold tailWord_2286113
  simp only [CollatzResearch.WordTrace]
  refine ⟨83381391166810512861230993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55587594111207008574153995 83381391166810512861230993)
  ·
    refine ⟨62536043375107884645923245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83381391166810512861230993 62536043375107884645923245)
    ·
      refine ⟨23451016265665456742221217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62536043375107884645923245 23451016265665456742221217)
      ·
        refine ⟨17588262199249092556665913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23451016265665456742221217 17588262199249092556665913)
        ·
          refine ⟨13191196649436819417499435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17588262199249092556665913 13191196649436819417499435)
          ·
            refine ⟨19786794974155229126249153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13191196649436819417499435 19786794974155229126249153)
            ·
              refine ⟨14840096230616421844686865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19786794974155229126249153 14840096230616421844686865)
              ·
                refine ⟨11130072172962316383515149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14840096230616421844686865 11130072172962316383515149)
                ·
                  refine ⟨4173777064860868643818181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11130072172962316383515149 4173777064860868643818181)
                  ·
                    refine ⟨782583199661412870715909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4173777064860868643818181 782583199661412870715909)
                    ·
                      rfl

theorem cell22_2286113_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 1, 2, 2, 3, 4].length) (baseStart_2286113 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286113 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286113 prefixEnd_2286113 := by exact prefixLift 2286113
  have htrace : WordTrace (prefixWord ++ tailWord_2286113) baseStart_2286113 baseEnd_2286113 := by
    simpa [prefixWord, tailWord_2286113, baseEnd_2286113] using wordTrace_append hprefix tailTrace_2286113
  have hstable : (prefixWord ++ tailWord_2286113).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286113).length < 2 ^ (prefixWord ++ tailWord_2286113).sum := by decide
  have hdescent : baseEnd_2286113 < baseStart_2286113 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286113) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286130 : List Nat := [3, 2, 1, 1, 2, 1, 5, 2, 1, 4]
def baseStart_2286130 : Nat := 118140960795 + 2286130 * 2 ^ 59
def prefixEnd_2286130 : Nat := 4983230072969 + 3 ^ 40 * 2286130 * 2
def baseEnd_2286130 : Nat := 782589019108830493040857

theorem tailTrace_2286130 : CollatzResearch.WordTrace tailWord_2286130 prefixEnd_2286130 782589019108830493040857 := by
  unfold tailWord_2286130
  simp only [CollatzResearch.WordTrace]
  refine ⟨20845502801937231191149961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55588007471832616509733229 20845502801937231191149961)
  ·
    refine ⟨15634127101452923393362471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20845502801937231191149961 15634127101452923393362471)
    ·
      refine ⟨23451190652179385090043707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15634127101452923393362471 23451190652179385090043707)
      ·
        refine ⟨35176785978269077635065561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23451190652179385090043707 35176785978269077635065561)
        ·
          refine ⟨26382589483701808226299171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35176785978269077635065561 26382589483701808226299171)
          ·
            refine ⟨39573884225552712339448757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26382589483701808226299171 39573884225552712339448757)
            ·
              refine ⟨3710051646145566781823321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39573884225552712339448757 3710051646145566781823321)
              ·
                refine ⟨2782538734609175086367491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3710051646145566781823321 2782538734609175086367491)
                ·
                  refine ⟨4173808101913762629551237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2782538734609175086367491 4173808101913762629551237)
                  ·
                    refine ⟨782589019108830493040857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4173808101913762629551237 782589019108830493040857)
                    ·
                      rfl

theorem cell22_2286130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 5, 2, 1, 4].length) (baseStart_2286130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286130 prefixEnd_2286130 := by exact prefixLift 2286130
  have htrace : WordTrace (prefixWord ++ tailWord_2286130) baseStart_2286130 baseEnd_2286130 := by
    simpa [prefixWord, tailWord_2286130, baseEnd_2286130] using wordTrace_append hprefix tailTrace_2286130
  have hstable : (prefixWord ++ tailWord_2286130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286130).length < 2 ^ (prefixWord ++ tailWord_2286130).sum := by decide
  have hdescent : baseEnd_2286130 < baseStart_2286130 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286143 : List Nat := [1, 1, 2, 2, 3, 2, 3, 2, 1, 5]
def baseStart_2286143 : Nat := 118140960795 + 2286143 * 2 ^ 59
def prefixEnd_2286143 : Nat := 4983230072969 + 3 ^ 40 * 2286143 * 2
def baseEnd_2286143 : Nat := 782593469274502792465817

theorem tailTrace_2286143 : CollatzResearch.WordTrace tailWord_2286143 prefixEnd_2286143 782593469274502792465817 := by
  unfold tailWord_2286143
  simp only [CollatzResearch.WordTrace]
  refine ⟨83382485356701827984823083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55588323571134551989882055 83382485356701827984823083)
  ·
    refine ⟨125073728035052741977234625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83382485356701827984823083 125073728035052741977234625)
    ·
      refine ⟨93805296026289556482925969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125073728035052741977234625 93805296026289556482925969)
      ·
        refine ⟨70353972019717167362194477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93805296026289556482925969 70353972019717167362194477)
        ·
          refine ⟨26382739507393937760822929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70353972019717167362194477 26382739507393937760822929)
          ·
            refine ⟨19787054630545453320617197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26382739507393937760822929 19787054630545453320617197)
            ·
              refine ⟨7420145486454544995231449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19787054630545453320617197 7420145486454544995231449)
              ·
                refine ⟨5565109114840908746423587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7420145486454544995231449 5565109114840908746423587)
                ·
                  refine ⟨8347663672261363119635381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5565109114840908746423587 8347663672261363119635381)
                  ·
                    refine ⟨782593469274502792465817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8347663672261363119635381 782593469274502792465817)
                    ·
                      rfl

theorem cell22_2286143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 2, 3, 2, 1, 5].length) (baseStart_2286143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286143 prefixEnd_2286143 := by exact prefixLift 2286143
  have htrace : WordTrace (prefixWord ++ tailWord_2286143) baseStart_2286143 baseEnd_2286143 := by
    simpa [prefixWord, tailWord_2286143, baseEnd_2286143] using wordTrace_append hprefix tailTrace_2286143
  have hstable : (prefixWord ++ tailWord_2286143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286143).length < 2 ^ (prefixWord ++ tailWord_2286143).sum := by decide
  have hdescent : baseEnd_2286143 < baseStart_2286143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286192 : List Nat := [2, 1, 1, 1, 7, 2, 1, 1, 2, 4]
def baseStart_2286192 : Nat := 118140960795 + 2286192 * 2 ^ 59
def prefixEnd_2286192 : Nat := 4983230072969 + 3 ^ 40 * 2286192 * 2
def baseEnd_2286192 : Nat := 782610242975882997990667

theorem tailTrace_2286192 : CollatzResearch.WordTrace tailWord_2286192 prefixEnd_2286192 782610242975882997990667 := by
  unfold tailWord_2286192
  simp only [CollatzResearch.WordTrace]
  refine ⟨41692136266762154676678415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55589515022349539568904553 41692136266762154676678415)
  ·
    refine ⟨62538204400143232015017623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41692136266762154676678415 62538204400143232015017623)
    ·
      refine ⟨93807306600214848022526435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62538204400143232015017623 93807306600214848022526435)
      ·
        refine ⟨140710959900322272033789653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93807306600214848022526435 140710959900322272033789653)
        ·
          refine ⟨3297913122663803250791945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 140710959900322272033789653 3297913122663803250791945)
          ·
            refine ⟨2473434841997852438093959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3297913122663803250791945 2473434841997852438093959)
            ·
              refine ⟨3710152262996778657140939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2473434841997852438093959 3710152262996778657140939)
              ·
                refine ⟨5565228394495167985711409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3710152262996778657140939 5565228394495167985711409)
                ·
                  refine ⟨4173921295871375989283557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5565228394495167985711409 4173921295871375989283557)
                  ·
                    refine ⟨782610242975882997990667, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4173921295871375989283557 782610242975882997990667)
                    ·
                      rfl

theorem cell22_2286192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 1, 2, 4].length) (baseStart_2286192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286192 prefixEnd_2286192 := by exact prefixLift 2286192
  have htrace : WordTrace (prefixWord ++ tailWord_2286192) baseStart_2286192 baseEnd_2286192 := by
    simpa [prefixWord, tailWord_2286192, baseEnd_2286192] using wordTrace_append hprefix tailTrace_2286192
  have hstable : (prefixWord ++ tailWord_2286192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286192).length < 2 ^ (prefixWord ++ tailWord_2286192).sum := by decide
  have hdescent : baseEnd_2286192 < baseStart_2286192 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286222 : List Nat := [4, 1, 1, 3, 1, 1, 4, 1, 3, 3]
def baseStart_2286222 : Nat := 118140960795 + 2286222 * 2 ^ 59
def prefixEnd_2286222 : Nat := 4983230072969 + 3 ^ 40 * 2286222 * 2
def baseEnd_2286222 : Nat := 782620512588972919740575

theorem tailTrace_2286222 : CollatzResearch.WordTrace tailWord_2286222 prefixEnd_2286222 782620512588972919740575 := by
  unfold tailWord_2286222
  simp only [CollatzResearch.WordTrace]
  refine ⟨10423170840426953059618615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55590244482277082984632613 10423170840426953059618615)
  ·
    refine ⟨15634756260640429589427923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10423170840426953059618615 15634756260640429589427923)
    ·
      refine ⟨23452134390960644384141885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15634756260640429589427923 23452134390960644384141885)
      ·
        refine ⟨8794550396610241644053207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23452134390960644384141885 8794550396610241644053207)
        ·
          refine ⟨13191825594915362466079811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8794550396610241644053207 13191825594915362466079811)
          ·
            refine ⟨19787738392373043699119717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13191825594915362466079811 19787738392373043699119717)
            ·
              refine ⟨3710200948569945693584947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19787738392373043699119717 3710200948569945693584947)
              ·
                refine ⟨5565301422854918540377421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3710200948569945693584947 5565301422854918540377421)
                ·
                  refine ⟨2086988033570594452641533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5565301422854918540377421 2086988033570594452641533)
                  ·
                    refine ⟨782620512588972919740575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2086988033570594452641533 782620512588972919740575)
                    ·
                      rfl

theorem cell22_2286222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 4, 1, 3, 3].length) (baseStart_2286222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286222 prefixEnd_2286222 := by exact prefixLift 2286222
  have htrace : WordTrace (prefixWord ++ tailWord_2286222) baseStart_2286222 baseEnd_2286222 := by
    simpa [prefixWord, tailWord_2286222, baseEnd_2286222] using wordTrace_append hprefix tailTrace_2286222
  have hstable : (prefixWord ++ tailWord_2286222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286222).length < 2 ^ (prefixWord ++ tailWord_2286222).sum := by decide
  have hdescent : baseEnd_2286222 < baseStart_2286222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286233 : List Nat := [1, 2, 1, 2, 1, 2, 3, 3, 2, 5]
def baseStart_2286233 : Nat := 118140960795 + 2286233 * 2 ^ 59
def prefixEnd_2286233 : Nat := 4983230072969 + 3 ^ 40 * 2286233 * 2
def baseEnd_2286233 : Nat := 782624278113772557715541

theorem tailTrace_2286233 : CollatzResearch.WordTrace tailWord_2286233 prefixEnd_2286233 782624278113772557715541 := by
  unfold tailWord_2286233
  simp only [CollatzResearch.WordTrace]
  refine ⟨83385767926375773355599353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55590511950917182237066235 83385767926375773355599353)
  ·
    refine ⟨62539325944781830016699515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83385767926375773355599353 62539325944781830016699515)
    ·
      refine ⟨93808988917172745025049273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62539325944781830016699515 93808988917172745025049273)
      ·
        refine ⟨70356741687879558768786955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93808988917172745025049273 70356741687879558768786955)
        ·
          refine ⟨105535112531819338153180433, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70356741687879558768786955 105535112531819338153180433)
          ·
            refine ⟨79151334398864503614885325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105535112531819338153180433 79151334398864503614885325)
            ·
              refine ⟨29681750399574188855581997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79151334398864503614885325 29681750399574188855581997)
              ·
                refine ⟨11130656399840320820843249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29681750399574188855581997 11130656399840320820843249)
                ·
                  refine ⟨8347992299880240615632437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11130656399840320820843249 8347992299880240615632437)
                  ·
                    refine ⟨782624278113772557715541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8347992299880240615632437 782624278113772557715541)
                    ·
                      rfl

theorem cell22_2286233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 3, 3, 2, 5].length) (baseStart_2286233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286233 prefixEnd_2286233 := by exact prefixLift 2286233
  have htrace : WordTrace (prefixWord ++ tailWord_2286233) baseStart_2286233 baseEnd_2286233 := by
    simpa [prefixWord, tailWord_2286233, baseEnd_2286233] using wordTrace_append hprefix tailTrace_2286233
  have hstable : (prefixWord ++ tailWord_2286233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286233).length < 2 ^ (prefixWord ++ tailWord_2286233).sum := by decide
  have hdescent : baseEnd_2286233 < baseStart_2286233 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286273 : List Nat := [1, 2, 6, 2, 2, 1, 1, 1, 3, 3]
def baseStart_2286273 : Nat := 118140960795 + 2286273 * 2 ^ 59
def prefixEnd_2286273 : Nat := 4983230072969 + 3 ^ 40 * 2286273 * 2
def baseEnd_2286273 : Nat := 782637970931225786715419

theorem tailTrace_2286273 : CollatzResearch.WordTrace tailWord_2286273 prefixEnd_2286273 782637970931225786715419 := by
  unfold tailWord_2286273
  simp only [CollatzResearch.WordTrace]
  refine ⟨83387226846230860187055473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55591484564153906791370315 83387226846230860187055473)
  ·
    refine ⟨62540420134673145140291605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83387226846230860187055473 62540420134673145140291605)
    ·
      refine ⟨2931582193812803678451169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 62540420134673145140291605 2931582193812803678451169)
      ·
        refine ⟨2198686645359602758838377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2931582193812803678451169 2198686645359602758838377)
        ·
          refine ⟨1649014984019702069128783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2198686645359602758838377 1649014984019702069128783)
          ·
            refine ⟨2473522476029553103693175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1649014984019702069128783 2473522476029553103693175)
            ·
              refine ⟨3710283714044329655539763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2473522476029553103693175 3710283714044329655539763)
              ·
                refine ⟨5565425571066494483309645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3710283714044329655539763 5565425571066494483309645)
                ·
                  refine ⟨2087034589149935431241117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5565425571066494483309645 2087034589149935431241117)
                  ·
                    refine ⟨782637970931225786715419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2087034589149935431241117 782637970931225786715419)
                    ·
                      rfl

theorem cell22_2286273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 2, 1, 1, 1, 3, 3].length) (baseStart_2286273 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286273 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286273 prefixEnd_2286273 := by exact prefixLift 2286273
  have htrace : WordTrace (prefixWord ++ tailWord_2286273) baseStart_2286273 baseEnd_2286273 := by
    simpa [prefixWord, tailWord_2286273, baseEnd_2286273] using wordTrace_append hprefix tailTrace_2286273
  have hstable : (prefixWord ++ tailWord_2286273).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286273).length < 2 ^ (prefixWord ++ tailWord_2286273).sum := by decide
  have hdescent : baseEnd_2286273 < baseStart_2286273 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286280 : List Nat := [2, 1, 3, 1, 2, 3, 3, 1, 6]
def baseStart_2286280 : Nat := 118140960795 + 2286280 * 2 ^ 59
def prefixEnd_2286280 : Nat := 4983230072969 + 3 ^ 40 * 2286280 * 2
def baseEnd_2286280 : Nat := 260880122391426700596799

theorem tailTrace_2286280 : CollatzResearch.WordTrace tailWord_2286280 prefixEnd_2286280 260880122391426700596799 := by
  unfold tailWord_2286280
  simp only [CollatzResearch.WordTrace]
  refine ⟨41693741078602750191280147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55591654771470333588373529 41693741078602750191280147)
  ·
    refine ⟨62540611617904125286920221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41693741078602750191280147 62540611617904125286920221)
    ·
      refine ⟨23452729356714046982595083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62540611617904125286920221 23452729356714046982595083)
      ·
        refine ⟨35179094035071070473892625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23452729356714046982595083 35179094035071070473892625)
        ·
          refine ⟨26384320526303302855419469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35179094035071070473892625 26384320526303302855419469)
          ·
            refine ⟨9894120197363738570782301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 26384320526303302855419469 9894120197363738570782301)
            ·
              refine ⟨3710295074011401964043363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9894120197363738570782301 3710295074011401964043363)
              ·
                refine ⟨5565442611017102946065045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3710295074011401964043363 5565442611017102946065045)
                ·
                  refine ⟨260880122391426700596799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5565442611017102946065045 260880122391426700596799)
                  ·
                    rfl

theorem cell22_2286280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 3, 1, 6].length) (baseStart_2286280 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286280 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286280 prefixEnd_2286280 := by exact prefixLift 2286280
  have htrace : WordTrace (prefixWord ++ tailWord_2286280) baseStart_2286280 baseEnd_2286280 := by
    simpa [prefixWord, tailWord_2286280, baseEnd_2286280] using wordTrace_append hprefix tailTrace_2286280
  have hstable : (prefixWord ++ tailWord_2286280).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286280).length < 2 ^ (prefixWord ++ tailWord_2286280).sum := by decide
  have hdescent : baseEnd_2286280 < baseStart_2286280 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286312 : List Nat := [2, 1, 4, 1, 4, 1, 1, 2, 1, 5]
def baseStart_2286312 : Nat := 118140960795 + 2286312 * 2 ^ 59
def prefixEnd_2286312 : Nat := 4983230072969 + 3 ^ 40 * 2286312 * 2
def baseEnd_2286312 : Nat := 782651321428242684990299

theorem tailTrace_2286312 : CollatzResearch.WordTrace tailWord_2286312 prefixEnd_2286312 782651321428242684990299 := by
  unfold tailWord_2286312
  simp only [CollatzResearch.WordTrace]
  refine ⟨41694324646544784923862595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55592432862059713231816793 41694324646544784923862595)
  ·
    refine ⟨62541486969817177385793893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41694324646544784923862595 62541486969817177385793893)
    ·
      refine ⟨11726528806840720759836355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62541486969817177385793893 11726528806840720759836355)
      ·
        refine ⟨17589793210261081139754533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11726528806840720759836355 17589793210261081139754533)
        ·
          refine ⟨3298086226923952713703975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17589793210261081139754533 3298086226923952713703975)
          ·
            refine ⟨4947129340385929070555963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3298086226923952713703975 4947129340385929070555963)
            ·
              refine ⟨7420694010578893605833945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4947129340385929070555963 7420694010578893605833945)
              ·
                refine ⟨5565520507934170204375459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7420694010578893605833945 5565520507934170204375459)
                ·
                  refine ⟨8348280761901255306563189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5565520507934170204375459 8348280761901255306563189)
                  ·
                    refine ⟨782651321428242684990299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8348280761901255306563189 782651321428242684990299)
                    ·
                      rfl

theorem cell22_2286312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 1, 1, 2, 1, 5].length) (baseStart_2286312 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286312 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286312 prefixEnd_2286312 := by exact prefixLift 2286312
  have htrace : WordTrace (prefixWord ++ tailWord_2286312) baseStart_2286312 baseEnd_2286312 := by
    simpa [prefixWord, tailWord_2286312, baseEnd_2286312] using wordTrace_append hprefix tailTrace_2286312
  have hstable : (prefixWord ++ tailWord_2286312).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286312).length < 2 ^ (prefixWord ++ tailWord_2286312).sum := by decide
  have hdescent : baseEnd_2286312 < baseStart_2286312 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286357 : List Nat := [1, 3, 2, 1, 2, 2, 3, 2, 3, 3]
def baseStart_2286357 : Nat := 118140960795 + 2286357 * 2 ^ 59
def prefixEnd_2286357 : Nat := 4983230072969 + 3 ^ 40 * 2286357 * 2
def baseEnd_2286357 : Nat := 782666725847877567615161

theorem tailTrace_2286357 : CollatzResearch.WordTrace tailWord_2286357 prefixEnd_2286357 782666725847877567615161 := by
  unfold tailWord_2286357
  simp only [CollatzResearch.WordTrace]
  refine ⟨83390290577926542533113325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55593527051951028355408883 83390290577926542533113325)
  ·
    refine ⟨31271358966722453449917497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83390290577926542533113325 31271358966722453449917497)
    ·
      refine ⟨23453519225041840087438123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31271358966722453449917497 23453519225041840087438123)
      ·
        refine ⟨35180278837562760131157185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23453519225041840087438123 35180278837562760131157185)
        ·
          refine ⟨26385209128172070098367889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35180278837562760131157185 26385209128172070098367889)
          ·
            refine ⟨19788906846129052573775917, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26385209128172070098367889 19788906846129052573775917)
            ·
              refine ⟨7420840067298394715165969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19788906846129052573775917 7420840067298394715165969)
              ·
                refine ⟨5565630050473796036374477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7420840067298394715165969 5565630050473796036374477)
                ·
                  refine ⟨2087111268927673513640429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5565630050473796036374477 2087111268927673513640429)
                  ·
                    refine ⟨782666725847877567615161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2087111268927673513640429 782666725847877567615161)
                    ·
                      rfl

theorem cell22_2286357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 3, 2, 3, 3].length) (baseStart_2286357 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286357 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286357 prefixEnd_2286357 := by exact prefixLift 2286357
  have htrace : WordTrace (prefixWord ++ tailWord_2286357) baseStart_2286357 baseEnd_2286357 := by
    simpa [prefixWord, tailWord_2286357, baseEnd_2286357] using wordTrace_append hprefix tailTrace_2286357
  have hstable : (prefixWord ++ tailWord_2286357).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286357).length < 2 ^ (prefixWord ++ tailWord_2286357).sum := by decide
  have hdescent : baseEnd_2286357 < baseStart_2286357 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286385 : List Nat := [1, 2, 2, 3, 2, 1, 1, 1, 4, 5]
def baseStart_2286385 : Nat := 118140960795 + 2286385 * 2 ^ 59
def prefixEnd_2286385 : Nat := 4983230072969 + 3 ^ 40 * 2286385 * 2
def baseEnd_2286385 : Nat := 782676310820094827915075

theorem tailTrace_2286385 : CollatzResearch.WordTrace tailWord_2286385 prefixEnd_2286385 782676310820094827915075 := by
  unfold tailWord_2286385
  simp only [CollatzResearch.WordTrace]
  refine ⟨83391311821825103315132609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55594207881216735543421739 83391311821825103315132609)
  ·
    refine ⟨62543483866368827486349457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83391311821825103315132609 62543483866368827486349457)
    ·
      refine ⟨46907612899776620614762093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62543483866368827486349457 46907612899776620614762093)
      ·
        refine ⟨17590354837416232730535785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46907612899776620614762093 17590354837416232730535785)
        ·
          refine ⟨13192766128062174547901839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17590354837416232730535785 13192766128062174547901839)
          ·
            refine ⟨19789149192093261821852759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13192766128062174547901839 19789149192093261821852759)
            ·
              refine ⟨29683723788139892732779139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19789149192093261821852759 29683723788139892732779139)
              ·
                refine ⟨44525585682209839099168709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29683723788139892732779139 44525585682209839099168709)
                ·
                  refine ⟨8348547315414344831094133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 44525585682209839099168709 8348547315414344831094133)
                  ·
                    refine ⟨782676310820094827915075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8348547315414344831094133 782676310820094827915075)
                    ·
                      rfl

theorem cell22_2286385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 1, 1, 1, 4, 5].length) (baseStart_2286385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286385 prefixEnd_2286385 := by exact prefixLift 2286385
  have htrace : WordTrace (prefixWord ++ tailWord_2286385) baseStart_2286385 baseEnd_2286385 := by
    simpa [prefixWord, tailWord_2286385, baseEnd_2286385] using wordTrace_append hprefix tailTrace_2286385
  have hstable : (prefixWord ++ tailWord_2286385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286385).length < 2 ^ (prefixWord ++ tailWord_2286385).sum := by decide
  have hdescent : baseEnd_2286385 < baseStart_2286385 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286387 : List Nat := [1, 1, 1, 2, 6, 1, 3, 2, 5]
def baseStart_2286387 : Nat := 118140960795 + 2286387 * 2 ^ 59
def prefixEnd_2286387 : Nat := 4983230072969 + 3 ^ 40 * 2286387 * 2
def baseEnd_2286387 : Nat := 260892331820322496455023

theorem tailTrace_2286387 : CollatzResearch.WordTrace tailWord_2286387 prefixEnd_2286387 260892331820322496455023 := by
  unfold tailWord_2286387
  simp only [CollatzResearch.WordTrace]
  refine ⟨83391384767817857656705415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55594256511878571771136943 83391384767817857656705415)
  ·
    refine ⟨125087077151726786485058123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83391384767817857656705415 125087077151726786485058123)
    ·
      refine ⟨187630615727590179727587185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125087077151726786485058123 187630615727590179727587185)
      ·
        refine ⟨140722961795692634795690389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187630615727590179727587185 140722961795692634795690389)
        ·
          refine ⟨6596388834173092256047987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 140722961795692634795690389 6596388834173092256047987)
          ·
            refine ⟨9894583251259638384071981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6596388834173092256047987 9894583251259638384071981)
            ·
              refine ⟨3710468719222364394026993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9894583251259638384071981 3710468719222364394026993)
              ·
                refine ⟨2782851539416773295520245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3710468719222364394026993 2782851539416773295520245)
                ·
                  refine ⟨260892331820322496455023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2782851539416773295520245 260892331820322496455023)
                  ·
                    rfl

theorem cell22_2286387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 5].length) (baseStart_2286387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286387 prefixEnd_2286387 := by exact prefixLift 2286387
  have htrace : WordTrace (prefixWord ++ tailWord_2286387) baseStart_2286387 baseEnd_2286387 := by
    simpa [prefixWord, tailWord_2286387, baseEnd_2286387] using wordTrace_append hprefix tailTrace_2286387
  have hstable : (prefixWord ++ tailWord_2286387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286387).length < 2 ^ (prefixWord ++ tailWord_2286387).sum := by decide
  have hdescent : baseEnd_2286387 < baseStart_2286387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286400 : List Nat := [2, 1, 1, 2, 2, 1, 1, 3, 5, 4]
def baseStart_2286400 : Nat := 118140960795 + 2286400 * 2 ^ 59
def prefixEnd_2286400 : Nat := 4983230072969 + 3 ^ 40 * 2286400 * 2
def baseEnd_2286400 : Nat := 782681445626639788790029

theorem tailTrace_2286400 : CollatzResearch.WordTrace tailWord_2286400 prefixEnd_2286400 782681445626639788790029 := by
  unfold tailWord_2286400
  simp only [CollatzResearch.WordTrace]
  refine ⟨41695929458385380438464327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55594572611180507251285769 41695929458385380438464327)
  ·
    refine ⟨62543894187578070657696491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41695929458385380438464327 62543894187578070657696491)
    ·
      refine ⟨93815841281367105986544737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62543894187578070657696491 93815841281367105986544737)
      ·
        refine ⟨70361880961025329489908553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93815841281367105986544737 70361880961025329489908553)
        ·
          refine ⟨52771410720768997117431415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70361880961025329489908553 52771410720768997117431415)
          ·
            refine ⟨79157116081153495676147123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52771410720768997117431415 79157116081153495676147123)
            ·
              refine ⟨118735674121730243514220685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79157116081153495676147123 118735674121730243514220685)
              ·
                refine ⟨44525877795648841317832757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 118735674121730243514220685 44525877795648841317832757)
                ·
                  refine ⟨4174301043342078873546821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44525877795648841317832757 4174301043342078873546821)
                  ·
                    refine ⟨782681445626639788790029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4174301043342078873546821 782681445626639788790029)
                    ·
                      rfl

theorem cell22_2286400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 1, 1, 3, 5, 4].length) (baseStart_2286400 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286400 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286400 prefixEnd_2286400 := by exact prefixLift 2286400
  have htrace : WordTrace (prefixWord ++ tailWord_2286400) baseStart_2286400 baseEnd_2286400 := by
    simpa [prefixWord, tailWord_2286400, baseEnd_2286400] using wordTrace_append hprefix tailTrace_2286400
  have hstable : (prefixWord ++ tailWord_2286400).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286400).length < 2 ^ (prefixWord ++ tailWord_2286400).sum := by decide
  have hdescent : baseEnd_2286400 < baseStart_2286400 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286475 : List Nat := [1, 1, 1, 1, 4, 2, 2, 1, 2, 7]
def baseStart_2286475 : Nat := 118140960795 + 2286475 * 2 ^ 59
def prefixEnd_2286475 : Nat := 4983230072969 + 3 ^ 40 * 2286475 * 2
def baseEnd_2286475 : Nat := 782707119659364593164799

theorem tailTrace_2286475 : CollatzResearch.WordTrace tailWord_2286475 prefixEnd_2286475 782707119659364593164799 := by
  unfold tailWord_2286475
  simp only [CollatzResearch.WordTrace]
  refine ⟨83394594391499048685908879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55596396260999365790605919 83394594391499048685908879)
  ·
    refine ⟨125091891587248573028863319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83394594391499048685908879 125091891587248573028863319)
    ·
      refine ⟨187637837380872859543294979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125091891587248573028863319 187637837380872859543294979)
      ·
        refine ⟨281456756071309289314942469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187637837380872859543294979 281456756071309289314942469)
        ·
          refine ⟨52773141763370491746551713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 281456756071309289314942469 52773141763370491746551713)
          ·
            refine ⟨39579856322527868809913785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52773141763370491746551713 39579856322527868809913785)
            ·
              refine ⟨29684892241895901607435339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39579856322527868809913785 29684892241895901607435339)
              ·
                refine ⟨44527338362843852411153009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29684892241895901607435339 44527338362843852411153009)
                ·
                  refine ⟨33395503772132889308364757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44527338362843852411153009 33395503772132889308364757)
                  ·
                    refine ⟨782707119659364593164799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33395503772132889308364757 782707119659364593164799)
                    ·
                      rfl

theorem cell22_2286475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 1, 2, 7].length) (baseStart_2286475 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286475 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286475 prefixEnd_2286475 := by exact prefixLift 2286475
  have htrace : WordTrace (prefixWord ++ tailWord_2286475) baseStart_2286475 baseEnd_2286475 := by
    simpa [prefixWord, tailWord_2286475, baseEnd_2286475] using wordTrace_append hprefix tailTrace_2286475
  have hstable : (prefixWord ++ tailWord_2286475).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286475).length < 2 ^ (prefixWord ++ tailWord_2286475).sum := by decide
  have hdescent : baseEnd_2286475 < baseStart_2286475 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286522 : List Nat := [3, 1, 1, 1, 2, 1, 3, 5, 5]
def baseStart_2286522 : Nat := 118140960795 + 2286522 * 2 ^ 59
def prefixEnd_2286522 : Nat := 4983230072969 + 3 ^ 40 * 2286522 * 2
def baseEnd_2286522 : Nat := 260907736239957379079885

theorem tailTrace_2286522 : CollatzResearch.WordTrace tailWord_2286522 prefixEnd_2286522 260907736239957379079885 := by
  unfold tailWord_2286522
  simp only [CollatzResearch.WordTrace]
  refine ⟨20849077155582193928217455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55597539081552517141913213 20849077155582193928217455)
  ·
    refine ⟨31273615733373290892326183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20849077155582193928217455 31273615733373290892326183)
    ·
      refine ⟨46910423600059936338489275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31273615733373290892326183 46910423600059936338489275)
      ·
        refine ⟨70365635400089904507733913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46910423600059936338489275 70365635400089904507733913)
        ·
          refine ⟨52774226550067428380800435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70365635400089904507733913 52774226550067428380800435)
          ·
            refine ⟨79161339825101142571200653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52774226550067428380800435 79161339825101142571200653)
            ·
              refine ⟨29685502434412928464200245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79161339825101142571200653 29685502434412928464200245)
              ·
                refine ⟨2783015853226212043518773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29685502434412928464200245 2783015853226212043518773)
                ·
                  refine ⟨260907736239957379079885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2783015853226212043518773 260907736239957379079885)
                  ·
                    rfl

theorem cell22_2286522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 5].length) (baseStart_2286522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286522 prefixEnd_2286522 := by exact prefixLift 2286522
  have htrace : WordTrace (prefixWord ++ tailWord_2286522) baseStart_2286522 baseEnd_2286522 := by
    simpa [prefixWord, tailWord_2286522, baseEnd_2286522] using wordTrace_append hprefix tailTrace_2286522
  have hstable : (prefixWord ++ tailWord_2286522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286522).length < 2 ^ (prefixWord ++ tailWord_2286522).sum := by decide
  have hdescent : baseEnd_2286522 < baseStart_2286522 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286594 : List Nat := [3, 4, 1, 3, 2, 1, 1, 3, 1, 3]
def baseStart_2286594 : Nat := 118140960795 + 2286594 * 2 ^ 59
def prefixEnd_2286594 : Nat := 4983230072969 + 3 ^ 40 * 2286594 * 2
def baseEnd_2286594 : Nat := 782747855791287949439435

theorem tailTrace_2286594 : CollatzResearch.WordTrace tailWord_2286594 prefixEnd_2286594 782747855791287949439435 := by
  unfold tailWord_2286594
  simp only [CollatzResearch.WordTrace]
  refine ⟨20849733669516983002372709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55599289785378621339660557 20849733669516983002372709)
  ·
    refine ⟨3909325063034434312944883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20849733669516983002372709 3909325063034434312944883)
    ·
      refine ⟨5863987594551651469417325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3909325063034434312944883 5863987594551651469417325)
      ·
        refine ⟨2198995347956869301031497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5863987594551651469417325 2198995347956869301031497)
        ·
          refine ⟨1649246510967651975773623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2198995347956869301031497 1649246510967651975773623)
          ·
            refine ⟨2473869766451477963660435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1649246510967651975773623 2473869766451477963660435)
            ·
              refine ⟨3710804649677216945490653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2473869766451477963660435 3710804649677216945490653)
              ·
                refine ⟨1391551743628956354558995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3710804649677216945490653 1391551743628956354558995)
                ·
                  refine ⟨2087327615443434531838493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1391551743628956354558995 2087327615443434531838493)
                  ·
                    refine ⟨782747855791287949439435, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2087327615443434531838493 782747855791287949439435)
                    ·
                      rfl

theorem cell22_2286594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 1, 1, 3, 1, 3].length) (baseStart_2286594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286594 prefixEnd_2286594 := by exact prefixLift 2286594
  have htrace : WordTrace (prefixWord ++ tailWord_2286594) baseStart_2286594 baseEnd_2286594 := by
    simpa [prefixWord, tailWord_2286594, baseEnd_2286594] using wordTrace_append hprefix tailTrace_2286594
  have hstable : (prefixWord ++ tailWord_2286594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286594).length < 2 ^ (prefixWord ++ tailWord_2286594).sum := by decide
  have hdescent : baseEnd_2286594 < baseStart_2286594 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286597 : List Nat := [1, 3, 1, 1, 2, 3, 1, 3, 1, 6]
def baseStart_2286597 : Nat := 118140960795 + 2286597 * 2 ^ 59
def prefixEnd_2286597 : Nat := 4983230072969 + 3 ^ 40 * 2286597 * 2
def baseEnd_2286597 : Nat := 782748882752596941614425

theorem tailTrace_2286597 : CollatzResearch.WordTrace tailWord_2286597 prefixEnd_2286597 782748882752596941614425 := by
  unfold tailWord_2286597
  simp only [CollatzResearch.WordTrace]
  refine ⟨83399044097057063521850045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55599362731371375681233363 83399044097057063521850045)
  ·
    refine ⟨31274641536396398820693767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83399044097057063521850045 31274641536396398820693767)
    ·
      refine ⟨46911962304594598231040651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31274641536396398820693767 46911962304594598231040651)
      ·
        refine ⟨70367943456891897346560977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46911962304594598231040651 70367943456891897346560977)
        ·
          refine ⟨52775957592668923009920733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70367943456891897346560977 52775957592668923009920733)
          ·
            refine ⟨19790984097250846128720275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52775957592668923009920733 19790984097250846128720275)
            ·
              refine ⟨29686476145876269193080413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19790984097250846128720275 29686476145876269193080413)
              ·
                refine ⟨11132428554703600947405155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29686476145876269193080413 11132428554703600947405155)
                ·
                  refine ⟨16698642832055401421107733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11132428554703600947405155 16698642832055401421107733)
                  ·
                    refine ⟨782748882752596941614425, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16698642832055401421107733 782748882752596941614425)
                    ·
                      rfl

theorem cell22_2286597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 1, 3, 1, 6].length) (baseStart_2286597 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286597 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286597 prefixEnd_2286597 := by exact prefixLift 2286597
  have htrace : WordTrace (prefixWord ++ tailWord_2286597) baseStart_2286597 baseEnd_2286597 := by
    simpa [prefixWord, tailWord_2286597, baseEnd_2286597] using wordTrace_append hprefix tailTrace_2286597
  have hstable : (prefixWord ++ tailWord_2286597).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286597).length < 2 ^ (prefixWord ++ tailWord_2286597).sum := by decide
  have hdescent : baseEnd_2286597 < baseStart_2286597 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286599 : List Nat := [1, 1, 4, 3, 1, 1, 1, 1, 6, 3]
def baseStart_2286599 : Nat := 118140960795 + 2286599 * 2 ^ 59
def prefixEnd_2286599 : Nat := 4983230072969 + 3 ^ 40 * 2286599 * 2
def baseEnd_2286599 : Nat := 782749567393469603064419

theorem tailTrace_2286599 : CollatzResearch.WordTrace tailWord_2286599 prefixEnd_2286599 782749567393469603064419 := by
  unfold tailWord_2286599
  simp only [CollatzResearch.WordTrace]
  refine ⟨83399117043049817863422851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55599411362033211908948567 83399117043049817863422851)
  ·
    refine ⟨125098675564574726795134277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83399117043049817863422851 125098675564574726795134277)
    ·
      refine ⟨23456001668357761274087677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125098675564574726795134277 23456001668357761274087677)
      ·
        refine ⟨8796000625634160477782879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23456001668357761274087677 8796000625634160477782879)
        ·
          refine ⟨13194000938451240716674319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8796000625634160477782879 13194000938451240716674319)
          ·
            refine ⟨19791001407676861075011479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13194000938451240716674319 19791001407676861075011479)
            ·
              refine ⟨29686502111515291612517219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19791001407676861075011479 29686502111515291612517219)
              ·
                refine ⟨44529753167272937418775829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29686502111515291612517219 44529753167272937418775829)
                ·
                  refine ⟨2087332179715918941505117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 44529753167272937418775829 2087332179715918941505117)
                  ·
                    refine ⟨782749567393469603064419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2087332179715918941505117 782749567393469603064419)
                    ·
                      rfl

theorem cell22_2286599_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_2286599 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286599 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286599 prefixEnd_2286599 := by exact prefixLift 2286599
  have htrace : WordTrace (prefixWord ++ tailWord_2286599) baseStart_2286599 baseEnd_2286599 := by
    simpa [prefixWord, tailWord_2286599, baseEnd_2286599] using wordTrace_append hprefix tailTrace_2286599
  have hstable : (prefixWord ++ tailWord_2286599).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286599).length < 2 ^ (prefixWord ++ tailWord_2286599).sum := by decide
  have hdescent : baseEnd_2286599 < baseStart_2286599 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286599) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286672 : List Nat := [2, 1, 1, 1, 1, 3, 1, 2, 3, 7]
def baseStart_2286672 : Nat := 118140960795 + 2286672 * 2 ^ 59
def prefixEnd_2286672 : Nat := 4983230072969 + 3 ^ 40 * 2286672 * 2
def baseEnd_2286672 : Nat := 782774556785321745989195

theorem tailTrace_2286672 : CollatzResearch.WordTrace tailWord_2286672 prefixEnd_2286672 782774556785321745989195 := by
  unfold tailWord_2286672
  simp only [CollatzResearch.WordTrace]
  refine ⟨41700889785892675665415135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55601186381190234220553513 41700889785892675665415135)
  ·
    refine ⟨62551334678839013498122703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41700889785892675665415135 62551334678839013498122703)
    ·
      refine ⟨93827002018258520247184055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62551334678839013498122703 93827002018258520247184055)
      ·
        refine ⟨140740503027387780370776083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93827002018258520247184055 140740503027387780370776083)
        ·
          refine ⟨211110754541081670556164125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140740503027387780370776083 211110754541081670556164125)
          ·
            refine ⟨79166532952905626458561547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211110754541081670556164125 79166532952905626458561547)
            ·
              refine ⟨118749799429358439687842321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79166532952905626458561547 118749799429358439687842321)
              ·
                refine ⟨89062349572018829765881741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 118749799429358439687842321 89062349572018829765881741)
                ·
                  refine ⟨33398381089507061162205653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 89062349572018829765881741 33398381089507061162205653)
                  ·
                    refine ⟨782774556785321745989195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33398381089507061162205653 782774556785321745989195)
                    ·
                      rfl

theorem cell22_2286672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 1, 2, 3, 7].length) (baseStart_2286672 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286672 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286672 prefixEnd_2286672 := by exact prefixLift 2286672
  have htrace : WordTrace (prefixWord ++ tailWord_2286672) baseStart_2286672 baseEnd_2286672 := by
    simpa [prefixWord, tailWord_2286672, baseEnd_2286672] using wordTrace_append hprefix tailTrace_2286672
  have hstable : (prefixWord ++ tailWord_2286672).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286672).length < 2 ^ (prefixWord ++ tailWord_2286672).sum := by decide
  have hdescent : baseEnd_2286672 < baseStart_2286672 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286704 : List Nat := [2, 1, 1, 1, 5, 1, 1, 3, 3, 4]
def baseStart_2286704 : Nat := 118140960795 + 2286704 * 2 ^ 59
def prefixEnd_2286704 : Nat := 4983230072969 + 3 ^ 40 * 2286704 * 2
def baseEnd_2286704 : Nat := 782785511039284329189097

theorem tailTrace_2286704 : CollatzResearch.WordTrace tailWord_2286704 prefixEnd_2286704 782785511039284329189097 := by
  unfold tailWord_2286704
  simp only [CollatzResearch.WordTrace]
  refine ⟨41701473353834710397997583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55601964471779613863996777 41701473353834710397997583)
  ·
    refine ⟨62552210030752065596996375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41701473353834710397997583 62552210030752065596996375)
    ·
      refine ⟨93828315046128098395494563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62552210030752065596996375 93828315046128098395494563)
      ·
        refine ⟨140742472569192147593241845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93828315046128098395494563 140742472569192147593241845)
        ·
          refine ⟨13194606803361763836866423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 140742472569192147593241845 13194606803361763836866423)
          ·
            refine ⟨19791910205042645755299635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13194606803361763836866423 19791910205042645755299635)
            ·
              refine ⟨29687865307563968632949453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19791910205042645755299635 29687865307563968632949453)
              ·
                refine ⟨11132949490336488237356045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29687865307563968632949453 11132949490336488237356045)
                ·
                  refine ⟨4174856058876183089008517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11132949490336488237356045 4174856058876183089008517)
                  ·
                    refine ⟨782785511039284329189097, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4174856058876183089008517 782785511039284329189097)
                    ·
                      rfl

theorem cell22_2286704_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 1, 3, 3, 4].length) (baseStart_2286704 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286704 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286704 prefixEnd_2286704 := by exact prefixLift 2286704
  have htrace : WordTrace (prefixWord ++ tailWord_2286704) baseStart_2286704 baseEnd_2286704 := by
    simpa [prefixWord, tailWord_2286704, baseEnd_2286704] using wordTrace_append hprefix tailTrace_2286704
  have hstable : (prefixWord ++ tailWord_2286704).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286704).length < 2 ^ (prefixWord ++ tailWord_2286704).sum := by decide
  have hdescent : baseEnd_2286704 < baseStart_2286704 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286704) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286749 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 3, 6]
def baseStart_2286749 : Nat := 118140960795 + 2286749 * 2 ^ 59
def prefixEnd_2286749 : Nat := 4983230072969 + 3 ^ 40 * 2286749 * 2
def baseEnd_2286749 : Nat := 782800915458919211813959

theorem tailTrace_2286749 : CollatzResearch.WordTrace tailWord_2286749 prefixEnd_2286749 782800915458919211813959 := by
  unfold tailWord_2286749
  simp only [CollatzResearch.WordTrace]
  refine ⟨83404587992506393481383301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55603058661670928987588867 83404587992506393481383301)
  ·
    refine ⟨15638360248594948777759369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83404587992506393481383301 15638360248594948777759369)
    ·
      refine ⟨11728770186446211583319527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15638360248594948777759369 11728770186446211583319527)
      ·
        refine ⟨17593155279669317374979291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11728770186446211583319527 17593155279669317374979291)
        ·
          refine ⟨26389732919503976062468937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17593155279669317374979291 26389732919503976062468937)
          ·
            refine ⟨19792299689627982046851703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26389732919503976062468937 19792299689627982046851703)
            ·
              refine ⟨29688449534441973070277555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19792299689627982046851703 29688449534441973070277555)
              ·
                refine ⟨44532674301662959605416333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29688449534441973070277555 44532674301662959605416333)
                ·
                  refine ⟨16699752863123609852031125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44532674301662959605416333 16699752863123609852031125)
                  ·
                    refine ⟨782800915458919211813959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16699752863123609852031125 782800915458919211813959)
                    ·
                      rfl

theorem cell22_2286749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 3, 6].length) (baseStart_2286749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286749 prefixEnd_2286749 := by exact prefixLift 2286749
  have htrace : WordTrace (prefixWord ++ tailWord_2286749) baseStart_2286749 baseEnd_2286749 := by
    simpa [prefixWord, tailWord_2286749, baseEnd_2286749] using wordTrace_append hprefix tailTrace_2286749
  have hstable : (prefixWord ++ tailWord_2286749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286749).length < 2 ^ (prefixWord ++ tailWord_2286749).sum := by decide
  have hdescent : baseEnd_2286749 < baseStart_2286749 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286847 : List Nat := [1, 1, 2, 2, 1, 7, 2, 2, 1, 3]
def baseStart_2286847 : Nat := 118140960795 + 2286847 * 2 ^ 59
def prefixEnd_2286847 : Nat := 4983230072969 + 3 ^ 40 * 2286847 * 2
def baseEnd_2286847 : Nat := 782834462861679622863659

theorem tailTrace_2286847 : CollatzResearch.WordTrace tailWord_2286847 prefixEnd_2286847 782834462861679622863659 := by
  unfold tailWord_2286847
  simp only [CollatzResearch.WordTrace]
  refine ⟨83408162346151356218450795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55605441564100904145633863 83408162346151356218450795)
  ·
    refine ⟨125112243519227034327676193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83408162346151356218450795 125112243519227034327676193)
    ·
      refine ⟨93834182639420275745757145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125112243519227034327676193 93834182639420275745757145)
      ·
        refine ⟨70375636979565206809317859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93834182639420275745757145 70375636979565206809317859)
        ·
          refine ⟨105563455469347810213976789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70375636979565206809317859 105563455469347810213976789)
          ·
            refine ⟨2474143487562839301890081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 105563455469347810213976789 2474143487562839301890081)
            ·
              refine ⟨1855607615672129476417561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2474143487562839301890081 1855607615672129476417561)
              ·
                refine ⟨1391705711754097107313171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1855607615672129476417561 1391705711754097107313171)
                ·
                  refine ⟨2087558567631145660969757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1391705711754097107313171 2087558567631145660969757)
                  ·
                    refine ⟨782834462861679622863659, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2087558567631145660969757 782834462861679622863659)
                    ·
                      rfl

theorem cell22_2286847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 7, 2, 2, 1, 3].length) (baseStart_2286847 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286847 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286847 prefixEnd_2286847 := by exact prefixLift 2286847
  have htrace : WordTrace (prefixWord ++ tailWord_2286847) baseStart_2286847 baseEnd_2286847 := by
    simpa [prefixWord, tailWord_2286847, baseEnd_2286847] using wordTrace_append hprefix tailTrace_2286847
  have hstable : (prefixWord ++ tailWord_2286847).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286847).length < 2 ^ (prefixWord ++ tailWord_2286847).sum := by decide
  have hdescent : baseEnd_2286847 < baseStart_2286847 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286871 : List Nat := [1, 1, 3, 4, 1, 1, 3, 2, 6]
def baseStart_2286871 : Nat := 118140960795 + 2286871 * 2 ^ 59
def prefixEnd_2286871 : Nat := 4983230072969 + 3 ^ 40 * 2286871 * 2
def baseEnd_2286871 : Nat := 260947559517383853421195

theorem tailTrace_2286871 : CollatzResearch.WordTrace tailWord_2286871 prefixEnd_2286871 260947559517383853421195 := by
  unfold tailWord_2286871
  simp only [CollatzResearch.WordTrace]
  refine ⟨83409037698064408317324467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55606025132042938878216311 83409037698064408317324467)
  ·
    refine ⟨125113556547096612475986701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83409037698064408317324467 125113556547096612475986701)
    ·
      refine ⟨46917583705161229678495013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125113556547096612475986701 46917583705161229678495013)
      ·
        refine ⟨8797046944717730564717815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46917583705161229678495013 8797046944717730564717815)
        ·
          refine ⟨13195570417076595847076723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8797046944717730564717815 13195570417076595847076723)
          ·
            refine ⟨19793355625614893770615085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13195570417076595847076723 19793355625614893770615085)
            ·
              refine ⟨7422508359605585163980657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19793355625614893770615085 7422508359605585163980657)
              ·
                refine ⟨5566881269704188872985493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7422508359605585163980657 5566881269704188872985493)
                ·
                  refine ⟨260947559517383853421195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5566881269704188872985493 260947559517383853421195)
                  ·
                    rfl

theorem cell22_2286871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 3, 2, 6].length) (baseStart_2286871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286871 prefixEnd_2286871 := by exact prefixLift 2286871
  have htrace : WordTrace (prefixWord ++ tailWord_2286871) baseStart_2286871 baseEnd_2286871 := by
    simpa [prefixWord, tailWord_2286871, baseEnd_2286871] using wordTrace_append hprefix tailTrace_2286871
  have hstable : (prefixWord ++ tailWord_2286871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286871).length < 2 ^ (prefixWord ++ tailWord_2286871).sum := by decide
  have hdescent : baseEnd_2286871 < baseStart_2286871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286890 : List Nat := [3, 1, 4, 2, 1, 2, 1, 3, 1, 4]
def baseStart_2286890 : Nat := 118140960795 + 2286890 * 2 ^ 59
def prefixEnd_2286890 : Nat := 4983230072969 + 3 ^ 40 * 2286890 * 2
def baseEnd_2286890 : Nat := 782849182640441844038527

theorem tailTrace_2286890 : CollatzResearch.WordTrace tailWord_2286890 prefixEnd_2286890 782849182640441844038527 := by
  unfold tailWord_2286890
  simp only [CollatzResearch.WordTrace]
  refine ⟨20852432671248893640566531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55606487123330383041510749 20852432671248893640566531)
  ·
    refine ⟨31278649006873340460849797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20852432671248893640566531 31278649006873340460849797)
    ·
      refine ⟨5864746688788751336409337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31278649006873340460849797 5864746688788751336409337)
      ·
        refine ⟨4398560016591563502307003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5864746688788751336409337 4398560016591563502307003)
        ·
          refine ⟨6597840024887345253460505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4398560016591563502307003 6597840024887345253460505)
          ·
            refine ⟨4948380018665508940095379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6597840024887345253460505 4948380018665508940095379)
            ·
              refine ⟨7422570027998263410143069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4948380018665508940095379 7422570027998263410143069)
              ·
                refine ⟨2783463760499348778803651, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7422570027998263410143069 2783463760499348778803651)
                ·
                  refine ⟨4175195640749023168205477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2783463760499348778803651 4175195640749023168205477)
                  ·
                    refine ⟨782849182640441844038527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4175195640749023168205477 782849182640441844038527)
                    ·
                      rfl

theorem cell22_2286890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_2286890 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286890 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286890 prefixEnd_2286890 := by exact prefixLift 2286890
  have htrace : WordTrace (prefixWord ++ tailWord_2286890) baseStart_2286890 baseEnd_2286890 := by
    simpa [prefixWord, tailWord_2286890, baseEnd_2286890] using wordTrace_append hprefix tailTrace_2286890
  have hstable : (prefixWord ++ tailWord_2286890).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286890).length < 2 ^ (prefixWord ++ tailWord_2286890).sum := by decide
  have hdescent : baseEnd_2286890 < baseStart_2286890 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286933 : List Nat := [1, 3, 2, 2, 3, 1, 4, 6]
def baseStart_2286933 : Nat := 118140960795 + 2286933 * 2 ^ 59
def prefixEnd_2286933 : Nat := 4983230072969 + 3 ^ 40 * 2286933 * 2
def baseEnd_2286933 : Nat := 86984878046578229468155

theorem tailTrace_2286933 : CollatzResearch.WordTrace tailWord_2286933 prefixEnd_2286933 86984878046578229468155 := by
  unfold tailWord_2286933
  simp only [CollatzResearch.WordTrace]
  refine ⟨83411299023839792906081453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55607532682559861937387635 83411299023839792906081453)
  ·
    refine ⟨31279237133939922339780545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83411299023839792906081453 31279237133939922339780545)
    ·
      refine ⟨23459427850454941754835409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31279237133939922339780545 23459427850454941754835409)
      ·
        refine ⟨17594570887841206316126557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23459427850454941754835409 17594570887841206316126557)
        ·
          refine ⟨6597964082940452368547459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17594570887841206316126557 6597964082940452368547459)
          ·
            refine ⟨9896946124410678552821189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6597964082940452368547459 9896946124410678552821189)
            ·
              refine ⟨1855677398327002228653973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9896946124410678552821189 1855677398327002228653973)
              ·
                refine ⟨86984878046578229468155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1855677398327002228653973 86984878046578229468155)
                ·
                  rfl

theorem cell22_2286933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 3, 1, 4, 6].length) (baseStart_2286933 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286933 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286933 prefixEnd_2286933 := by exact prefixLift 2286933
  have htrace : WordTrace (prefixWord ++ tailWord_2286933) baseStart_2286933 baseEnd_2286933 := by
    simpa [prefixWord, tailWord_2286933, baseEnd_2286933] using wordTrace_append hprefix tailTrace_2286933
  have hstable : (prefixWord ++ tailWord_2286933).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286933).length < 2 ^ (prefixWord ++ tailWord_2286933).sum := by decide
  have hdescent : baseEnd_2286933 < baseStart_2286933 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286961 : List Nat := [1, 2, 2, 2, 1, 2, 4, 1, 7]
def baseStart_2286961 : Nat := 118140960795 + 2286961 * 2 ^ 59
def prefixEnd_2286961 : Nat := 4983230072969 + 3 ^ 40 * 2286961 * 2
def baseEnd_2286961 : Nat := 260957829130473775171103

theorem tailTrace_2286961 : CollatzResearch.WordTrace tailWord_2286961 prefixEnd_2286961 260957829130473775171103 := by
  unfold tailWord_2286961
  simp only [CollatzResearch.WordTrace]
  refine ⟨83412320267738353688100737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55608213511825569125400491 83412320267738353688100737)
  ·
    refine ⟨62559240200803765266075553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83412320267738353688100737 62559240200803765266075553)
    ·
      refine ⟨46919430150602823949556665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62559240200803765266075553 46919430150602823949556665)
      ·
        refine ⟨35189572612952117962167499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46919430150602823949556665 35189572612952117962167499)
        ·
          refine ⟨52784358919428176943251249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35189572612952117962167499 52784358919428176943251249)
          ·
            refine ⟨39588269189571132707438437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52784358919428176943251249 39588269189571132707438437)
            ·
              refine ⟨7422800473044587382644707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39588269189571132707438437 7422800473044587382644707)
              ·
                refine ⟨11134200709566881073967061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7422800473044587382644707 11134200709566881073967061)
                ·
                  refine ⟨260957829130473775171103, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11134200709566881073967061 260957829130473775171103)
                  ·
                    rfl

theorem cell22_2286961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 4, 1, 7].length) (baseStart_2286961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286961 prefixEnd_2286961 := by exact prefixLift 2286961
  have htrace : WordTrace (prefixWord ++ tailWord_2286961) baseStart_2286961 baseEnd_2286961 := by
    simpa [prefixWord, tailWord_2286961, baseEnd_2286961] using wordTrace_append hprefix tailTrace_2286961
  have hstable : (prefixWord ++ tailWord_2286961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286961).length < 2 ^ (prefixWord ++ tailWord_2286961).sum := by decide
  have hdescent : baseEnd_2286961 < baseStart_2286961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2286976 : List Nat := [2, 1, 1, 2, 1, 2, 1, 5, 2, 5]
def baseStart_2286976 : Nat := 118140960795 + 2286976 * 2 ^ 59
def prefixEnd_2286976 : Nat := 4983230072969 + 3 ^ 40 * 2286976 * 2
def baseEnd_2286976 : Nat := 782878622197966286388263

theorem tailTrace_2286976 : CollatzResearch.WordTrace tailWord_2286976 prefixEnd_2286976 782878622197966286388263 := by
  unfold tailWord_2286976
  simp only [CollatzResearch.WordTrace]
  refine ⟨41706433681342005624948391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55608578241789340833264521 41706433681342005624948391)
  ·
    refine ⟨62559650522013008437422587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41706433681342005624948391 62559650522013008437422587)
    ·
      refine ⟨93839475783019512656133881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62559650522013008437422587 93839475783019512656133881)
      ·
        refine ⟨70379606837264634492100411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93839475783019512656133881 70379606837264634492100411)
        ·
          refine ⟨105569410255896951738150617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70379606837264634492100411 105569410255896951738150617)
          ·
            refine ⟨79177057691922713803612963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105569410255896951738150617 79177057691922713803612963)
            ·
              refine ⟨118765586537884070705419445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 79177057691922713803612963 118765586537884070705419445)
              ·
                refine ⟨11134273737926631628633073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 118765586537884070705419445 11134273737926631628633073)
                ·
                  refine ⟨8350705303444973721474805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11134273737926631628633073 8350705303444973721474805)
                  ·
                    refine ⟨782878622197966286388263, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8350705303444973721474805 782878622197966286388263)
                    ·
                      rfl

theorem cell22_2286976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 1, 5, 2, 5].length) (baseStart_2286976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2286976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2286976 prefixEnd_2286976 := by exact prefixLift 2286976
  have htrace : WordTrace (prefixWord ++ tailWord_2286976) baseStart_2286976 baseEnd_2286976 := by
    simpa [prefixWord, tailWord_2286976, baseEnd_2286976] using wordTrace_append hprefix tailTrace_2286976
  have hstable : (prefixWord ++ tailWord_2286976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2286976).length < 2 ^ (prefixWord ++ tailWord_2286976).sum := by decide
  have hdescent : baseEnd_2286976 < baseStart_2286976 := by decide
  rcases family_descends (prefixWord ++ tailWord_2286976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287051 : List Nat := [1, 1, 1, 1, 3, 3, 2, 10]
def baseStart_2287051 : Nat := 118140960795 + 2287051 * 2 ^ 59
def prefixEnd_2287051 : Nat := 4983230072969 + 3 ^ 40 * 2287051 * 2
def baseEnd_2287051 : Nat := 86989366247854565640337

theorem tailTrace_2287051 : CollatzResearch.WordTrace tailWord_2287051 prefixEnd_2287051 86989366247854565640337 := by
  unfold tailWord_2287051
  simp only [CollatzResearch.WordTrace]
  refine ⟨83415602837412299058877007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55610401891608199372584671 83415602837412299058877007)
  ·
    refine ⟨125123404256118448588315511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83415602837412299058877007 125123404256118448588315511)
    ·
      refine ⟨187685106384177672882473267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125123404256118448588315511 187685106384177672882473267)
      ·
        refine ⟨281527659576266509323709901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187685106384177672882473267 281527659576266509323709901)
        ·
          refine ⟨105572872341099940996391213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 281527659576266509323709901 105572872341099940996391213)
          ·
            refine ⟨39589827127912477873646705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105572872341099940996391213 39589827127912477873646705)
            ·
              refine ⟨29692370345934358405235029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39589827127912477873646705 29692370345934358405235029)
              ·
                refine ⟨86989366247854565640337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 29692370345934358405235029 86989366247854565640337)
                ·
                  rfl

theorem cell22_2287051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 10].length) (baseStart_2287051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287051 prefixEnd_2287051 := by exact prefixLift 2287051
  have htrace : WordTrace (prefixWord ++ tailWord_2287051) baseStart_2287051 baseEnd_2287051 := by
    simpa [prefixWord, tailWord_2287051, baseEnd_2287051] using wordTrace_append hprefix tailTrace_2287051
  have hstable : (prefixWord ++ tailWord_2287051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287051).length < 2 ^ (prefixWord ++ tailWord_2287051).sum := by decide
  have hdescent : baseEnd_2287051 < baseStart_2287051 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287100 : List Nat := [2, 2, 2, 1, 2, 1, 4, 2, 3, 3]
def baseStart_2287100 : Nat := 118140960795 + 2287100 * 2 ^ 59
def prefixEnd_2287100 : Nat := 4983230072969 + 3 ^ 40 * 2287100 * 2
def baseEnd_2287100 : Nat := 782921069932071296287883

theorem tailTrace_2287100 : CollatzResearch.WordTrace tailWord_2287100 prefixEnd_2287100 782921069932071296287883 := by
  unfold tailWord_2287100
  simp only [CollatzResearch.WordTrace]
  refine ⟨41708695007117390213705377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55611593342823186951607169 41708695007117390213705377)
  ·
    refine ⟨31281521255338042660279033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41708695007117390213705377 31281521255338042660279033)
    ·
      refine ⟨23461140941503531995209275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31281521255338042660279033 23461140941503531995209275)
      ·
        refine ⟨35191711412255297992813913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23461140941503531995209275 35191711412255297992813913)
        ·
          refine ⟨26393783559191473494610435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35191711412255297992813913 26393783559191473494610435)
          ·
            refine ⟨39590675338787210241915653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26393783559191473494610435 39590675338787210241915653)
            ·
              refine ⟨7423251626022601920359185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39590675338787210241915653 7423251626022601920359185)
              ·
                refine ⟨5567438719516951440269389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7423251626022601920359185 5567438719516951440269389)
                ·
                  refine ⟨2087789519818856790101021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5567438719516951440269389 2087789519818856790101021)
                  ·
                    refine ⟨782921069932071296287883, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2087789519818856790101021 782921069932071296287883)
                    ·
                      rfl

theorem cell22_2287100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 4, 2, 3, 3].length) (baseStart_2287100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287100 prefixEnd_2287100 := by exact prefixLift 2287100
  have htrace : WordTrace (prefixWord ++ tailWord_2287100) baseStart_2287100 baseEnd_2287100 := by
    simpa [prefixWord, tailWord_2287100, baseEnd_2287100] using wordTrace_append hprefix tailTrace_2287100
  have hstable : (prefixWord ++ tailWord_2287100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287100).length < 2 ^ (prefixWord ++ tailWord_2287100).sum := by decide
  have hdescent : baseEnd_2287100 < baseStart_2287100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287102 : List Nat := [4, 2, 2, 3, 1, 1, 1, 8]
def baseStart_2287102 : Nat := 118140960795 + 2287102 * 2 ^ 59
def prefixEnd_2287102 : Nat := 4983230072969 + 3 ^ 40 * 2287102 * 2
def baseEnd_2287102 : Nat := 86991306063660439748653

theorem tailTrace_2287102 : CollatzResearch.WordTrace tailWord_2287102 prefixEnd_2287102 86991306063660439748653 := by
  unfold tailWord_2287102
  simp only [CollatzResearch.WordTrace]
  refine ⟨10427182870028441846122945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55611641973485023179322373 10427182870028441846122945)
  ·
    refine ⟨7820387152521331384592209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10427182870028441846122945 7820387152521331384592209)
    ·
      refine ⟨5865290364390998538444157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7820387152521331384592209 5865290364390998538444157)
      ·
        refine ⟨2199483886646624451916559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5865290364390998538444157 2199483886646624451916559)
        ·
          refine ⟨3299225829969936677874839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2199483886646624451916559 3299225829969936677874839)
          ·
            refine ⟨4948838744954905016812259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3299225829969936677874839 4948838744954905016812259)
            ·
              refine ⟨7423258117432357525218389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4948838744954905016812259 7423258117432357525218389)
              ·
                refine ⟨86991306063660439748653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 7423258117432357525218389 86991306063660439748653)
                ·
                  rfl

theorem cell22_2287102_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 1, 1, 1, 8].length) (baseStart_2287102 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287102 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287102 prefixEnd_2287102 := by exact prefixLift 2287102
  have htrace : WordTrace (prefixWord ++ tailWord_2287102) baseStart_2287102 baseEnd_2287102 := by
    simpa [prefixWord, tailWord_2287102, baseEnd_2287102] using wordTrace_append hprefix tailTrace_2287102
  have hstable : (prefixWord ++ tailWord_2287102).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287102).length < 2 ^ (prefixWord ++ tailWord_2287102).sum := by decide
  have hdescent : baseEnd_2287102 < baseStart_2287102 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287102) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287160 : List Nat := [2, 1, 2, 1, 4, 3, 1, 1, 3, 4]
def baseStart_2287160 : Nat := 118140960795 + 2287160 * 2 ^ 59
def prefixEnd_2287160 : Nat := 4983230072969 + 3 ^ 40 * 2287160 * 2
def baseEnd_2287160 : Nat := 782941609158251139787699

theorem tailTrace_2287160 : CollatzResearch.WordTrace tailWord_2287160 prefixEnd_2287160 782941609158251139787699 := by
  unfold tailWord_2287160
  simp only [CollatzResearch.WordTrace]
  refine ⟨41709789197008705337297467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55613052262678273783063289 41709789197008705337297467)
  ·
    refine ⟨62564683795513058005946201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41709789197008705337297467 62564683795513058005946201)
    ·
      refine ⟨46923512846634793504459651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62564683795513058005946201 46923512846634793504459651)
      ·
        refine ⟨70385269269952190256689477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46923512846634793504459651 70385269269952190256689477)
        ·
          refine ⟨13197237988116035673129277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 70385269269952190256689477 13197237988116035673129277)
          ·
            refine ⟨4948964245543513377423479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13197237988116035673129277 4948964245543513377423479)
            ·
              refine ⟨7423446368315270066135219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4948964245543513377423479 7423446368315270066135219)
              ·
                refine ⟨11135169552472905099202829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7423446368315270066135219 11135169552472905099202829)
                ·
                  refine ⟨4175688582177339412201061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11135169552472905099202829 4175688582177339412201061)
                  ·
                    refine ⟨782941609158251139787699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4175688582177339412201061 782941609158251139787699)
                    ·
                      rfl

theorem cell22_2287160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 3, 1, 1, 3, 4].length) (baseStart_2287160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287160 prefixEnd_2287160 := by exact prefixLift 2287160
  have htrace : WordTrace (prefixWord ++ tailWord_2287160) baseStart_2287160 baseEnd_2287160 := by
    simpa [prefixWord, tailWord_2287160, baseEnd_2287160] using wordTrace_append hprefix tailTrace_2287160
  have hstable : (prefixWord ++ tailWord_2287160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287160).length < 2 ^ (prefixWord ++ tailWord_2287160).sum := by decide
  have hdescent : baseEnd_2287160 < baseStart_2287160 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287207 : List Nat := [1, 1, 5, 1, 1, 1, 4, 3, 2, 3]
def baseStart_2287207 : Nat := 118140960795 + 2287207 * 2 ^ 59
def prefixEnd_2287207 : Nat := 4983230072969 + 3 ^ 40 * 2287207 * 2
def baseEnd_2287207 : Nat := 782957698218758683862555

theorem tailTrace_2287207 : CollatzResearch.WordTrace tailWord_2287207 prefixEnd_2287207 782957698218758683862555 := by
  unfold tailWord_2287207
  simp only [CollatzResearch.WordTrace]
  refine ⟨83421292624847137701555875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55614195083231425134370583 83421292624847137701555875)
  ·
    refine ⟨125131938937270706552333813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83421292624847137701555875 125131938937270706552333813)
    ·
      refine ⟨11731119275369128739281295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125131938937270706552333813 11731119275369128739281295)
      ·
        refine ⟨17596678913053693108921943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11731119275369128739281295 17596678913053693108921943)
        ·
          refine ⟨26395018369580539663382915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17596678913053693108921943 26395018369580539663382915)
          ·
            refine ⟨39592527554370809495074373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26395018369580539663382915 39592527554370809495074373)
            ·
              refine ⟨7423598916444526780326445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39592527554370809495074373 7423598916444526780326445)
              ·
                refine ⟨2783849593666697542622417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7423598916444526780326445 2783849593666697542622417)
                ·
                  refine ⟨2087887195250023156966813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2783849593666697542622417 2087887195250023156966813)
                  ·
                    refine ⟨782957698218758683862555, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2087887195250023156966813 782957698218758683862555)
                    ·
                      rfl

theorem cell22_2287207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_2287207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287207 prefixEnd_2287207 := by exact prefixLift 2287207
  have htrace : WordTrace (prefixWord ++ tailWord_2287207) baseStart_2287207 baseEnd_2287207 := by
    simpa [prefixWord, tailWord_2287207, baseEnd_2287207] using wordTrace_append hprefix tailTrace_2287207
  have hstable : (prefixWord ++ tailWord_2287207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287207).length < 2 ^ (prefixWord ++ tailWord_2287207).sum := by decide
  have hdescent : baseEnd_2287207 < baseStart_2287207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287222 : List Nat := [5, 1, 1, 2, 2, 2, 1, 1, 1, 6]
def baseStart_2287222 : Nat := 118140960795 + 2287222 * 2 ^ 59
def prefixEnd_2287222 : Nat := 4983230072969 + 3 ^ 40 * 2287222 * 2
def baseEnd_2287222 : Nat := 782962833025303644737509

theorem tailTrace_2287222 : CollatzResearch.WordTrace tailWord_2287222 prefixEnd_2287222 782962833025303644737509 := by
  unfold tailWord_2287222
  simp only [CollatzResearch.WordTrace]
  refine ⟨5213864982487049703959495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55614559813195196842234613 5213864982487049703959495)
  ·
    refine ⟨7820797473730574555939243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5213864982487049703959495 7820797473730574555939243)
    ·
      refine ⟨11731196210595861833908865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7820797473730574555939243 11731196210595861833908865)
      ·
        refine ⟨8798397157946896375431649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11731196210595861833908865 8798397157946896375431649)
        ·
          refine ⟨6598797868460172281573737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8798397157946896375431649 6598797868460172281573737)
          ·
            refine ⟨4949098401345129211180303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6598797868460172281573737 4949098401345129211180303)
            ·
              refine ⟨7423647602017693816770455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4949098401345129211180303 7423647602017693816770455)
              ·
                refine ⟨11135471403026540725155683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7423647602017693816770455 11135471403026540725155683)
                ·
                  refine ⟨16703207104539811087733525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11135471403026540725155683 16703207104539811087733525)
                  ·
                    refine ⟨782962833025303644737509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16703207104539811087733525 782962833025303644737509)
                    ·
                      rfl

theorem cell22_2287222_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_2287222 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287222 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287222 prefixEnd_2287222 := by exact prefixLift 2287222
  have htrace : WordTrace (prefixWord ++ tailWord_2287222) baseStart_2287222 baseEnd_2287222 := by
    simpa [prefixWord, tailWord_2287222, baseEnd_2287222] using wordTrace_append hprefix tailTrace_2287222
  have hstable : (prefixWord ++ tailWord_2287222).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287222).length < 2 ^ (prefixWord ++ tailWord_2287222).sum := by decide
  have hdescent : baseEnd_2287222 < baseStart_2287222 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287222) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287235 : List Nat := [1, 1, 1, 3, 3, 1, 1, 1, 7, 3]
def baseStart_2287235 : Nat := 118140960795 + 2287235 * 2 ^ 59
def prefixEnd_2287235 : Nat := 4983230072969 + 3 ^ 40 * 2287235 * 2
def baseEnd_2287235 : Nat := 782967283190975944162469

theorem tailTrace_2287235 : CollatzResearch.WordTrace tailWord_2287235 prefixEnd_2287235 782967283190975944162469 := by
  unfold tailWord_2287235
  simp only [CollatzResearch.WordTrace]
  refine ⟨83422313868745698483575159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55614875912497132322383439 83422313868745698483575159)
  ·
    refine ⟨125133470803118547725362739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83422313868745698483575159 125133470803118547725362739)
    ·
      refine ⟨187700206204677821588044109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125133470803118547725362739 187700206204677821588044109)
      ·
        refine ⟨70387577326754183095516541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187700206204677821588044109 70387577326754183095516541)
        ·
          refine ⟨26395341497532818660818703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 70387577326754183095516541 26395341497532818660818703)
          ·
            refine ⟨39593012246299227991228055, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26395341497532818660818703 39593012246299227991228055)
            ·
              refine ⟨59389518369448841986842083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39593012246299227991228055 59389518369448841986842083)
              ·
                refine ⟨89084277554173262980263125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59389518369448841986842083 89084277554173262980263125)
                ·
                  refine ⟨2087912755175935851099917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 89084277554173262980263125 2087912755175935851099917)
                  ·
                    refine ⟨782967283190975944162469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2087912755175935851099917 782967283190975944162469)
                    ·
                      rfl

theorem cell22_2287235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 1, 1, 7, 3].length) (baseStart_2287235 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287235 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287235 prefixEnd_2287235 := by exact prefixLift 2287235
  have htrace : WordTrace (prefixWord ++ tailWord_2287235) baseStart_2287235 baseEnd_2287235 := by
    simpa [prefixWord, tailWord_2287235, baseEnd_2287235] using wordTrace_append hprefix tailTrace_2287235
  have hstable : (prefixWord ++ tailWord_2287235).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287235).length < 2 ^ (prefixWord ++ tailWord_2287235).sum := by decide
  have hdescent : baseEnd_2287235 < baseStart_2287235 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287316 : List Nat := [2, 4, 1, 3, 1, 3, 2, 1, 5]
def baseStart_2287316 : Nat := 118140960795 + 2287316 * 2 ^ 59
def prefixEnd_2287316 : Nat := 4983230072969 + 3 ^ 40 * 2287316 * 2
def baseEnd_2287316 : Nat := 260998337048772910962407

theorem tailTrace_2287316 : CollatzResearch.WordTrace tailWord_2287316 prefixEnd_2287316 260998337048772910962407 := by
  unfold tailWord_2287316
  simp only [CollatzResearch.WordTrace]
  refine ⟨41712634090726124658636901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55616845454301499544849201 41712634090726124658636901)
  ·
    refine ⟨7821118892011148373494419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41712634090726124658636901 7821118892011148373494419)
    ·
      refine ⟨11731678338016722560241629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7821118892011148373494419 11731678338016722560241629)
      ·
        refine ⟨4399379376756270960090611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11731678338016722560241629 4399379376756270960090611)
        ·
          refine ⟨6599069065134406440135917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4399379376756270960090611 6599069065134406440135917)
          ·
            refine ⟨2474650899425402415050969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6599069065134406440135917 2474650899425402415050969)
            ·
              refine ⟨1855988174569051811288227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2474650899425402415050969 1855988174569051811288227)
              ·
                refine ⟨2783982261853577716932341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1855988174569051811288227 2783982261853577716932341)
                ·
                  refine ⟨260998337048772910962407, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2783982261853577716932341 260998337048772910962407)
                  ·
                    rfl

theorem cell22_2287316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 3, 2, 1, 5].length) (baseStart_2287316 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287316 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287316 prefixEnd_2287316 := by exact prefixLift 2287316
  have htrace : WordTrace (prefixWord ++ tailWord_2287316) baseStart_2287316 baseEnd_2287316 := by
    simpa [prefixWord, tailWord_2287316, baseEnd_2287316] using wordTrace_append hprefix tailTrace_2287316
  have hstable : (prefixWord ++ tailWord_2287316).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287316).length < 2 ^ (prefixWord ++ tailWord_2287316).sum := by decide
  have hdescent : baseEnd_2287316 < baseStart_2287316 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287340 : List Nat := [2, 2, 1, 1, 2, 2, 2, 3, 1, 6]
def baseStart_2287340 : Nat := 118140960795 + 2287340 * 2 ^ 59
def prefixEnd_2287340 : Nat := 4983230072969 + 3 ^ 40 * 2287340 * 2
def baseEnd_2287340 : Nat := 783003226836790670287147

theorem tailTrace_2287340 : CollatzResearch.WordTrace tailWord_2287340 prefixEnd_2287340 783003226836790670287147 := by
  unfold tailWord_2287340
  simp only [CollatzResearch.WordTrace]
  refine ⟨41713071766682650708073737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55617429022243534277431649 41713071766682650708073737)
  ·
    refine ⟨31284803825011988031055303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41713071766682650708073737 31284803825011988031055303)
    ·
      refine ⟨46927205737517982046582955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31284803825011988031055303 46927205737517982046582955)
      ·
        refine ⟨70390808606276973069874433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46927205737517982046582955 70390808606276973069874433)
        ·
          refine ⟨52793106454707729802405825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70390808606276973069874433 52793106454707729802405825)
          ·
            refine ⟨39594829841030797351804369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52793106454707729802405825 39594829841030797351804369)
            ·
              refine ⟨29696122380773098013853277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39594829841030797351804369 29696122380773098013853277)
              ·
                refine ⟨11136045892789911755194979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29696122380773098013853277 11136045892789911755194979)
                ·
                  refine ⟨16704068839184867632792469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11136045892789911755194979 16704068839184867632792469)
                  ·
                    refine ⟨783003226836790670287147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16704068839184867632792469 783003226836790670287147)
                    ·
                      rfl

theorem cell22_2287340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 6].length) (baseStart_2287340 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287340 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287340 prefixEnd_2287340 := by exact prefixLift 2287340
  have htrace : WordTrace (prefixWord ++ tailWord_2287340) baseStart_2287340 baseEnd_2287340 := by
    simpa [prefixWord, tailWord_2287340, baseEnd_2287340] using wordTrace_append hprefix tailTrace_2287340
  have hstable : (prefixWord ++ tailWord_2287340).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287340).length < 2 ^ (prefixWord ++ tailWord_2287340).sum := by decide
  have hdescent : baseEnd_2287340 < baseStart_2287340 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287342 : List Nat := [4, 1, 2, 1, 1, 2, 3, 2, 1, 5]
def baseStart_2287342 : Nat := 118140960795 + 2287342 * 2 ^ 59
def prefixEnd_2287342 : Nat := 4983230072969 + 3 ^ 40 * 2287342 * 2
def baseEnd_2287342 : Nat := 783003911477663331737141

theorem tailTrace_2287342 : CollatzResearch.WordTrace tailWord_2287342 prefixEnd_2287342 783003911477663331737141 := by
  unfold tailWord_2287342
  simp only [CollatzResearch.WordTrace]
  refine ⟨10428277059919756969715035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55617477652905370505146853 10428277059919756969715035)
  ·
    refine ⟨15642415589879635454572553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10428277059919756969715035 15642415589879635454572553)
    ·
      refine ⟨11731811692409726590929415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15642415589879635454572553 11731811692409726590929415)
      ·
        refine ⟨17597717538614589886394123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11731811692409726590929415 17597717538614589886394123)
        ·
          refine ⟨26396576307921884829591185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17597717538614589886394123 26396576307921884829591185)
          ·
            refine ⟨19797432230941413622193389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26396576307921884829591185 19797432230941413622193389)
            ·
              refine ⟨7424037086603030108322521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19797432230941413622193389 7424037086603030108322521)
              ·
                refine ⟨5568027814952272581241891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7424037086603030108322521 5568027814952272581241891)
                ·
                  refine ⟨8352041722428408871862837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5568027814952272581241891 8352041722428408871862837)
                  ·
                    refine ⟨783003911477663331737141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8352041722428408871862837 783003911477663331737141)
                    ·
                      rfl

theorem cell22_2287342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 2, 3, 2, 1, 5].length) (baseStart_2287342 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287342 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287342 prefixEnd_2287342 := by exact prefixLift 2287342
  have htrace : WordTrace (prefixWord ++ tailWord_2287342) baseStart_2287342 baseEnd_2287342 := by
    simpa [prefixWord, tailWord_2287342, baseEnd_2287342] using wordTrace_append hprefix tailTrace_2287342
  have hstable : (prefixWord ++ tailWord_2287342).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287342).length < 2 ^ (prefixWord ++ tailWord_2287342).sum := by decide
  have hdescent : baseEnd_2287342 < baseStart_2287342 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287387 : List Nat := [1, 1, 1, 1, 1, 1, 4, 6, 3, 3]
def baseStart_2287387 : Nat := 118140960795 + 2287387 * 2 ^ 59
def prefixEnd_2287387 : Nat := 4983230072969 + 3 ^ 40 * 2287387 * 2
def baseEnd_2287387 : Nat := 783019315897298214362003

theorem tailTrace_2287387 : CollatzResearch.WordTrace tailWord_2287387 prefixEnd_2287387 783019315897298214362003 := by
  unfold tailWord_2287387
  simp only [CollatzResearch.WordTrace]
  refine ⟨83427857764195028443108415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55618571842796685628738943 83427857764195028443108415)
  ·
    refine ⟨125141786646292542664662623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83427857764195028443108415 125141786646292542664662623)
    ·
      refine ⟨187712679969438813996993935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125141786646292542664662623 187712679969438813996993935)
      ·
        refine ⟨281569019954158220995490903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187712679969438813996993935 281569019954158220995490903)
        ·
          refine ⟨422353529931237331493236355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281569019954158220995490903 422353529931237331493236355)
          ·
            refine ⟨633530294896855997239854533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422353529931237331493236355 633530294896855997239854533)
            ·
              refine ⟨118786930293160499482472725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 633530294896855997239854533 118786930293160499482472725)
              ·
                refine ⟨5568137357491898413240909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 118786930293160499482472725 5568137357491898413240909)
                ·
                  refine ⟨2088051509059461904965341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5568137357491898413240909 2088051509059461904965341)
                  ·
                    refine ⟨783019315897298214362003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2088051509059461904965341 783019315897298214362003)
                    ·
                      rfl

theorem cell22_2287387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 4, 6, 3, 3].length) (baseStart_2287387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287387 prefixEnd_2287387 := by exact prefixLift 2287387
  have htrace : WordTrace (prefixWord ++ tailWord_2287387) baseStart_2287387 baseEnd_2287387 := by
    simpa [prefixWord, tailWord_2287387, baseEnd_2287387] using wordTrace_append hprefix tailTrace_2287387
  have hstable : (prefixWord ++ tailWord_2287387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287387).length < 2 ^ (prefixWord ++ tailWord_2287387).sum := by decide
  have hdescent : baseEnd_2287387 < baseStart_2287387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287421 : List Nat := [1, 4, 1, 4, 1, 2, 2, 1, 3, 3]
def baseStart_2287421 : Nat := 118140960795 + 2287421 * 2 ^ 59
def prefixEnd_2287421 : Nat := 4983230072969 + 3 ^ 40 * 2287421 * 2
def baseEnd_2287421 : Nat := 783030954792133459011899

theorem tailTrace_2287421 : CollatzResearch.WordTrace tailWord_2287421 prefixEnd_2287421 783030954792133459011899 := by
  unfold tailWord_2287421
  simp only [CollatzResearch.WordTrace]
  refine ⟨83429097846071852249846117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55619398564047901499897411 83429097846071852249846117)
  ·
    refine ⟨15642955846138472296846147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83429097846071852249846117 15642955846138472296846147)
    ·
      refine ⟨23464433769207708445269221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15642955846138472296846147 23464433769207708445269221)
      ·
        refine ⟨4399581331726445333487979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23464433769207708445269221 4399581331726445333487979)
        ·
          refine ⟨6599371997589668000231969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4399581331726445333487979 6599371997589668000231969)
          ·
            refine ⟨4949528998192251000173977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6599371997589668000231969 4949528998192251000173977)
            ·
              refine ⟨3712146748644188250130483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4949528998192251000173977 3712146748644188250130483)
              ·
                refine ⟨5568220122966282375195725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3712146748644188250130483 5568220122966282375195725)
                ·
                  refine ⟨2088082546112355890698397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5568220122966282375195725 2088082546112355890698397)
                  ·
                    refine ⟨783030954792133459011899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2088082546112355890698397 783030954792133459011899)
                    ·
                      rfl

theorem cell22_2287421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 2, 2, 1, 3, 3].length) (baseStart_2287421 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287421 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287421 prefixEnd_2287421 := by exact prefixLift 2287421
  have htrace : WordTrace (prefixWord ++ tailWord_2287421) baseStart_2287421 baseEnd_2287421 := by
    simpa [prefixWord, tailWord_2287421, baseEnd_2287421] using wordTrace_append hprefix tailTrace_2287421
  have hstable : (prefixWord ++ tailWord_2287421).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287421).length < 2 ^ (prefixWord ++ tailWord_2287421).sum := by decide
  have hdescent : baseEnd_2287421 < baseStart_2287421 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287432 : List Nat := [2, 1, 3, 1, 1, 4, 2, 1, 2, 5]
def baseStart_2287432 : Nat := 118140960795 + 2287432 * 2 ^ 59
def prefixEnd_2287432 : Nat := 4983230072969 + 3 ^ 40 * 2287432 * 2
def baseEnd_2287432 : Nat := 783034720316933096986865

theorem tailTrace_2287432 : CollatzResearch.WordTrace tailWord_2287432 prefixEnd_2287432 783034720316933096986865 := by
  unfold tailWord_2287432
  simp only [CollatzResearch.WordTrace]
  refine ⟨41714749524516000564248275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55619666032688000752331033 41714749524516000564248275)
  ·
    refine ⟨62572124286774000846372413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41714749524516000564248275 62572124286774000846372413)
    ·
      refine ⟨23464546607540250317389655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 62572124286774000846372413 23464546607540250317389655)
      ·
        refine ⟨35196819911310375476084483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23464546607540250317389655 35196819911310375476084483)
        ·
          refine ⟨52795229866965563214126725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35196819911310375476084483 52795229866965563214126725)
          ·
            refine ⟨9899105600056043102648761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52795229866965563214126725 9899105600056043102648761)
            ·
              refine ⟨7424329200042032326986571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9899105600056043102648761 7424329200042032326986571)
              ·
                refine ⟨11136493800063048490479857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7424329200042032326986571 11136493800063048490479857)
                ·
                  refine ⟨8352370350047286367859893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11136493800063048490479857 8352370350047286367859893)
                  ·
                    refine ⟨783034720316933096986865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8352370350047286367859893 783034720316933096986865)
                    ·
                      rfl

theorem cell22_2287432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 2, 1, 2, 5].length) (baseStart_2287432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287432 prefixEnd_2287432 := by exact prefixLift 2287432
  have htrace : WordTrace (prefixWord ++ tailWord_2287432) baseStart_2287432 baseEnd_2287432 := by
    simpa [prefixWord, tailWord_2287432, baseEnd_2287432] using wordTrace_append hprefix tailTrace_2287432
  have hstable : (prefixWord ++ tailWord_2287432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287432).length < 2 ^ (prefixWord ++ tailWord_2287432).sum := by decide
  have hdescent : baseEnd_2287432 < baseStart_2287432 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287434 : List Nat := [3, 1, 2, 1, 1, 1, 7, 1, 5]
def baseStart_2287434 : Nat := 118140960795 + 2287434 * 2 ^ 59
def prefixEnd_2287434 : Nat := 4983230072969 + 3 ^ 40 * 2287434 * 2
def baseEnd_2287434 : Nat := 261011801652601919478953

theorem tailTrace_2287434 : CollatzResearch.WordTrace tailWord_2287434 prefixEnd_2287434 261011801652601919478953 := by
  unfold tailWord_2287434
  simp only [CollatzResearch.WordTrace]
  refine ⟨20857392998756188867517339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55619714663349836980046237 20857392998756188867517339)
  ·
    refine ⟨31286089498134283301276009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20857392998756188867517339 31286089498134283301276009)
    ·
      refine ⟨23464567123600712475957007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31286089498134283301276009 23464567123600712475957007)
      ·
        refine ⟨35196850685401068713935511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23464567123600712475957007 35196850685401068713935511)
        ·
          refine ⟨52795276028101603070903267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35196850685401068713935511 52795276028101603070903267)
          ·
            refine ⟨79192914042152404606354901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52795276028101603070903267 79192914042152404606354901)
            ·
              refine ⟨1856083922862946982961443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 79192914042152404606354901 1856083922862946982961443)
              ·
                refine ⟨2784125884294420474442165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1856083922862946982961443 2784125884294420474442165)
                ·
                  refine ⟨261011801652601919478953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2784125884294420474442165 261011801652601919478953)
                  ·
                    rfl

theorem cell22_2287434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 5].length) (baseStart_2287434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287434 prefixEnd_2287434 := by exact prefixLift 2287434
  have htrace : WordTrace (prefixWord ++ tailWord_2287434) baseStart_2287434 baseEnd_2287434 := by
    simpa [prefixWord, tailWord_2287434, baseEnd_2287434] using wordTrace_append hprefix tailTrace_2287434
  have hstable : (prefixWord ++ tailWord_2287434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287434).length < 2 ^ (prefixWord ++ tailWord_2287434).sum := by decide
  have hdescent : baseEnd_2287434 < baseStart_2287434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287464 : List Nat := [2, 1, 4, 2, 1, 1, 1, 5, 1, 4]
def baseStart_2287464 : Nat := 118140960795 + 2287464 * 2 ^ 59
def prefixEnd_2287464 : Nat := 4983230072969 + 3 ^ 40 * 2287464 * 2
def baseEnd_2287464 : Nat := 783045674570895680186767

theorem tailTrace_2287464 : CollatzResearch.WordTrace tailWord_2287464 prefixEnd_2287464 783045674570895680186767 := by
  unfold tailWord_2287464
  simp only [CollatzResearch.WordTrace]
  refine ⟨41715333092458035296830723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55620444123277380395774297 41715333092458035296830723)
  ·
    refine ⟨62572999638687052945246085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41715333092458035296830723 62572999638687052945246085)
    ·
      refine ⟨11732437432253822427233641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62572999638687052945246085 11732437432253822427233641)
      ·
        refine ⟨8799328074190366820425231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11732437432253822427233641 8799328074190366820425231)
        ·
          refine ⟨13198992111285550230637847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8799328074190366820425231 13198992111285550230637847)
          ·
            refine ⟨19798488166928325345956771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13198992111285550230637847 19798488166928325345956771)
            ·
              refine ⟨29697732250392488018935157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19798488166928325345956771 29697732250392488018935157)
              ·
                refine ⟨2784162398474295751775171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29697732250392488018935157 2784162398474295751775171)
                ·
                  refine ⟨4176243597711443627662757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2784162398474295751775171 4176243597711443627662757)
                  ·
                    refine ⟨783045674570895680186767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4176243597711443627662757 783045674570895680186767)
                    ·
                      rfl

theorem cell22_2287464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 1, 5, 1, 4].length) (baseStart_2287464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287464 prefixEnd_2287464 := by exact prefixLift 2287464
  have htrace : WordTrace (prefixWord ++ tailWord_2287464) baseStart_2287464 baseEnd_2287464 := by
    simpa [prefixWord, tailWord_2287464, baseEnd_2287464] using wordTrace_append hprefix tailTrace_2287464
  have hstable : (prefixWord ++ tailWord_2287464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287464).length < 2 ^ (prefixWord ++ tailWord_2287464).sum := by decide
  have hdescent : baseEnd_2287464 < baseStart_2287464 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287492 : List Nat := [2, 3, 2, 1, 1, 1, 2, 1, 3, 6]
def baseStart_2287492 : Nat := 118140960795 + 2287492 * 2 ^ 59
def prefixEnd_2287492 : Nat := 4983230072969 + 3 ^ 40 * 2287492 * 2
def baseEnd_2287492 : Nat := 783055259543112940486681

theorem tailTrace_2287492 : CollatzResearch.WordTrace tailWord_2287492 prefixEnd_2287492 783055259543112940486681 := by
  unfold tailWord_2287492
  simp only [CollatzResearch.WordTrace]
  refine ⟨41715843714407315687840365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55621124952543087583787153 41715843714407315687840365)
  ·
    refine ⟨15643441392902743382940137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41715843714407315687840365 15643441392902743382940137)
    ·
      refine ⟨11732581044677057537205103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15643441392902743382940137 11732581044677057537205103)
      ·
        refine ⟨17598871567015586305807655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11732581044677057537205103 17598871567015586305807655)
        ·
          refine ⟨26398307350523379458711483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17598871567015586305807655 26398307350523379458711483)
          ·
            refine ⟨39597461025785069188067225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26398307350523379458711483 39597461025785069188067225)
            ·
              refine ⟨29698095769338801891050419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39597461025785069188067225 29698095769338801891050419)
              ·
                refine ⟨44547143654008202836575629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29698095769338801891050419 44547143654008202836575629)
                ·
                  refine ⟨16705178870253076063715861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44547143654008202836575629 16705178870253076063715861)
                  ·
                    refine ⟨783055259543112940486681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16705178870253076063715861 783055259543112940486681)
                    ·
                      rfl

theorem cell22_2287492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 2, 1, 3, 6].length) (baseStart_2287492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287492 prefixEnd_2287492 := by exact prefixLift 2287492
  have htrace : WordTrace (prefixWord ++ tailWord_2287492) baseStart_2287492 baseEnd_2287492 := by
    simpa [prefixWord, tailWord_2287492, baseEnd_2287492] using wordTrace_append hprefix tailTrace_2287492
  have hstable : (prefixWord ++ tailWord_2287492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287492).length < 2 ^ (prefixWord ++ tailWord_2287492).sum := by decide
  have hdescent : baseEnd_2287492 < baseStart_2287492 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287498 : List Nat := [3, 1, 2, 4, 2, 2, 1, 2, 1, 4]
def baseStart_2287498 : Nat := 118140960795 + 2287498 * 2 ^ 59
def prefixEnd_2287498 : Nat := 4983230072969 + 3 ^ 40 * 2287498 * 2
def baseEnd_2287498 : Nat := 783057313465730924836663

theorem tailTrace_2287498 : CollatzResearch.WordTrace tailWord_2287498 prefixEnd_2287498 783057313465730924836663 := by
  unfold tailWord_2287498
  simp only [CollatzResearch.WordTrace]
  refine ⟨20857976566698223600099787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55621270844528596266932765 20857976566698223600099787)
  ·
    refine ⟨31286964850047335400149681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20857976566698223600099787 31286964850047335400149681)
    ·
      refine ⟨23465223637535501550112261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31286964850047335400149681 23465223637535501550112261)
      ·
        refine ⟨4399729432037906540646049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23465223637535501550112261 4399729432037906540646049)
        ·
          refine ⟨3299797074028429905484537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4399729432037906540646049 3299797074028429905484537)
          ·
            refine ⟨2474847805521322429113403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3299797074028429905484537 2474847805521322429113403)
            ·
              refine ⟨3712271708281983643670105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2474847805521322429113403 3712271708281983643670105)
              ·
                refine ⟨2784203781211487732752579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3712271708281983643670105 2784203781211487732752579)
                ·
                  refine ⟨4176305671817231599128869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2784203781211487732752579 4176305671817231599128869)
                  ·
                    refine ⟨783057313465730924836663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4176305671817231599128869 783057313465730924836663)
                    ·
                      rfl

theorem cell22_2287498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 2, 2, 1, 2, 1, 4].length) (baseStart_2287498 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287498 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287498 prefixEnd_2287498 := by exact prefixLift 2287498
  have htrace : WordTrace (prefixWord ++ tailWord_2287498) baseStart_2287498 baseEnd_2287498 := by
    simpa [prefixWord, tailWord_2287498, baseEnd_2287498] using wordTrace_append hprefix tailTrace_2287498
  have hstable : (prefixWord ++ tailWord_2287498).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287498).length < 2 ^ (prefixWord ++ tailWord_2287498).sum := by decide
  have hdescent : baseEnd_2287498 < baseStart_2287498 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287509 : List Nat := [1, 3, 2, 1, 1, 3, 4, 1, 2, 4]
def baseStart_2287509 : Nat := 118140960795 + 2287509 * 2 ^ 59
def prefixEnd_2287509 : Nat := 4983230072969 + 3 ^ 40 * 2287509 * 2
def baseEnd_2287509 : Nat := 783061078990530562811629

theorem tailTrace_2287509 : CollatzResearch.WordTrace tailWord_2287509 prefixEnd_2287509 783061078990530562811629 := by
  unfold tailWord_2287509
  simp only [CollatzResearch.WordTrace]
  refine ⟨83432307469753043279049581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55621538313168695519366387 83432307469753043279049581)
  ·
    refine ⟨31287115301157391229643593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83432307469753043279049581 31287115301157391229643593)
    ·
      refine ⟨23465336475868043422232695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31287115301157391229643593 23465336475868043422232695)
      ·
        refine ⟨35198004713802065133349043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23465336475868043422232695 35198004713802065133349043)
        ·
          refine ⟨52797007070703097700023565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35198004713802065133349043 52797007070703097700023565)
          ·
            refine ⟨19798877651513661637508837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52797007070703097700023565 19798877651513661637508837)
            ·
              refine ⟨3712289559658811557032907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19798877651513661637508837 3712289559658811557032907)
              ·
                refine ⟨5568434339488217335549361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3712289559658811557032907 5568434339488217335549361)
                ·
                  refine ⟨4176325754616163001662021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5568434339488217335549361 4176325754616163001662021)
                  ·
                    refine ⟨783061078990530562811629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4176325754616163001662021 783061078990530562811629)
                    ·
                      rfl

theorem cell22_2287509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 3, 4, 1, 2, 4].length) (baseStart_2287509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287509 prefixEnd_2287509 := by exact prefixLift 2287509
  have htrace : WordTrace (prefixWord ++ tailWord_2287509) baseStart_2287509 baseEnd_2287509 := by
    simpa [prefixWord, tailWord_2287509, baseEnd_2287509] using wordTrace_append hprefix tailTrace_2287509
  have hstable : (prefixWord ++ tailWord_2287509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287509).length < 2 ^ (prefixWord ++ tailWord_2287509).sum := by decide
  have hdescent : baseEnd_2287509 < baseStart_2287509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287539 : List Nat := [1, 1, 1, 2, 3, 1, 4, 3, 3, 3]
def baseStart_2287539 : Nat := 118140960795 + 2287539 * 2 ^ 59
def prefixEnd_2287539 : Nat := 4983230072969 + 3 ^ 40 * 2287539 * 2
def baseEnd_2287539 : Nat := 783071348603620484561537

theorem tailTrace_2287539 : CollatzResearch.WordTrace tailWord_2287539 prefixEnd_2287539 783071348603620484561537 := by
  unfold tailWord_2287539
  simp only [CollatzResearch.WordTrace]
  refine ⟨83433401659644358402641671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55622267773096238935094447 83433401659644358402641671)
  ·
    refine ⟨125150102489466537603962507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83433401659644358402641671 125150102489466537603962507)
    ·
      refine ⟨187725153734199806405943761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125150102489466537603962507 187725153734199806405943761)
      ·
        refine ⟨140793865300649854804457821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187725153734199806405943761 140793865300649854804457821)
        ·
          refine ⟨52797699487743695551671683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140793865300649854804457821 52797699487743695551671683)
          ·
            refine ⟨79196549231615543327507525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52797699487743695551671683 79196549231615543327507525)
            ·
              refine ⟨14849352980927914373907661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79196549231615543327507525 14849352980927914373907661)
              ·
                refine ⟨5568507367847967890215373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14849352980927914373907661 5568507367847967890215373)
                ·
                  refine ⟨2088190262942987958830765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5568507367847967890215373 2088190262942987958830765)
                  ·
                    refine ⟨783071348603620484561537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2088190262942987958830765 783071348603620484561537)
                    ·
                      rfl

theorem cell22_2287539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 4, 3, 3, 3].length) (baseStart_2287539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287539 prefixEnd_2287539 := by exact prefixLift 2287539
  have htrace : WordTrace (prefixWord ++ tailWord_2287539) baseStart_2287539 baseEnd_2287539 := by
    simpa [prefixWord, tailWord_2287539, baseEnd_2287539] using wordTrace_append hprefix tailTrace_2287539
  have hstable : (prefixWord ++ tailWord_2287539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287539).length < 2 ^ (prefixWord ++ tailWord_2287539).sum := by decide
  have hdescent : baseEnd_2287539 < baseStart_2287539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287567 : List Nat := [1, 1, 2, 1, 1, 5, 1, 2, 1, 7]
def baseStart_2287567 : Nat := 118140960795 + 2287567 * 2 ^ 59
def prefixEnd_2287567 : Nat := 4983230072969 + 3 ^ 40 * 2287567 * 2
def baseEnd_2287567 : Nat := 783080933575837744861451

theorem tailTrace_2287567 : CollatzResearch.WordTrace tailWord_2287567 prefixEnd_2287567 783080933575837744861451 := by
  unfold tailWord_2287567
  simp only [CollatzResearch.WordTrace]
  refine ⟨83434422903542919184660955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55622948602361946123107303 83434422903542919184660955)
  ·
    refine ⟨125151634355314378776991433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83434422903542919184660955 125151634355314378776991433)
    ·
      refine ⟨93863725766485784082743575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125151634355314378776991433 93863725766485784082743575)
      ·
        refine ⟨140795588649728676124115363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93863725766485784082743575 140795588649728676124115363)
        ·
          refine ⟨211193382974593014186173045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140795588649728676124115363 211193382974593014186173045)
          ·
            refine ⟨19799379653868095079953723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 211193382974593014186173045 19799379653868095079953723)
            ·
              refine ⟨29699069480802142619930585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19799379653868095079953723 29699069480802142619930585)
              ·
                refine ⟨22274302110601606964947939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29699069480802142619930585 22274302110601606964947939)
                ·
                  refine ⟨33411453165902410447421909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22274302110601606964947939 33411453165902410447421909)
                  ·
                    refine ⟨783080933575837744861451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33411453165902410447421909 783080933575837744861451)
                    ·
                      rfl

theorem cell22_2287567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 1, 2, 1, 7].length) (baseStart_2287567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287567 prefixEnd_2287567 := by exact prefixLift 2287567
  have htrace : WordTrace (prefixWord ++ tailWord_2287567) baseStart_2287567 baseEnd_2287567 := by
    simpa [prefixWord, tailWord_2287567, baseEnd_2287567] using wordTrace_append hprefix tailTrace_2287567
  have hstable : (prefixWord ++ tailWord_2287567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287567).length < 2 ^ (prefixWord ++ tailWord_2287567).sum := by decide
  have hdescent : baseEnd_2287567 < baseStart_2287567 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287573 : List Nat := [1, 3, 2, 3, 2, 1, 1, 5, 1, 3]
def baseStart_2287573 : Nat := 118140960795 + 2287573 * 2 ^ 59
def prefixEnd_2287573 : Nat := 4983230072969 + 3 ^ 40 * 2287573 * 2
def baseEnd_2287573 : Nat := 783082987498455729211433

theorem tailTrace_2287573 : CollatzResearch.WordTrace tailWord_2287573 prefixEnd_2287573 783082987498455729211433 := by
  unfold tailWord_2287573
  simp only [CollatzResearch.WordTrace]
  refine ⟨83434641741521182209379373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55623094494347454806252915 83434641741521182209379373)
  ·
    refine ⟨31287990653070443328517265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83434641741521182209379373 31287990653070443328517265)
    ·
      refine ⟨23465992989802832496387949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31287990653070443328517265 23465992989802832496387949)
      ·
        refine ⟨8799747371176062186145481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23465992989802832496387949 8799747371176062186145481)
        ·
          refine ⟨6599810528382046639609111, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8799747371176062186145481 6599810528382046639609111)
          ·
            refine ⟨9899715792573069959413667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6599810528382046639609111 9899715792573069959413667)
            ·
              refine ⟨14849573688859604939120501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9899715792573069959413667 14849573688859604939120501)
              ·
                refine ⟨1392147533330587963042547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14849573688859604939120501 1392147533330587963042547)
                ·
                  refine ⟨2088221299995881944563821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1392147533330587963042547 2088221299995881944563821)
                  ·
                    refine ⟨783082987498455729211433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2088221299995881944563821 783082987498455729211433)
                    ·
                      rfl

theorem cell22_2287573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 1, 1, 5, 1, 3].length) (baseStart_2287573 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287573 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287573 prefixEnd_2287573 := by exact prefixLift 2287573
  have htrace : WordTrace (prefixWord ++ tailWord_2287573) baseStart_2287573 baseEnd_2287573 := by
    simpa [prefixWord, tailWord_2287573, baseEnd_2287573] using wordTrace_append hprefix tailTrace_2287573
  have hstable : (prefixWord ++ tailWord_2287573).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287573).length < 2 ^ (prefixWord ++ tailWord_2287573).sum := by decide
  have hdescent : baseEnd_2287573 < baseStart_2287573 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287832 : List Nat := [2, 1, 2, 2, 4, 3, 2, 1, 2, 3]
def baseStart_2287832 : Nat := 118140960795 + 2287832 * 2 ^ 59
def prefixEnd_2287832 : Nat := 4983230072969 + 3 ^ 40 * 2287832 * 2
def baseEnd_2287832 : Nat := 783171648491465386985639

theorem tailTrace_2287832 : CollatzResearch.WordTrace tailWord_2287832 prefixEnd_2287832 783171648491465386985639 := by
  unfold tailWord_2287832
  simp only [CollatzResearch.WordTrace]
  refine ⟨41722044123791434721528875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55629392165055246295371833 41722044123791434721528875)
  ·
    refine ⟨62583066185687152082293313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41722044123791434721528875 62583066185687152082293313)
    ·
      refine ⟨46937299639265364061719985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62583066185687152082293313 46937299639265364061719985)
      ·
        refine ⟨35202974729449023046289989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46937299639265364061719985 35202974729449023046289989)
        ·
          refine ⟨6600557761771691821179373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35202974729449023046289989 6600557761771691821179373)
          ·
            refine ⟨2475209160664384432942265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6600557761771691821179373 2475209160664384432942265)
            ·
              refine ⟨1856406870498288324706699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2475209160664384432942265 1856406870498288324706699)
              ·
                refine ⟨2784610305747432487060049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1856406870498288324706699 2784610305747432487060049)
                ·
                  refine ⟨2088457729310574365295037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2784610305747432487060049 2088457729310574365295037)
                  ·
                    refine ⟨783171648491465386985639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2088457729310574365295037 783171648491465386985639)
                    ·
                      rfl

theorem cell22_2287832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 3, 2, 1, 2, 3].length) (baseStart_2287832 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287832 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287832 prefixEnd_2287832 := by exact prefixLift 2287832
  have htrace : WordTrace (prefixWord ++ tailWord_2287832) baseStart_2287832 baseEnd_2287832 := by
    simpa [prefixWord, tailWord_2287832, baseEnd_2287832] using wordTrace_append hprefix tailTrace_2287832
  have hstable : (prefixWord ++ tailWord_2287832).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287832).length < 2 ^ (prefixWord ++ tailWord_2287832).sum := by decide
  have hdescent : baseEnd_2287832 < baseStart_2287832 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287871 : List Nat := [1, 1, 2, 2, 1, 4, 2, 2, 2, 5]
def baseStart_2287871 : Nat := 118140960795 + 2287871 * 2 ^ 59
def prefixEnd_2287871 : Nat := 4983230072969 + 3 ^ 40 * 2287871 * 2
def baseEnd_2287871 : Nat := 783184998988482285260519

theorem tailTrace_2287871 : CollatzResearch.WordTrace tailWord_2287871 prefixEnd_2287871 783184998988482285260519 := by
  unfold tailWord_2287871
  simp only [CollatzResearch.WordTrace]
  refine ⟨83445510694441579103727467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55630340462961052735818311 83445510694441579103727467)
  ·
    refine ⟨125168266041662368655591201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83445510694441579103727467 125168266041662368655591201)
    ·
      refine ⟨93876199531246776491693401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125168266041662368655591201 93876199531246776491693401)
      ·
        refine ⟨70407149648435082368770051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93876199531246776491693401 70407149648435082368770051)
        ·
          refine ⟨105610724472652623553155077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70407149648435082368770051 105610724472652623553155077)
          ·
            refine ⟨19802010838622366916216577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105610724472652623553155077 19802010838622366916216577)
            ·
              refine ⟨14851508128966775187162433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19802010838622366916216577 14851508128966775187162433)
              ·
                refine ⟨11138631096725081390371825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14851508128966775187162433 11138631096725081390371825)
                ·
                  refine ⟨8353973322543811042778869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11138631096725081390371825 8353973322543811042778869)
                  ·
                    refine ⟨783184998988482285260519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8353973322543811042778869 783184998988482285260519)
                    ·
                      rfl

theorem cell22_2287871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 4, 2, 2, 2, 5].length) (baseStart_2287871 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287871 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287871 prefixEnd_2287871 := by exact prefixLift 2287871
  have htrace : WordTrace (prefixWord ++ tailWord_2287871) baseStart_2287871 baseEnd_2287871 := by
    simpa [prefixWord, tailWord_2287871, baseEnd_2287871] using wordTrace_append hprefix tailTrace_2287871
  have hstable : (prefixWord ++ tailWord_2287871).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287871).length < 2 ^ (prefixWord ++ tailWord_2287871).sum := by decide
  have hdescent : baseEnd_2287871 < baseStart_2287871 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287873 : List Nat := [1, 2, 4, 1, 1, 2, 4, 2, 5]
def baseStart_2287873 : Nat := 118140960795 + 2287873 * 2 ^ 59
def prefixEnd_2287873 : Nat := 4983230072969 + 3 ^ 40 * 2287873 * 2
def baseEnd_2287873 : Nat := 261061894543118315570171

theorem tailTrace_2287873 : CollatzResearch.WordTrace tailWord_2287873 prefixEnd_2287873 261061894543118315570171 := by
  unfold tailWord_2287873
  simp only [CollatzResearch.WordTrace]
  refine ⟨83445583640434333445300273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55630389093622888963533515 83445583640434333445300273)
  ·
    refine ⟨62584187730325750083975205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83445583640434333445300273 62584187730325750083975205)
    ·
      refine ⟨11734535199436078140745351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62584187730325750083975205 11734535199436078140745351)
      ·
        refine ⟨17601802799154117211118027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11734535199436078140745351 17601802799154117211118027)
        ·
          refine ⟨26402704198731175816677041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17601802799154117211118027 26402704198731175816677041)
          ·
            refine ⟨19802028149048381862507781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26402704198731175816677041 19802028149048381862507781)
            ·
              refine ⟨3712880277946571599220209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19802028149048381862507781 3712880277946571599220209)
              ·
                refine ⟨2784660208459928699415157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3712880277946571599220209 2784660208459928699415157)
                ·
                  refine ⟨261061894543118315570171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2784660208459928699415157 261061894543118315570171)
                  ·
                    rfl

theorem cell22_2287873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 4, 2, 5].length) (baseStart_2287873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287873 prefixEnd_2287873 := by exact prefixLift 2287873
  have htrace : WordTrace (prefixWord ++ tailWord_2287873) baseStart_2287873 baseEnd_2287873 := by
    simpa [prefixWord, tailWord_2287873, baseEnd_2287873] using wordTrace_append hprefix tailTrace_2287873
  have hstable : (prefixWord ++ tailWord_2287873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287873).length < 2 ^ (prefixWord ++ tailWord_2287873).sum := by decide
  have hdescent : baseEnd_2287873 < baseStart_2287873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287903 : List Nat := [1, 1, 2, 4, 3, 1, 2, 1, 3, 4]
def baseStart_2287903 : Nat := 118140960795 + 2287903 * 2 ^ 59
def prefixEnd_2287903 : Nat := 4983230072969 + 3 ^ 40 * 2287903 * 2
def baseEnd_2287903 : Nat := 783195953242444868460421

theorem tailTrace_2287903 : CollatzResearch.WordTrace tailWord_2287903 prefixEnd_2287903 783195953242444868460421 := by
  unfold tailWord_2287903
  simp only [CollatzResearch.WordTrace]
  refine ⟨83446677830325648568892363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55631118553550432379261575 83446677830325648568892363)
  ·
    refine ⟨125170016745488472853338545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83446677830325648568892363 125170016745488472853338545)
    ·
      refine ⟨93877512559116354640003909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125170016745488472853338545 93877512559116354640003909)
      ·
        refine ⟨17602033604834316495000733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 93877512559116354640003909 17602033604834316495000733)
        ·
          refine ⟨6600762601812868685625275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17602033604834316495000733 6600762601812868685625275)
          ·
            refine ⟨9901143902719303028437913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6600762601812868685625275 9901143902719303028437913)
            ·
              refine ⟨7425857927039477271328435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9901143902719303028437913 7425857927039477271328435)
              ·
                refine ⟨11138786890559215906992653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7425857927039477271328435 11138786890559215906992653)
                ·
                  refine ⟨4177045083959705965122245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 11138786890559215906992653 4177045083959705965122245)
                  ·
                    refine ⟨783195953242444868460421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4177045083959705965122245 783195953242444868460421)
                    ·
                      rfl

theorem cell22_2287903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 2, 1, 3, 4].length) (baseStart_2287903 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287903 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287903 prefixEnd_2287903 := by exact prefixLift 2287903
  have htrace : WordTrace (prefixWord ++ tailWord_2287903) baseStart_2287903 baseEnd_2287903 := by
    simpa [prefixWord, tailWord_2287903, baseEnd_2287903] using wordTrace_append hprefix tailTrace_2287903
  have hstable : (prefixWord ++ tailWord_2287903).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287903).length < 2 ^ (prefixWord ++ tailWord_2287903).sum := by decide
  have hdescent : baseEnd_2287903 < baseStart_2287903 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287961 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 1, 9]
def baseStart_2287961 : Nat := 118140960795 + 2287961 * 2 ^ 59
def prefixEnd_2287961 : Nat := 4983230072969 + 3 ^ 40 * 2287961 * 2
def baseEnd_2287961 : Nat := 783215807827752050510243

theorem tailTrace_2287961 : CollatzResearch.WordTrace tailWord_2287961 prefixEnd_2287961 783215807827752050510243 := by
  unfold tailWord_2287961
  simp only [CollatzResearch.WordTrace]
  refine ⟨83448793264115524474503737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55632528842743682983002491 83448793264115524474503737)
  ·
    refine ⟨62586594948086643355877803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83448793264115524474503737 62586594948086643355877803)
    ·
      refine ⟨93879892422129965033816705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62586594948086643355877803 93879892422129965033816705)
      ·
        refine ⟨70409919316597473775362529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93879892422129965033816705 70409919316597473775362529)
        ·
          refine ⟨52807439487448105331521897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70409919316597473775362529 52807439487448105331521897)
          ·
            refine ⟨39605579615586078998641423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52807439487448105331521897 39605579615586078998641423)
            ·
              refine ⟨59408369423379118497962135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39605579615586078998641423 59408369423379118497962135)
              ·
                refine ⟨89112554135068677746943203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 59408369423379118497962135 89112554135068677746943203)
                ·
                  refine ⟨133668831202603016620414805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 89112554135068677746943203 133668831202603016620414805)
                  ·
                    refine ⟨783215807827752050510243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 133668831202603016620414805 783215807827752050510243)
                    ·
                      rfl

theorem cell22_2287961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 1, 9].length) (baseStart_2287961 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287961 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287961 prefixEnd_2287961 := by exact prefixLift 2287961
  have htrace : WordTrace (prefixWord ++ tailWord_2287961) baseStart_2287961 baseEnd_2287961 := by
    simpa [prefixWord, tailWord_2287961, baseEnd_2287961] using wordTrace_append hprefix tailTrace_2287961
  have hstable : (prefixWord ++ tailWord_2287961).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287961).length < 2 ^ (prefixWord ++ tailWord_2287961).sum := by decide
  have hdescent : baseEnd_2287961 < baseStart_2287961 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287980 : List Nat := [2, 2, 1, 1, 7, 1, 8]
def baseStart_2287980 : Nat := 118140960795 + 2287980 * 2 ^ 59
def prefixEnd_2287980 : Nat := 4983230072969 + 3 ^ 40 * 2287980 * 2
def baseEnd_2287980 : Nat := 29008233774668234603155

theorem tailTrace_2287980 : CollatzResearch.WordTrace tailWord_2287980 prefixEnd_2287980 29008233774668234603155 := by
  unfold tailWord_2287980
  simp only [CollatzResearch.WordTrace]
  refine ⟨41724743125523345359722697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55632990834031127146296929 41724743125523345359722697)
  ·
    refine ⟨31293557344142509019792023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41724743125523345359722697 31293557344142509019792023)
    ·
      refine ⟨46940336016213763529688035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31293557344142509019792023 46940336016213763529688035)
      ·
        refine ⟨70410504024320645294532053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46940336016213763529688035 70410504024320645294532053)
        ·
          refine ⟨1650246188070015124090595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 70410504024320645294532053 1650246188070015124090595)
          ·
            refine ⟨2475369282105022686135893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1650246188070015124090595 2475369282105022686135893)
            ·
              refine ⟨29008233774668234603155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 2475369282105022686135893 29008233774668234603155)
              ·
                rfl

theorem cell22_2287980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 7, 1, 8].length) (baseStart_2287980 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287980 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287980 prefixEnd_2287980 := by exact prefixLift 2287980
  have htrace : WordTrace (prefixWord ++ tailWord_2287980) baseStart_2287980 baseEnd_2287980 := by
    simpa [prefixWord, tailWord_2287980, baseEnd_2287980] using wordTrace_append hprefix tailTrace_2287980
  have hstable : (prefixWord ++ tailWord_2287980).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287980).length < 2 ^ (prefixWord ++ tailWord_2287980).sum := by decide
  have hdescent : baseEnd_2287980 < baseStart_2287980 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2287995 : List Nat := [1, 1, 1, 1, 1, 7, 3, 1, 3, 3]
def baseStart_2287995 : Nat := 118140960795 + 2287995 * 2 ^ 59
def prefixEnd_2287995 : Nat := 4983230072969 + 3 ^ 40 * 2287995 * 2
def baseEnd_2287995 : Nat := 783227446722587295160139

theorem tailTrace_2287995 : CollatzResearch.WordTrace tailWord_2287995 prefixEnd_2287995 783227446722587295160139 := by
  unfold tailWord_2287995
  simp only [CollatzResearch.WordTrace]
  refine ⟨83450033345992348281241439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55633355563994898854160959 83450033345992348281241439)
  ·
    refine ⟨125175050018988522421862159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83450033345992348281241439 125175050018988522421862159)
    ·
      refine ⟨187762575028482783632793239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125175050018988522421862159 187762575028482783632793239)
      ·
        refine ⟨281643862542724175449189859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187762575028482783632793239 281643862542724175449189859)
        ·
          refine ⟨422465793814086263173784789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281643862542724175449189859 422465793814086263173784789)
          ·
            refine ⟨9901542042517646793135581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 422465793814086263173784789 9901542042517646793135581)
            ·
              refine ⟨3713078265944117547425843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9901542042517646793135581 3713078265944117547425843)
              ·
                refine ⟨5569617398916176321138765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3713078265944117547425843 5569617398916176321138765)
                ·
                  refine ⟨2088606524593566120427037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5569617398916176321138765 2088606524593566120427037)
                  ·
                    refine ⟨783227446722587295160139, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2088606524593566120427037 783227446722587295160139)
                    ·
                      rfl

theorem cell22_2287995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 7, 3, 1, 3, 3].length) (baseStart_2287995 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2287995 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2287995 prefixEnd_2287995 := by exact prefixLift 2287995
  have htrace : WordTrace (prefixWord ++ tailWord_2287995) baseStart_2287995 baseEnd_2287995 := by
    simpa [prefixWord, tailWord_2287995, baseEnd_2287995] using wordTrace_append hprefix tailTrace_2287995
  have hstable : (prefixWord ++ tailWord_2287995).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2287995).length < 2 ^ (prefixWord ++ tailWord_2287995).sum := by decide
  have hdescent : baseEnd_2287995 < baseStart_2287995 := by decide
  rcases family_descends (prefixWord ++ tailWord_2287995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288085 : List Nat := [1, 3, 2, 3, 1, 2, 2, 2, 1, 5]
def baseStart_2288085 : Nat := 118140960795 + 2288085 * 2 ^ 59
def prefixEnd_2288085 : Nat := 4983230072969 + 3 ^ 40 * 2288085 * 2
def baseEnd_2288085 : Nat := 783258255561857060409863

theorem tailTrace_2288085 : CollatzResearch.WordTrace tailWord_2288085 prefixEnd_2288085 783258255561857060409863 := by
  unfold tailWord_2288085
  simp only [CollatzResearch.WordTrace]
  refine ⟨83453315915666293652017709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55635543943777529101345139 83453315915666293652017709)
  ·
    refine ⟨31294993468374860119506641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83453315915666293652017709 31294993468374860119506641)
    ·
      refine ⟨23471245101281145089629981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31294993468374860119506641 23471245101281145089629981)
      ·
        refine ⟨8801716912980429408611243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23471245101281145089629981 8801716912980429408611243)
        ·
          refine ⟨13202575369470644112916865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8801716912980429408611243 13202575369470644112916865)
          ·
            refine ⟨9901931527102983084687649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13202575369470644112916865 9901931527102983084687649)
            ·
              refine ⟨7426448645327237313515737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9901931527102983084687649 7426448645327237313515737)
              ·
                refine ⟨5569836483995427985136803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7426448645327237313515737 5569836483995427985136803)
                ·
                  refine ⟨8354754725993141977705205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5569836483995427985136803 8354754725993141977705205)
                  ·
                    refine ⟨783258255561857060409863, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8354754725993141977705205 783258255561857060409863)
                    ·
                      rfl

theorem cell22_2288085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 2, 2, 2, 1, 5].length) (baseStart_2288085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2288085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2288085 prefixEnd_2288085 := by exact prefixLift 2288085
  have htrace : WordTrace (prefixWord ++ tailWord_2288085) baseStart_2288085 baseEnd_2288085 := by
    simpa [prefixWord, tailWord_2288085, baseEnd_2288085] using wordTrace_append hprefix tailTrace_2288085
  have hstable : (prefixWord ++ tailWord_2288085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288085).length < 2 ^ (prefixWord ++ tailWord_2288085).sum := by decide
  have hdescent : baseEnd_2288085 < baseStart_2288085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288132 : List Nat := [2, 3, 2, 3, 1, 1, 4, 6]
def baseStart_2288132 : Nat := 118140960795 + 2288132 * 2 ^ 59
def prefixEnd_2288132 : Nat := 4983230072969 + 3 ^ 40 * 2288132 * 2
def baseEnd_2288132 : Nat := 87030482735818289387191

theorem tailTrace_2288132 : CollatzResearch.WordTrace tailWord_2288132 prefixEnd_2288132 87030482735818289387191 := by
  unfold tailWord_2288132
  simp only [CollatzResearch.WordTrace]
  refine ⟨41727515073248010339489325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55636686764330680452652433 41727515073248010339489325)
  ·
    refine ⟨15647818152468003877308497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41727515073248010339489325 15647818152468003877308497)
    ·
      refine ⟨11735863614351002907981373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15647818152468003877308497 11735863614351002907981373)
      ·
        refine ⟨4400948855381626090493015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11735863614351002907981373 4400948855381626090493015)
        ·
          refine ⟨6601423283072439135739523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4400948855381626090493015 6601423283072439135739523)
          ·
            refine ⟨9902134924608658703609285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6601423283072439135739523 9902134924608658703609285)
            ·
              refine ⟨1856650298364123506926741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9902134924608658703609285 1856650298364123506926741)
              ·
                refine ⟨87030482735818289387191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1856650298364123506926741 87030482735818289387191)
                ·
                  rfl

theorem cell22_2288132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 1, 4, 6].length) (baseStart_2288132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2288132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2288132 prefixEnd_2288132 := by exact prefixLift 2288132
  have htrace : WordTrace (prefixWord ++ tailWord_2288132) baseStart_2288132 baseEnd_2288132 := by
    simpa [prefixWord, tailWord_2288132, baseEnd_2288132] using wordTrace_append hprefix tailTrace_2288132
  have hstable : (prefixWord ++ tailWord_2288132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288132).length < 2 ^ (prefixWord ++ tailWord_2288132).sum := by decide
  have hdescent : baseEnd_2288132 < baseStart_2288132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288143 : List Nat := [1, 1, 2, 1, 1, 1, 2, 6, 7]
def baseStart_2288143 : Nat := 118140960795 + 2288143 * 2 ^ 59
def prefixEnd_2288143 : Nat := 4983230072969 + 3 ^ 40 * 2288143 * 2
def baseEnd_2288143 : Nat := 261092703382388080819895

theorem tailTrace_2288143 : CollatzResearch.WordTrace tailWord_2288143 prefixEnd_2288143 261092703382388080819895 := by
  unfold tailWord_2288143
  simp only [CollatzResearch.WordTrace]
  refine ⟨83455431349456169557629083, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55636954232970779705086055 83455431349456169557629083)
  ·
    refine ⟨125183147024184254336443625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83455431349456169557629083 125183147024184254336443625)
    ·
      refine ⟨93887360268138190752332719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125183147024184254336443625 93887360268138190752332719)
      ·
        refine ⟨140831040402207286128499079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93887360268138190752332719 140831040402207286128499079)
        ·
          refine ⟨211246560603310929192748619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140831040402207286128499079 211246560603310929192748619)
          ·
            refine ⟨316869840904966393789122929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211246560603310929192748619 316869840904966393789122929)
            ·
              refine ⟨237652380678724795341842197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 316869840904966393789122929 237652380678724795341842197)
              ·
                refine ⟨11139955344315224781648853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 237652380678724795341842197 11139955344315224781648853)
                ·
                  refine ⟨261092703382388080819895, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 11139955344315224781648853 261092703382388080819895)
                  ·
                    rfl

theorem cell22_2288143_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 2, 6, 7].length) (baseStart_2288143 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2288143 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2288143 prefixEnd_2288143 := by exact prefixLift 2288143
  have htrace : WordTrace (prefixWord ++ tailWord_2288143) baseStart_2288143 baseEnd_2288143 := by
    simpa [prefixWord, tailWord_2288143, baseEnd_2288143] using wordTrace_append hprefix tailTrace_2288143
  have hstable : (prefixWord ++ tailWord_2288143).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288143).length < 2 ^ (prefixWord ++ tailWord_2288143).sum := by decide
  have hdescent : baseEnd_2288143 < baseStart_2288143 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288143) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288177 : List Nat := [1, 2, 2, 3, 1, 1, 6, 1, 5]
def baseStart_2288177 : Nat := 118140960795 + 2288177 * 2 ^ 59
def prefixEnd_2288177 : Nat := 4983230072969 + 3 ^ 40 * 2288177 * 2
def baseEnd_2288177 : Nat := 261096583013999829036527

theorem tailTrace_2288177 : CollatzResearch.WordTrace tailWord_2288177 prefixEnd_2288177 261096583013999829036527 := by
  unfold tailWord_2288177
  simp only [CollatzResearch.WordTrace]
  refine ⟨83456671431332993364366785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55637780954221995576244523 83456671431332993364366785)
  ·
    refine ⟨62592503573499745023275089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83456671431332993364366785 62592503573499745023275089)
    ·
      refine ⟨46944377680124808767456317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62592503573499745023275089 46944377680124808767456317)
      ·
        refine ⟨17604141630046803287796119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46944377680124808767456317 17604141630046803287796119)
        ·
          refine ⟨26406212445070204931694179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17604141630046803287796119 26406212445070204931694179)
          ·
            refine ⟨39609318667605307397541269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26406212445070204931694179 39609318667605307397541269)
            ·
              refine ⟨1856686812543998784259747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 39609318667605307397541269 1856686812543998784259747)
              ·
                refine ⟨2785030218815998176389621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1856686812543998784259747 2785030218815998176389621)
                ·
                  refine ⟨261096583013999829036527, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2785030218815998176389621 261096583013999829036527)
                  ·
                    rfl

theorem cell22_2288177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 6, 1, 5].length) (baseStart_2288177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2288177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2288177 prefixEnd_2288177 := by exact prefixLift 2288177
  have htrace : WordTrace (prefixWord ++ tailWord_2288177) baseStart_2288177 baseEnd_2288177 := by
    simpa [prefixWord, tailWord_2288177, baseEnd_2288177] using wordTrace_append hprefix tailTrace_2288177
  have hstable : (prefixWord ++ tailWord_2288177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288177).length < 2 ^ (prefixWord ++ tailWord_2288177).sum := by decide
  have hdescent : baseEnd_2288177 < baseStart_2288177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288237 : List Nat := [1, 5, 1, 1, 3, 1, 1, 3, 1, 5]
def baseStart_2288237 : Nat := 118140960795 + 2288237 * 2 ^ 59
def prefixEnd_2288237 : Nat := 4983230072969 + 3 ^ 40 * 2288237 * 2
def baseEnd_2288237 : Nat := 783310288268179330609397

theorem tailTrace_2288237 : CollatzResearch.WordTrace tailWord_2288237 prefixEnd_2288237 783310288268179330609397 := by
  unfold tailWord_2288237
  simp only [CollatzResearch.WordTrace]
  refine ⟨83458859811115623611550965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55639239874077082407700643 83458859811115623611550965)
  ·
    refine ⟨7824268107292089713582903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83458859811115623611550965 7824268107292089713582903)
    ·
      refine ⟨11736402160938134570374355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7824268107292089713582903 11736402160938134570374355)
      ·
        refine ⟨17604603241407201855561533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11736402160938134570374355 17604603241407201855561533)
        ·
          refine ⟨6601726215527700695835575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17604603241407201855561533 6601726215527700695835575)
          ·
            refine ⟨9902589323291551043753363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6601726215527700695835575 9902589323291551043753363)
            ·
              refine ⟨14853883984937326565630045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9902589323291551043753363 14853883984937326565630045)
              ·
                refine ⟨5570206494351497462111267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14853883984937326565630045 5570206494351497462111267)
                ·
                  refine ⟨8355309741527246193166901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5570206494351497462111267 8355309741527246193166901)
                  ·
                    refine ⟨783310288268179330609397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8355309741527246193166901 783310288268179330609397)
                    ·
                      rfl

theorem cell22_2288237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 1, 1, 3, 1, 5].length) (baseStart_2288237 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2288237 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2288237 prefixEnd_2288237 := by exact prefixLift 2288237
  have htrace : WordTrace (prefixWord ++ tailWord_2288237) baseStart_2288237 baseEnd_2288237 := by
    simpa [prefixWord, tailWord_2288237, baseEnd_2288237] using wordTrace_append hprefix tailTrace_2288237
  have hstable : (prefixWord ++ tailWord_2288237).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288237).length < 2 ^ (prefixWord ++ tailWord_2288237).sum := by decide
  have hdescent : baseEnd_2288237 < baseStart_2288237 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288252 : List Nat := [2, 2, 2, 1, 1, 2, 5, 1, 2, 4]
def baseStart_2288252 : Nat := 118140960795 + 2288252 * 2 ^ 59
def prefixEnd_2288252 : Nat := 4983230072969 + 3 ^ 40 * 2288252 * 2
def baseEnd_2288252 : Nat := 783315423074724291484351

theorem tailTrace_2288252 : CollatzResearch.WordTrace tailWord_2288252 prefixEnd_2288252 783315423074724291484351 := by
  unfold tailWord_2288252
  simp only [CollatzResearch.WordTrace]
  refine ⟨41729703453030640586673505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55639604604040854115564673 41729703453030640586673505)
  ·
    refine ⟨31297277589772980440005129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41729703453030640586673505 31297277589772980440005129)
    ·
      refine ⟨23472958192329735330003847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31297277589772980440005129 23472958192329735330003847)
      ·
        refine ⟨35209437288494602995005771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23472958192329735330003847 35209437288494602995005771)
        ·
          refine ⟨52814155932741904492508657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35209437288494602995005771 52814155932741904492508657)
          ·
            refine ⟨39610616949556428369381493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52814155932741904492508657 39610616949556428369381493)
            ·
              refine ⟨3713495339020915159629515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39610616949556428369381493 3713495339020915159629515)
              ·
                refine ⟨5570243008531372739444273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3713495339020915159629515 5570243008531372739444273)
                ·
                  refine ⟨4177682256398529554583205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5570243008531372739444273 4177682256398529554583205)
                  ·
                    refine ⟨783315423074724291484351, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4177682256398529554583205 783315423074724291484351)
                    ·
                      rfl

theorem cell22_2288252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 5, 1, 2, 4].length) (baseStart_2288252 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2288252 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2288252 prefixEnd_2288252 := by exact prefixLift 2288252
  have htrace : WordTrace (prefixWord ++ tailWord_2288252) baseStart_2288252 baseEnd_2288252 := by
    simpa [prefixWord, tailWord_2288252, baseEnd_2288252] using wordTrace_append hprefix tailTrace_2288252
  have hstable : (prefixWord ++ tailWord_2288252).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288252).length < 2 ^ (prefixWord ++ tailWord_2288252).sum := by decide
  have hdescent : baseEnd_2288252 < baseStart_2288252 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288391 : List Nat := [1, 1, 4, 4, 1, 2, 1, 4, 4]
def baseStart_2288391 : Nat := 118140960795 + 2288391 * 2 ^ 59
def prefixEnd_2288391 : Nat := 4983230072969 + 3 ^ 40 * 2288391 * 2
def baseEnd_2288391 : Nat := 261121001871791420752975

theorem tailTrace_2288391 : CollatzResearch.WordTrace tailWord_2288391 prefixEnd_2288391 261121001871791420752975 := by
  unfold tailWord_2288391
  simp only [CollatzResearch.WordTrace]
  refine ⟨83464476652557707912657027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55642984435038471941771351 83464476652557707912657027)
  ·
    refine ⟨125196714978836561868985541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83464476652557707912657027 125196714978836561868985541)
    ·
      refine ⟨23474384058531855350434789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125196714978836561868985541 23474384058531855350434789)
      ·
        refine ⟨4401447010974722878206523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23474384058531855350434789 4401447010974722878206523)
        ·
          refine ⟨6602170516462084317309785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4401447010974722878206523 6602170516462084317309785)
          ·
            refine ⟨4951627887346563237982339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6602170516462084317309785 4951627887346563237982339)
            ·
              refine ⟨7427441831019844856973509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4951627887346563237982339 7427441831019844856973509)
              ·
                refine ⟨1392645343316220910682533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7427441831019844856973509 1392645343316220910682533)
                ·
                  refine ⟨261121001871791420752975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1392645343316220910682533 261121001871791420752975)
                  ·
                    rfl

theorem cell22_2288391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4, 4].length) (baseStart_2288391 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2288391 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2288391 prefixEnd_2288391 := by exact prefixLift 2288391
  have htrace : WordTrace (prefixWord ++ tailWord_2288391) baseStart_2288391 baseEnd_2288391 := by
    simpa [prefixWord, tailWord_2288391, baseEnd_2288391] using wordTrace_append hprefix tailTrace_2288391
  have hstable : (prefixWord ++ tailWord_2288391).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288391).length < 2 ^ (prefixWord ++ tailWord_2288391).sum := by decide
  have hdescent : baseEnd_2288391 < baseStart_2288391 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288434 : List Nat := [3, 2, 1, 1, 3, 1, 1, 2, 5, 3]
def baseStart_2288434 : Nat := 118140960795 + 2288434 * 2 ^ 59
def prefixEnd_2288434 : Nat := 4983230072969 + 3 ^ 40 * 2288434 * 2
def baseEnd_2288434 : Nat := 783377725394136483433793

theorem tailTrace_2288434 : CollatzResearch.WordTrace tailWord_2288434 prefixEnd_2288434 783377725394136483433793 := by
  unfold tailWord_2288434
  simp only [CollatzResearch.WordTrace]
  refine ⟨20866511247850481564118089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55644029994267950837648237 20866511247850481564118089)
  ·
    refine ⟨15649883435887861173088567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20866511247850481564118089 15649883435887861173088567)
    ·
      refine ⟨23474825153831791759632851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15649883435887861173088567 23474825153831791759632851)
      ·
        refine ⟨35212237730747687639449277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23474825153831791759632851 35212237730747687639449277)
        ·
          refine ⟨13204589149030382864793479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35212237730747687639449277 13204589149030382864793479)
          ·
            refine ⟨19806883723545574297190219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13204589149030382864793479 19806883723545574297190219)
            ·
              refine ⟨29710325585318361445785329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19806883723545574297190219 29710325585318361445785329)
              ·
                refine ⟨22282744188988771084338997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29710325585318361445785329 22282744188988771084338997)
                ·
                  refine ⟨2089007267717697289156781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22282744188988771084338997 2089007267717697289156781)
                  ·
                    refine ⟨783377725394136483433793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2089007267717697289156781 783377725394136483433793)
                    ·
                      rfl

theorem cell22_2288434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 1, 2, 5, 3].length) (baseStart_2288434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2288434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2288434 prefixEnd_2288434 := by exact prefixLift 2288434
  have htrace : WordTrace (prefixWord ++ tailWord_2288434) baseStart_2288434 baseEnd_2288434 := by
    simpa [prefixWord, tailWord_2288434, baseEnd_2288434] using wordTrace_append hprefix tailTrace_2288434
  have hstable : (prefixWord ++ tailWord_2288434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288434).length < 2 ^ (prefixWord ++ tailWord_2288434).sum := by decide
  have hdescent : baseEnd_2288434 < baseStart_2288434 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288451 : List Nat := [1, 1, 1, 3, 1, 4, 1, 6, 1, 3]
def baseStart_2288451 : Nat := 118140960795 + 2288451 * 2 ^ 59
def prefixEnd_2288451 : Nat := 4983230072969 + 3 ^ 40 * 2288451 * 2
def baseEnd_2288451 : Nat := 783383544841554105758741

theorem tailTrace_2288451 : CollatzResearch.WordTrace tailWord_2288451 prefixEnd_2288451 783383544841554105758741 := by
  unfold tailWord_2288451
  simp only [CollatzResearch.WordTrace]
  refine ⟨83466665032340338159841207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55644443354893558773227471 83466665032340338159841207)
  ·
    refine ⟨125199997548510507239761811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83466665032340338159841207 125199997548510507239761811)
    ·
      refine ⟨187799996322765760859642717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125199997548510507239761811 187799996322765760859642717)
      ·
        refine ⟨70424998621037160322366019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 187799996322765760859642717 70424998621037160322366019)
        ·
          refine ⟨105637497931555740483549029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70424998621037160322366019 105637497931555740483549029)
          ·
            refine ⟨19807030862166701340665443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105637497931555740483549029 19807030862166701340665443)
            ·
              refine ⟨29710546293250052010998165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19807030862166701340665443 29710546293250052010998165)
              ·
                refine ⟨1392681857496096188015539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29710546293250052010998165 1392681857496096188015539)
                ·
                  refine ⟨2089022786244144282023309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1392681857496096188015539 2089022786244144282023309)
                  ·
                    refine ⟨783383544841554105758741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2089022786244144282023309 783383544841554105758741)
                    ·
                      rfl

theorem cell22_2288451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 1, 6, 1, 3].length) (baseStart_2288451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2288451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2288451 prefixEnd_2288451 := by exact prefixLift 2288451
  have htrace : WordTrace (prefixWord ++ tailWord_2288451) baseStart_2288451 baseEnd_2288451 := by
    simpa [prefixWord, tailWord_2288451, baseEnd_2288451] using wordTrace_append hprefix tailTrace_2288451
  have hstable : (prefixWord ++ tailWord_2288451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288451).length < 2 ^ (prefixWord ++ tailWord_2288451).sum := by decide
  have hdescent : baseEnd_2288451 < baseStart_2288451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288502 : List Nat := [5, 1, 1, 3, 1, 2, 3, 2, 1, 3]
def baseStart_2288502 : Nat := 118140960795 + 2288502 * 2 ^ 59
def prefixEnd_2288502 : Nat := 4983230072969 + 3 ^ 40 * 2288502 * 2
def baseEnd_2288502 : Nat := 783401003183806972733585

theorem tailTrace_2288502 : CollatzResearch.WordTrace tailWord_2288502 prefixEnd_2288502 783401003183806972733585 := by
  unfold tailWord_2288502
  simp only [CollatzResearch.WordTrace]
  refine ⟨5216782822197223366871735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55645683436770382579965173 5216782822197223366871735)
  ·
    refine ⟨7825174233295835050307603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5216782822197223366871735 7825174233295835050307603)
    ·
      refine ⟨11737761349943752575461405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7825174233295835050307603 11737761349943752575461405)
      ·
        refine ⟨4401660506228907215798027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11737761349943752575461405 4401660506228907215798027)
        ·
          refine ⟨6602490759343360823697041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4401660506228907215798027 6602490759343360823697041)
          ·
            refine ⟨4951868069507520617772781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6602490759343360823697041 4951868069507520617772781)
            ·
              refine ⟨1856950526065320231664793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4951868069507520617772781 1856950526065320231664793)
              ·
                refine ⟨1392712894548990173748595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1856950526065320231664793 1392712894548990173748595)
                ·
                  refine ⟨2089069341823485260622893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1392712894548990173748595 2089069341823485260622893)
                  ·
                    refine ⟨783401003183806972733585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2089069341823485260622893 783401003183806972733585)
                    ·
                      rfl

theorem cell22_2288502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_2288502 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2288502 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2288502 prefixEnd_2288502 := by exact prefixLift 2288502
  have htrace : WordTrace (prefixWord ++ tailWord_2288502) baseStart_2288502 baseEnd_2288502 := by
    simpa [prefixWord, tailWord_2288502, baseEnd_2288502] using wordTrace_append hprefix tailTrace_2288502
  have hstable : (prefixWord ++ tailWord_2288502).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288502).length < 2 ^ (prefixWord ++ tailWord_2288502).sum := by decide
  have hdescent : baseEnd_2288502 < baseStart_2288502 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288509 : List Nat := [1, 4, 1, 1, 2, 1, 5, 1, 6]
def baseStart_2288509 : Nat := 118140960795 + 2288509 * 2 ^ 59
def prefixEnd_2288509 : Nat := 4983230072969 + 3 ^ 40 * 2288509 * 2
def baseEnd_2288509 : Nat := 261134466475620429269521

theorem tailTrace_2288509 : CollatzResearch.WordTrace tailWord_2288509 prefixEnd_2288509 261134466475620429269521 := by
  unfold tailWord_2288509
  simp only [CollatzResearch.WordTrace]
  refine ⟨83468780466130214065452581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55645853644086809376968387 83468780466130214065452581)
  ·
    refine ⟨15650396337399415137272359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83468780466130214065452581 15650396337399415137272359)
    ·
      refine ⟨23475594506099122705908539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15650396337399415137272359 23475594506099122705908539)
      ·
        refine ⟨35213391759148684058862809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23475594506099122705908539 35213391759148684058862809)
        ·
          refine ⟨26410043819361513044147107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35213391759148684058862809 26410043819361513044147107)
          ·
            refine ⟨39615065729042269566220661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26410043819361513044147107 39615065729042269566220661)
            ·
              refine ⟨3713912412097712771833187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39615065729042269566220661 3713912412097712771833187)
              ·
                refine ⟨5570868618146569157749781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3713912412097712771833187 5570868618146569157749781)
                ·
                  refine ⟨261134466475620429269521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5570868618146569157749781 261134466475620429269521)
                  ·
                    rfl

theorem cell22_2288509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 5, 1, 6].length) (baseStart_2288509 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2288509 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2288509 prefixEnd_2288509 := by exact prefixLift 2288509
  have htrace : WordTrace (prefixWord ++ tailWord_2288509) baseStart_2288509 baseEnd_2288509 := by
    simpa [prefixWord, tailWord_2288509, baseEnd_2288509] using wordTrace_append hprefix tailTrace_2288509
  have hstable : (prefixWord ++ tailWord_2288509).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288509).length < 2 ^ (prefixWord ++ tailWord_2288509).sum := by decide
  have hdescent : baseEnd_2288509 < baseStart_2288509 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288616 : List Nat := [2, 1, 4, 1, 1, 1, 5, 2, 5]
def baseStart_2288616 : Nat := 118140960795 + 2288616 * 2 ^ 59
def prefixEnd_2288616 : Nat := 4983230072969 + 3 ^ 40 * 2288616 * 2
def baseEnd_2288616 : Nat := 261146675904516225127745

theorem tailTrace_2288616 : CollatzResearch.WordTrace tailWord_2288616 prefixEnd_2288616 261146675904516225127745 := by
  unfold tailWord_2288616
  simp only [CollatzResearch.WordTrace]
  refine ⟨41736341538371285669798851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55648455384495047559731801 41736341538371285669798851)
  ·
    refine ⟨62604512307556928504698277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41736341538371285669798851 62604512307556928504698277)
    ·
      refine ⟨11738346057666924094630927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62604512307556928504698277 11738346057666924094630927)
      ·
        refine ⟨17607519086500386141946391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11738346057666924094630927 17607519086500386141946391)
        ·
          refine ⟨26411278629750579212919587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17607519086500386141946391 26411278629750579212919587)
          ·
            refine ⟨39616917944625868819379381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26411278629750579212919587 39616917944625868819379381)
            ·
              refine ⟨3714086057308675201816817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39616917944625868819379381 3714086057308675201816817)
              ·
                refine ⟨2785564542981506401362613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3714086057308675201816817 2785564542981506401362613)
                ·
                  refine ⟨261146675904516225127745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2785564542981506401362613 261146675904516225127745)
                  ·
                    rfl

theorem cell22_2288616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 5].length) (baseStart_2288616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2288616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2288616 prefixEnd_2288616 := by exact prefixLift 2288616
  have htrace : WordTrace (prefixWord ++ tailWord_2288616) baseStart_2288616 baseEnd_2288616 := by
    simpa [prefixWord, tailWord_2288616, baseEnd_2288616] using wordTrace_append hprefix tailTrace_2288616
  have hstable : (prefixWord ++ tailWord_2288616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288616).length < 2 ^ (prefixWord ++ tailWord_2288616).sum := by decide
  have hdescent : baseEnd_2288616 < baseStart_2288616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288659 : List Nat := [1, 1, 1, 2, 1, 4, 1, 3, 3, 5]
def baseStart_2288659 : Nat := 118140960795 + 2288659 * 2 ^ 59
def prefixEnd_2288659 : Nat := 4983230072969 + 3 ^ 40 * 2288659 * 2
def baseEnd_2288659 : Nat := 783454747492310896558103

theorem tailTrace_2288659 : CollatzResearch.WordTrace tailWord_2288659 prefixEnd_2288659 783454747492310896558103 := by
  unfold tailWord_2288659
  simp only [CollatzResearch.WordTrace]
  refine ⟨83474251415586789683413031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55649500943724526455608687 83474251415586789683413031)
  ·
    refine ⟨125211377123380184525119547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83474251415586789683413031 125211377123380184525119547)
    ·
      refine ⟨187817065685070276787679321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125211377123380184525119547 187817065685070276787679321)
      ·
        refine ⟨140862799263802707590759491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187817065685070276787679321 140862799263802707590759491)
        ·
          refine ⟨211294198895704061386139237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140862799263802707590759491 211294198895704061386139237)
          ·
            refine ⟨39617662292944511509901107, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 211294198895704061386139237 39617662292944511509901107)
            ·
              refine ⟨59426493439416767264851661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39617662292944511509901107 59426493439416767264851661)
              ·
                refine ⟨22284935039781287724319373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 59426493439416767264851661 22284935039781287724319373)
                ·
                  refine ⟨8356850639917982896619765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 22284935039781287724319373 8356850639917982896619765)
                  ·
                    refine ⟨783454747492310896558103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8356850639917982896619765 783454747492310896558103)
                    ·
                      rfl

theorem cell22_2288659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 3, 3, 5].length) (baseStart_2288659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2288659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2288659 prefixEnd_2288659 := by exact prefixLift 2288659
  have htrace : WordTrace (prefixWord ++ tailWord_2288659) baseStart_2288659 baseEnd_2288659 := by
    simpa [prefixWord, tailWord_2288659, baseEnd_2288659] using wordTrace_append hprefix tailTrace_2288659
  have hstable : (prefixWord ++ tailWord_2288659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288659).length < 2 ^ (prefixWord ++ tailWord_2288659).sum := by decide
  have hdescent : baseEnd_2288659 < baseStart_2288659 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288663 : List Nat := [1, 1, 3, 5, 1, 1, 2, 3, 1, 4]
def baseStart_2288663 : Nat := 118140960795 + 2288663 * 2 ^ 59
def prefixEnd_2288663 : Nat := 4983230072969 + 3 ^ 40 * 2288663 * 2
def baseEnd_2288663 : Nat := 783456116774056219458091

theorem tailTrace_2288663 : CollatzResearch.WordTrace tailWord_2288663 prefixEnd_2288663 783456116774056219458091 := by
  unfold tailWord_2288663
  simp only [CollatzResearch.WordTrace]
  refine ⟨83474397307572298366558643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55649598205048198911039095 83474397307572298366558643)
  ·
    refine ⟨125211595961358447549837965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83474397307572298366558643 125211595961358447549837965)
    ·
      refine ⟨46954348485509417831189237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125211595961358447549837965 46954348485509417831189237)
      ·
        refine ⟨4401970170516507921673991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 46954348485509417831189237 4401970170516507921673991)
        ·
          refine ⟨6602955255774761882510987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4401970170516507921673991 6602955255774761882510987)
          ·
            refine ⟨9904432883662142823766481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6602955255774761882510987 9904432883662142823766481)
            ·
              refine ⟨7428324662746607117824861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9904432883662142823766481 7428324662746607117824861)
              ·
                refine ⟨2785621748529977669184323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7428324662746607117824861 2785621748529977669184323)
                ·
                  refine ⟨4178432622794966503776485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2785621748529977669184323 4178432622794966503776485)
                  ·
                    refine ⟨783456116774056219458091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4178432622794966503776485 783456116774056219458091)
                    ·
                      rfl

theorem cell22_2288663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_2288663 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2288663 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2288663 prefixEnd_2288663 := by exact prefixLift 2288663
  have htrace : WordTrace (prefixWord ++ tailWord_2288663) baseStart_2288663 baseEnd_2288663 := by
    simpa [prefixWord, tailWord_2288663, baseEnd_2288663] using wordTrace_append hprefix tailTrace_2288663
  have hstable : (prefixWord ++ tailWord_2288663).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288663).length < 2 ^ (prefixWord ++ tailWord_2288663).sum := by decide
  have hdescent : baseEnd_2288663 < baseStart_2288663 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288710 : List Nat := [6, 1, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_2288710 : Nat := 118140960795 + 2288710 * 2 ^ 59
def prefixEnd_2288710 : Nat := 4983230072969 + 3 ^ 40 * 2288710 * 2
def baseEnd_2288710 : Nat := 783472205834563763532947

theorem tailTrace_2288710 : CollatzResearch.WordTrace tailWord_2288710 prefixEnd_2288710 783472205834563763532947 := by
  unfold tailWord_2288710
  simp only [CollatzResearch.WordTrace]
  refine ⟨2608628485575063293547487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 55650741025601350262346389 2608628485575063293547487)
  ·
    refine ⟨3912942728362594940321231, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2608628485575063293547487 3912942728362594940321231)
    ·
      refine ⟨5869414092543892410481847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3912942728362594940321231 5869414092543892410481847)
      ·
        refine ⟨8804121138815838615722771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5869414092543892410481847 8804121138815838615722771)
        ·
          refine ⟨13206181708223757923584157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8804121138815838615722771 13206181708223757923584157)
          ·
            refine ⟨4952318140583909221344059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13206181708223757923584157 4952318140583909221344059)
            ·
              refine ⟨7428477210875863832016089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4952318140583909221344059 7428477210875863832016089)
              ·
                refine ⟨5571357908156897874012067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7428477210875863832016089 5571357908156897874012067)
                ·
                  refine ⟨8357036862235346811018101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5571357908156897874012067 8357036862235346811018101)
                  ·
                    refine ⟨783472205834563763532947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8357036862235346811018101 783472205834563763532947)
                    ·
                      rfl

theorem cell22_2288710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_2288710 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2288710 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2288710 prefixEnd_2288710 := by exact prefixLift 2288710
  have htrace : WordTrace (prefixWord ++ tailWord_2288710) baseStart_2288710 baseEnd_2288710 := by
    simpa [prefixWord, tailWord_2288710, baseEnd_2288710] using wordTrace_append hprefix tailTrace_2288710
  have hstable : (prefixWord ++ tailWord_2288710).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288710).length < 2 ^ (prefixWord ++ tailWord_2288710).sum := by decide
  have hdescent : baseEnd_2288710 < baseStart_2288710 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288719 : List Nat := [1, 1, 2, 1, 1, 2, 2, 1, 3, 8]
def baseStart_2288719 : Nat := 118140960795 + 2288719 * 2 ^ 59
def prefixEnd_2288719 : Nat := 4983230072969 + 3 ^ 40 * 2288719 * 2
def baseEnd_2288719 : Nat := 783475286718490740057919

theorem tailTrace_2288719 : CollatzResearch.WordTrace tailWord_2288719 prefixEnd_2288719 783475286718490740057919 := by
  unfold tailWord_2288719
  simp only [CollatzResearch.WordTrace]
  refine ⟨83476439795369419930597211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55650959863579613287064807 83476439795369419930597211)
  ·
    refine ⟨125214659693054129895895817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83476439795369419930597211 125214659693054129895895817)
    ·
      refine ⟨93910994769790597421921863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125214659693054129895895817 93910994769790597421921863)
      ·
        refine ⟨140866492154685896132882795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93910994769790597421921863 140866492154685896132882795)
        ·
          refine ⟨211299738232028844199324193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140866492154685896132882795 211299738232028844199324193)
          ·
            refine ⟨158474803674021633149493145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211299738232028844199324193 158474803674021633149493145)
            ·
              refine ⟨118856102755516224862119859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 158474803674021633149493145 118856102755516224862119859)
              ·
                refine ⟨178284154133274337293179789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 118856102755516224862119859 178284154133274337293179789)
                ·
                  refine ⟨66856557799977876484942421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 178284154133274337293179789 66856557799977876484942421)
                  ·
                    refine ⟨783475286718490740057919, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 66856557799977876484942421 783475286718490740057919)
                    ·
                      rfl

theorem cell22_2288719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 1, 3, 8].length) (baseStart_2288719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2288719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2288719 prefixEnd_2288719 := by exact prefixLift 2288719
  have htrace : WordTrace (prefixWord ++ tailWord_2288719) baseStart_2288719 baseEnd_2288719 := by
    simpa [prefixWord, tailWord_2288719, baseEnd_2288719] using wordTrace_append hprefix tailTrace_2288719
  have hstable : (prefixWord ++ tailWord_2288719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288719).length < 2 ^ (prefixWord ++ tailWord_2288719).sum := by decide
  have hdescent : baseEnd_2288719 < baseStart_2288719 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288751 : List Nat := [1, 1, 2, 1, 3, 3, 1, 5, 5]
def baseStart_2288751 : Nat := 118140960795 + 2288751 * 2 ^ 59
def prefixEnd_2288751 : Nat := 4983230072969 + 3 ^ 40 * 2288751 * 2
def baseEnd_2288751 : Nat := 261162080324151107752607

theorem tailTrace_2288751 : CollatzResearch.WordTrace tailWord_2288751 prefixEnd_2288751 261162080324151107752607 := by
  unfold tailWord_2288751
  simp only [CollatzResearch.WordTrace]
  refine ⟨83477606931253489395762107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55651737954168992930508071 83477606931253489395762107)
  ·
    refine ⟨125216410396880234093643161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83477606931253489395762107 125216410396880234093643161)
    ·
      refine ⟨93912307797660175570232371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125216410396880234093643161 93912307797660175570232371)
      ·
        refine ⟨140868461696490263355348557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93912307797660175570232371 140868461696490263355348557)
        ·
          refine ⟨52825673136183848758255709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140868461696490263355348557 52825673136183848758255709)
          ·
            refine ⟨19809627426068943284345891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52825673136183848758255709 19809627426068943284345891)
            ·
              refine ⟨29714441139103414926518837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19809627426068943284345891 29714441139103414926518837)
              ·
                refine ⟨2785728856790945149361141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29714441139103414926518837 2785728856790945149361141)
                ·
                  refine ⟨261162080324151107752607, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2785728856790945149361141 261162080324151107752607)
                  ·
                    rfl

theorem cell22_2288751_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 5].length) (baseStart_2288751 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2288751 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2288751 prefixEnd_2288751 := by exact prefixLift 2288751
  have htrace : WordTrace (prefixWord ++ tailWord_2288751) baseStart_2288751 baseEnd_2288751 := by
    simpa [prefixWord, tailWord_2288751, baseEnd_2288751] using wordTrace_append hprefix tailTrace_2288751
  have hstable : (prefixWord ++ tailWord_2288751).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288751).length < 2 ^ (prefixWord ++ tailWord_2288751).sum := by decide
  have hdescent : baseEnd_2288751 < baseStart_2288751 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288751) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288772 : List Nat := [2, 3, 2, 1, 2, 3, 2, 3, 1, 3]
def baseStart_2288772 : Nat := 118140960795 + 2288772 * 2 ^ 59
def prefixEnd_2288772 : Nat := 4983230072969 + 3 ^ 40 * 2288772 * 2
def baseEnd_2288772 : Nat := 783493429701616268482757

theorem tailTrace_2288772 : CollatzResearch.WordTrace tailWord_2288772 prefixEnd_2288772 783493429701616268482757 := by
  unfold tailWord_2288772
  simp only [CollatzResearch.WordTrace]
  refine ⟨41739186432088704991138285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55652248576118273321517713 41739186432088704991138285)
  ·
    refine ⟨15652194912033264371676857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41739186432088704991138285 15652194912033264371676857)
    ·
      refine ⟨11739146184024948278757643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15652194912033264371676857 11739146184024948278757643)
      ·
        refine ⟨17608719276037422418136465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11739146184024948278757643 17608719276037422418136465)
        ·
          refine ⟨13206539457028066813602349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17608719276037422418136465 13206539457028066813602349)
          ·
            refine ⟨4952452296385525055100881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13206539457028066813602349 4952452296385525055100881)
            ·
              refine ⟨3714339222289143791325661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4952452296385525055100881 3714339222289143791325661)
              ·
                refine ⟨1392877208358428921747123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3714339222289143791325661 1392877208358428921747123)
                ·
                  refine ⟨2089315812537643382620685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1392877208358428921747123 2089315812537643382620685)
                  ·
                    refine ⟨783493429701616268482757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2089315812537643382620685 783493429701616268482757)
                    ·
                      rfl

theorem cell22_2288772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 3, 2, 3, 1, 3].length) (baseStart_2288772 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2288772 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2288772 prefixEnd_2288772 := by exact prefixLift 2288772
  have htrace : WordTrace (prefixWord ++ tailWord_2288772) baseStart_2288772 baseEnd_2288772 := by
    simpa [prefixWord, tailWord_2288772, baseEnd_2288772] using wordTrace_append hprefix tailTrace_2288772
  have hstable : (prefixWord ++ tailWord_2288772).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288772).length < 2 ^ (prefixWord ++ tailWord_2288772).sum := by decide
  have hdescent : baseEnd_2288772 < baseStart_2288772 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288802 : List Nat := [3, 3, 1, 3, 2, 1, 3, 1, 5]
def baseStart_2288802 : Nat := 118140960795 + 2288802 * 2 ^ 59
def prefixEnd_2288802 : Nat := 4983230072969 + 3 ^ 40 * 2288802 * 2
def baseEnd_2288802 : Nat := 261167899771568730077555

theorem tailTrace_2288802 : CollatzResearch.WordTrace tailWord_2288802 prefixEnd_2288802 261167899771568730077555 := by
  unfold tailWord_2288802
  simp only [CollatzResearch.WordTrace]
  refine ⟨20869866763517181276467165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55652978036045816737245773 20869866763517181276467165)
  ·
    refine ⟨7826200036318942978675187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20869866763517181276467165 7826200036318942978675187)
    ·
      refine ⟨11739300054478414468012781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7826200036318942978675187 11739300054478414468012781)
      ·
        refine ⟨4402237520429405425504793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11739300054478414468012781 4402237520429405425504793)
        ·
          refine ⟨3301678140322054069128595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4402237520429405425504793 3301678140322054069128595)
          ·
            refine ⟨4952517210483081103692893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3301678140322054069128595 4952517210483081103692893)
            ·
              refine ⟨1857193953931155413884835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4952517210483081103692893 1857193953931155413884835)
              ·
                refine ⟨2785790930896733120827253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1857193953931155413884835 2785790930896733120827253)
                ·
                  refine ⟨261167899771568730077555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2785790930896733120827253 261167899771568730077555)
                  ·
                    rfl

theorem cell22_2288802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 5].length) (baseStart_2288802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2288802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2288802 prefixEnd_2288802 := by exact prefixLift 2288802
  have htrace : WordTrace (prefixWord ++ tailWord_2288802) baseStart_2288802 baseEnd_2288802 := by
    simpa [prefixWord, tailWord_2288802, baseEnd_2288802] using wordTrace_append hprefix tailTrace_2288802
  have hstable : (prefixWord ++ tailWord_2288802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288802).length < 2 ^ (prefixWord ++ tailWord_2288802).sum := by decide
  have hdescent : baseEnd_2288802 < baseStart_2288802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288907 : List Nat := [1, 1, 1, 1, 5, 4, 1, 4, 1, 3]
def baseStart_2288907 : Nat := 118140960795 + 2288907 * 2 ^ 59
def prefixEnd_2288907 : Nat := 4983230072969 + 3 ^ 40 * 2288907 * 2
def baseEnd_2288907 : Nat := 783539642960520916357343

theorem tailTrace_2288907 : CollatzResearch.WordTrace tailWord_2288907 prefixEnd_2288907 783539642960520916357343 := by
  unfold tailWord_2288907
  simp only [CollatzResearch.WordTrace]
  refine ⟨83483296718688328038440975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55655531145792218692293983 83483296718688328038440975)
  ·
    refine ⟨125224945078032492057661463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83483296718688328038440975 125224945078032492057661463)
    ·
      refine ⟨187837417617048738086492195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125224945078032492057661463 187837417617048738086492195)
      ·
        refine ⟨281756126425573107129738293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187837417617048738086492195 281756126425573107129738293)
        ·
          refine ⟨26414636852397478793412965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 281756126425573107129738293 26414636852397478793412965)
          ·
            refine ⟨4952744409824527273764931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26414636852397478793412965 4952744409824527273764931)
            ·
              refine ⟨7429116614736790910647397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4952744409824527273764931 7429116614736790910647397)
              ·
                refine ⟨1392959365263148295746387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7429116614736790910647397 1392959365263148295746387)
                ·
                  refine ⟨2089439047894722443619581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1392959365263148295746387 2089439047894722443619581)
                  ·
                    refine ⟨783539642960520916357343, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2089439047894722443619581 783539642960520916357343)
                    ·
                      rfl

theorem cell22_2288907_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 4, 1, 4, 1, 3].length) (baseStart_2288907 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2288907 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2288907 prefixEnd_2288907 := by exact prefixLift 2288907
  have htrace : WordTrace (prefixWord ++ tailWord_2288907) baseStart_2288907 baseEnd_2288907 := by
    simpa [prefixWord, tailWord_2288907, baseEnd_2288907] using wordTrace_append hprefix tailTrace_2288907
  have hstable : (prefixWord ++ tailWord_2288907).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288907).length < 2 ^ (prefixWord ++ tailWord_2288907).sum := by decide
  have hdescent : baseEnd_2288907 < baseStart_2288907 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288907) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288941 : List Nat := [1, 5, 3, 1, 1, 2, 2, 3, 1, 3]
def baseStart_2288941 : Nat := 118140960795 + 2288941 * 2 ^ 59
def prefixEnd_2288941 : Nat := 4983230072969 + 3 ^ 40 * 2288941 * 2
def baseEnd_2288941 : Nat := 783551281855356161007239

theorem tailTrace_2288941 : CollatzResearch.WordTrace tailWord_2288941 prefixEnd_2288941 783551281855356161007239 := by
  unfold tailWord_2288941
  simp only [CollatzResearch.WordTrace]
  refine ⟨83484536800565151845178677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55656357867043434563452451 83484536800565151845178677)
  ·
    refine ⟨7826675325052982985485501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 83484536800565151845178677 7826675325052982985485501)
    ·
      refine ⟨2935003246894868619557063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7826675325052982985485501 2935003246894868619557063)
      ·
        refine ⟨4402504870342302929335595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2935003246894868619557063 4402504870342302929335595)
        ·
          refine ⟨6603757305513454394003393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4402504870342302929335595 6603757305513454394003393)
          ·
            refine ⟨4952817979135090795502545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6603757305513454394003393 4952817979135090795502545)
            ·
              refine ⟨3714613484351318096626909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4952817979135090795502545 3714613484351318096626909)
              ·
                refine ⟨1392980056631744286235091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3714613484351318096626909 1392980056631744286235091)
                ·
                  refine ⟨2089470084947616429352637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1392980056631744286235091 2089470084947616429352637)
                  ·
                    refine ⟨783551281855356161007239, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2089470084947616429352637 783551281855356161007239)
                    ·
                      rfl

theorem cell22_2288941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 2, 2, 3, 1, 3].length) (baseStart_2288941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2288941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2288941 prefixEnd_2288941 := by exact prefixLift 2288941
  have htrace : WordTrace (prefixWord ++ tailWord_2288941) baseStart_2288941 baseEnd_2288941 := by
    simpa [prefixWord, tailWord_2288941, baseEnd_2288941] using wordTrace_append hprefix tailTrace_2288941
  have hstable : (prefixWord ++ tailWord_2288941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288941).length < 2 ^ (prefixWord ++ tailWord_2288941).sum := by decide
  have hdescent : baseEnd_2288941 < baseStart_2288941 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2288999 : List Nat := [1, 1, 5, 1, 4, 2, 1, 3, 4]
def baseStart_2288999 : Nat := 118140960795 + 2288999 * 2 ^ 59
def prefixEnd_2288999 : Nat := 4983230072969 + 3 ^ 40 * 2288999 * 2
def baseEnd_2288999 : Nat := 261190378813554447685687

theorem tailTrace_2288999 : CollatzResearch.WordTrace tailWord_2288999 prefixEnd_2288999 261190378813554447685687 := by
  unfold tailWord_2288999
  simp only [CollatzResearch.WordTrace]
  refine ⟨83486652234355027750790051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55657768156236685167193367 83486652234355027750790051)
  ·
    refine ⟨125229978351532541626185077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83486652234355027750790051 125229978351532541626185077)
    ·
      refine ⟨11740310470456175777454851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 125229978351532541626185077 11740310470456175777454851)
      ·
        refine ⟨17610465705684263666182277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11740310470456175777454851 17610465705684263666182277)
        ·
          refine ⟨3301962319815799437409177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17610465705684263666182277 3301962319815799437409177)
          ·
            refine ⟨2476471739861849578056883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3301962319815799437409177 2476471739861849578056883)
            ·
              refine ⟨3714707609792774367085325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2476471739861849578056883 3714707609792774367085325)
              ·
                refine ⟨1393015353672290387656997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3714707609792774367085325 1393015353672290387656997)
                ·
                  refine ⟨261190378813554447685687, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1393015353672290387656997 261190378813554447685687)
                  ·
                    rfl

theorem cell22_2288999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 2, 1, 3, 4].length) (baseStart_2288999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2288999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2288999 prefixEnd_2288999 := by exact prefixLift 2288999
  have htrace : WordTrace (prefixWord ++ tailWord_2288999) baseStart_2288999 baseEnd_2288999 := by
    simpa [prefixWord, tailWord_2288999, baseEnd_2288999] using wordTrace_append hprefix tailTrace_2288999
  have hstable : (prefixWord ++ tailWord_2288999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2288999).length < 2 ^ (prefixWord ++ tailWord_2288999).sum := by decide
  have hdescent : baseEnd_2288999 < baseStart_2288999 := by decide
  rcases family_descends (prefixWord ++ tailWord_2288999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289085 : List Nat := [1, 4, 1, 2, 2, 1, 1, 1, 5, 4]
def baseStart_2289085 : Nat := 118140960795 + 2289085 * 2 ^ 59
def prefixEnd_2289085 : Nat := 4983230072969 + 3 ^ 40 * 2289085 * 2
def baseEnd_2289085 : Nat := 783600575998187785406797

theorem tailTrace_2289085 : CollatzResearch.WordTrace tailWord_2289085 prefixEnd_2289085 783600575998187785406797 := by
  unfold tailWord_2289085
  simp only [CollatzResearch.WordTrace]
  refine ⟨83489788912043464438420709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55659859274695642958947139 83489788912043464438420709)
  ·
    refine ⟨15654335421008149582203883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83489788912043464438420709 15654335421008149582203883)
    ·
      refine ⟨23481503131512224373305825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15654335421008149582203883 23481503131512224373305825)
      ·
        refine ⟨17611127348634168279979369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23481503131512224373305825 17611127348634168279979369)
        ·
          refine ⟨13208345511475626209984527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17611127348634168279979369 13208345511475626209984527)
          ·
            refine ⟨19812518267213439314976791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13208345511475626209984527 19812518267213439314976791)
            ·
              refine ⟨29718777400820158972465187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19812518267213439314976791 29718777400820158972465187)
              ·
                refine ⟨44578166101230238458697781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29718777400820158972465187 44578166101230238458697781)
                ·
                  refine ⟨4179203071990334855502917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 44578166101230238458697781 4179203071990334855502917)
                  ·
                    refine ⟨783600575998187785406797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4179203071990334855502917 783600575998187785406797)
                    ·
                      rfl

theorem cell22_2289085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 1, 1, 5, 4].length) (baseStart_2289085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2289085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2289085 prefixEnd_2289085 := by exact prefixLift 2289085
  have htrace : WordTrace (prefixWord ++ tailWord_2289085) baseStart_2289085 baseEnd_2289085 := by
    simpa [prefixWord, tailWord_2289085, baseEnd_2289085] using wordTrace_append hprefix tailTrace_2289085
  have hstable : (prefixWord ++ tailWord_2289085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289085).length < 2 ^ (prefixWord ++ tailWord_2289085).sum := by decide
  have hdescent : baseEnd_2289085 < baseStart_2289085 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289100 : List Nat := [2, 2, 1, 4, 2, 1, 1, 1, 8]
def baseStart_2289100 : Nat := 118140960795 + 2289100 * 2 ^ 59
def prefixEnd_2289100 : Nat := 4983230072969 + 3 ^ 40 * 2289100 * 2
def baseEnd_2289100 : Nat := 261201903601577582093917

theorem tailTrace_2289100 : CollatzResearch.WordTrace tailWord_2289100 prefixEnd_2289100 261201903601577582093917 := by
  unfold tailWord_2289100
  simp only [CollatzResearch.WordTrace]
  refine ⟨41745168003494561000108377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55660224004659414666811169 41745168003494561000108377)
  ·
    refine ⟨31308876002620920750081283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41745168003494561000108377 31308876002620920750081283)
    ·
      refine ⟨46963314003931381125121925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31308876002620920750081283 46963314003931381125121925)
      ·
        refine ⟨8805621375737133960960361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 46963314003931381125121925 8805621375737133960960361)
        ·
          refine ⟨6604216031802850470720271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8805621375737133960960361 6604216031802850470720271)
          ·
            refine ⟨9906324047704275706080407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6604216031802850470720271 9906324047704275706080407)
            ·
              refine ⟨14859486071556413559120611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9906324047704275706080407 14859486071556413559120611)
              ·
                refine ⟨22289229107334620338680917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14859486071556413559120611 22289229107334620338680917)
                ·
                  refine ⟨261201903601577582093917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22289229107334620338680917 261201903601577582093917)
                  ·
                    rfl

theorem cell22_2289100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 1, 1, 1, 8].length) (baseStart_2289100 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2289100 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2289100 prefixEnd_2289100 := by exact prefixLift 2289100
  have htrace : WordTrace (prefixWord ++ tailWord_2289100) baseStart_2289100 baseEnd_2289100 := by
    simpa [prefixWord, tailWord_2289100, baseEnd_2289100] using wordTrace_append hprefix tailTrace_2289100
  have hstable : (prefixWord ++ tailWord_2289100).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289100).length < 2 ^ (prefixWord ++ tailWord_2289100).sum := by decide
  have hdescent : baseEnd_2289100 < baseStart_2289100 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289115 : List Nat := [1, 1, 1, 1, 1, 1, 1, 2, 10, 3]
def baseStart_2289115 : Nat := 118140960795 + 2289115 * 2 ^ 59
def prefixEnd_2289115 : Nat := 4983230072969 + 3 ^ 40 * 2289115 * 2
def baseEnd_2289115 : Nat := 783610845611277707156705

theorem tailTrace_2289115 : CollatzResearch.WordTrace tailWord_2289115 prefixEnd_2289115 783610845611277707156705 := by
  unfold tailWord_2289115
  simp only [CollatzResearch.WordTrace]
  refine ⟨83490883101934779562012799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55660588734623186374675199 83490883101934779562012799)
  ·
    refine ⟨125236324652902169343019199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83490883101934779562012799 125236324652902169343019199)
    ·
      refine ⟨187854486979353254014528799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125236324652902169343019199 187854486979353254014528799)
      ·
        refine ⟨281781730469029881021793199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187854486979353254014528799 281781730469029881021793199)
        ·
          refine ⟨422672595703544821532689799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281781730469029881021793199 422672595703544821532689799)
          ·
            refine ⟨634008893555317232299034699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 422672595703544821532689799 634008893555317232299034699)
            ·
              refine ⟨951013340332975848448552049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 634008893555317232299034699 951013340332975848448552049)
              ·
                refine ⟨713260005249731886336414037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 951013340332975848448552049 713260005249731886336414037)
                ·
                  refine ⟨2089628921630073885751213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 713260005249731886336414037 2089628921630073885751213)
                  ·
                    refine ⟨783610845611277707156705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2089628921630073885751213 783610845611277707156705)
                    ·
                      rfl

theorem cell22_2289115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 10, 3].length) (baseStart_2289115 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2289115 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2289115 prefixEnd_2289115 := by exact prefixLift 2289115
  have htrace : WordTrace (prefixWord ++ tailWord_2289115) baseStart_2289115 baseEnd_2289115 := by
    simpa [prefixWord, tailWord_2289115, baseEnd_2289115] using wordTrace_append hprefix tailTrace_2289115
  have hstable : (prefixWord ++ tailWord_2289115).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289115).length < 2 ^ (prefixWord ++ tailWord_2289115).sum := by decide
  have hdescent : baseEnd_2289115 < baseStart_2289115 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289132 : List Nat := [2, 2, 1, 1, 2, 1, 2, 6, 2, 3]
def baseStart_2289132 : Nat := 118140960795 + 2289132 * 2 ^ 59
def prefixEnd_2289132 : Nat := 4983230072969 + 3 ^ 40 * 2289132 * 2
def baseEnd_2289132 : Nat := 783616665058695329481653

theorem tailTrace_2289132 : CollatzResearch.WordTrace tailWord_2289132 prefixEnd_2289132 783616665058695329481653 := by
  unfold tailWord_2289132
  simp only [CollatzResearch.WordTrace]
  refine ⟨41745751571436595732690825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55661002095248794310254433 41745751571436595732690825)
  ·
    refine ⟨31309313678577446799518119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41745751571436595732690825 31309313678577446799518119)
    ·
      refine ⟨46963970517866170199277179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31309313678577446799518119 46963970517866170199277179)
      ·
        refine ⟨70445955776799255298915769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46963970517866170199277179 70445955776799255298915769)
        ·
          refine ⟨52834466832599441474186827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70445955776799255298915769 52834466832599441474186827)
          ·
            refine ⟨79251700248899162211280241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52834466832599441474186827 79251700248899162211280241)
            ·
              refine ⟨59438775186674371658460181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79251700248899162211280241 59438775186674371658460181)
              ·
                refine ⟨2786192586875361171490321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 59438775186674371658460181 2786192586875361171490321)
                ·
                  refine ⟨2089644440156520878617741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2786192586875361171490321 2089644440156520878617741)
                  ·
                    refine ⟨783616665058695329481653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2089644440156520878617741 783616665058695329481653)
                    ·
                      rfl

theorem cell22_2289132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 2, 3].length) (baseStart_2289132 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2289132 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2289132 prefixEnd_2289132 := by exact prefixLift 2289132
  have htrace : WordTrace (prefixWord ++ tailWord_2289132) baseStart_2289132 baseEnd_2289132 := by
    simpa [prefixWord, tailWord_2289132, baseEnd_2289132] using wordTrace_append hprefix tailTrace_2289132
  have hstable : (prefixWord ++ tailWord_2289132).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289132).length < 2 ^ (prefixWord ++ tailWord_2289132).sum := by decide
  have hdescent : baseEnd_2289132 < baseStart_2289132 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289162 : List Nat := [3, 1, 2, 2, 2, 2, 4, 6]
def baseStart_2289162 : Nat := 118140960795 + 2289162 * 2 ^ 59
def prefixEnd_2289162 : Nat := 4983230072969 + 3 ^ 40 * 2289162 * 2
def baseEnd_2289162 : Nat := 87069659407976139025729

theorem tailTrace_2289162 : CollatzResearch.WordTrace tailWord_2289162 prefixEnd_2289162 87069659407976139025729 := by
  unfold tailWord_2289162
  simp only [CollatzResearch.WordTrace]
  refine ⟨20873149333191126647243435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55661731555176337725982493 20873149333191126647243435)
  ·
    refine ⟨31309723999786689970865153, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20873149333191126647243435 31309723999786689970865153)
    ·
      refine ⟨23482292999840017478148865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31309723999786689970865153 23482292999840017478148865)
      ·
        refine ⟨17611719749880013108611649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23482292999840017478148865 17611719749880013108611649)
        ·
          refine ⟨13208789812410009831458737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17611719749880013108611649 13208789812410009831458737)
          ·
            refine ⟨9906592359307507373594053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13208789812410009831458737 9906592359307507373594053)
            ·
              refine ⟨1857486067370157632548885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9906592359307507373594053 1857486067370157632548885)
              ·
                refine ⟨87069659407976139025729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1857486067370157632548885 87069659407976139025729)
                ·
                  rfl

theorem cell22_2289162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 2, 4, 6].length) (baseStart_2289162 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2289162 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2289162 prefixEnd_2289162 := by exact prefixLift 2289162
  have htrace : WordTrace (prefixWord ++ tailWord_2289162) baseStart_2289162 baseEnd_2289162 := by
    simpa [prefixWord, tailWord_2289162, baseEnd_2289162] using wordTrace_append hprefix tailTrace_2289162
  have hstable : (prefixWord ++ tailWord_2289162).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289162).length < 2 ^ (prefixWord ++ tailWord_2289162).sum := by decide
  have hdescent : baseEnd_2289162 < baseStart_2289162 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289207 : List Nat := [1, 1, 3, 1, 2, 5, 1, 3, 5]
def baseStart_2289207 : Nat := 118140960795 + 2289207 * 2 ^ 59
def prefixEnd_2289207 : Nat := 4983230072969 + 3 ^ 40 * 2289207 * 2
def baseEnd_2289207 : Nat := 261214113030473377952141

theorem tailTrace_2289207 : CollatzResearch.WordTrace tailWord_2289207 prefixEnd_2289207 261214113030473377952141 := by
  unfold tailWord_2289207
  simp only [CollatzResearch.WordTrace]
  refine ⟨83494238617601479274361875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55662825745067652849574583 83494238617601479274361875)
  ·
    refine ⟨125241357926402218911542813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83494238617601479274361875 125241357926402218911542813)
    ·
      refine ⟨46965509222400832091828555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125241357926402218911542813 46965509222400832091828555)
      ·
        refine ⟨70448263833601248137742833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46965509222400832091828555 70448263833601248137742833)
        ·
          refine ⟨52836197875200936103307125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70448263833601248137742833 52836197875200936103307125)
          ·
            refine ⟨4953393550800087759685043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 52836197875200936103307125 4953393550800087759685043)
            ·
              refine ⟨7430090326200131639527565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4953393550800087759685043 7430090326200131639527565)
              ·
                refine ⟨2786283872325049364822837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7430090326200131639527565 2786283872325049364822837)
                ·
                  refine ⟨261214113030473377952141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2786283872325049364822837 261214113030473377952141)
                  ·
                    rfl

theorem cell22_2289207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 5].length) (baseStart_2289207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2289207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2289207 prefixEnd_2289207 := by exact prefixLift 2289207
  have htrace : WordTrace (prefixWord ++ tailWord_2289207) baseStart_2289207 baseEnd_2289207 := by
    simpa [prefixWord, tailWord_2289207, baseEnd_2289207] using wordTrace_append hprefix tailTrace_2289207
  have hstable : (prefixWord ++ tailWord_2289207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289207).length < 2 ^ (prefixWord ++ tailWord_2289207).sum := by decide
  have hdescent : baseEnd_2289207 < baseStart_2289207 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289245 : List Nat := [1, 4, 4, 2, 1, 1, 1, 4, 1, 3]
def baseStart_2289245 : Nat := 118140960795 + 2289245 * 2 ^ 59
def prefixEnd_2289245 : Nat := 4983230072969 + 3 ^ 40 * 2289245 * 2
def baseEnd_2289245 : Nat := 783655347268000701406307

theorem tailTrace_2289245 : CollatzResearch.WordTrace tailWord_2289245 prefixEnd_2289245 783655347268000701406307 := by
  unfold tailWord_2289245
  simp only [CollatzResearch.WordTrace]
  refine ⟨83495624591463811764245189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55663749727642541176163459 83495624591463811764245189)
  ·
    refine ⟨15655429610899464705795973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83495624591463811764245189 15655429610899464705795973)
    ·
      refine ⟨2935393052043649632336745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15655429610899464705795973 2935393052043649632336745)
      ·
        refine ⟨2201544789032737224252559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2935393052043649632336745 2201544789032737224252559)
        ·
          refine ⟨3302317183549105836378839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2201544789032737224252559 3302317183549105836378839)
          ·
            refine ⟨4953475775323658754568259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3302317183549105836378839 4953475775323658754568259)
            ·
              refine ⟨7430213662985488131852389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4953475775323658754568259 7430213662985488131852389)
              ·
                refine ⟨1393165061809779024722323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7430213662985488131852389 1393165061809779024722323)
                ·
                  refine ⟨2089747592714668537083485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1393165061809779024722323 2089747592714668537083485)
                  ·
                    refine ⟨783655347268000701406307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2089747592714668537083485 783655347268000701406307)
                    ·
                      rfl

theorem cell22_2289245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 1, 1, 1, 4, 1, 3].length) (baseStart_2289245 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2289245 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2289245 prefixEnd_2289245 := by exact prefixLift 2289245
  have htrace : WordTrace (prefixWord ++ tailWord_2289245) baseStart_2289245 baseEnd_2289245 := by
    simpa [prefixWord, tailWord_2289245, baseEnd_2289245] using wordTrace_append hprefix tailTrace_2289245
  have hstable : (prefixWord ++ tailWord_2289245).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289245).length < 2 ^ (prefixWord ++ tailWord_2289245).sum := by decide
  have hdescent : baseEnd_2289245 < baseStart_2289245 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289269 : List Nat := [1, 3, 4, 2, 1, 2, 1, 2, 6]
def baseStart_2289269 : Nat := 118140960795 + 2289269 * 2 ^ 59
def prefixEnd_2289269 : Nat := 4983230072969 + 3 ^ 40 * 2289269 * 2
def baseEnd_2289269 : Nat := 261221187652824212935411

theorem tailTrace_2289269 : CollatzResearch.WordTrace tailWord_2289269 prefixEnd_2289269 261221187652824212935411 := by
  unfold tailWord_2289269
  simp only [CollatzResearch.WordTrace]
  refine ⟨83496499943376863863118861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55664333295584575908745907 83496499943376863863118861)
  ·
    refine ⟨31311187478766323948669573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83496499943376863863118861 31311187478766323948669573)
    ·
      refine ⟨5870847652268685740375545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31311187478766323948669573 5870847652268685740375545)
      ·
        refine ⟨4403135739201514305281659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5870847652268685740375545 4403135739201514305281659)
        ·
          refine ⟨6604703608802271457922489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4403135739201514305281659 6604703608802271457922489)
          ·
            refine ⟨4953527706601703593441867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6604703608802271457922489 4953527706601703593441867)
            ·
              refine ⟨7430291559902555390162801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4953527706601703593441867 7430291559902555390162801)
              ·
                refine ⟨5572718669926916542622101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7430291559902555390162801 5572718669926916542622101)
                ·
                  refine ⟨261221187652824212935411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5572718669926916542622101 261221187652824212935411)
                  ·
                    rfl

theorem cell22_2289269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 1, 2, 6].length) (baseStart_2289269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2289269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2289269 prefixEnd_2289269 := by exact prefixLift 2289269
  have htrace : WordTrace (prefixWord ++ tailWord_2289269) baseStart_2289269 baseEnd_2289269 := by
    simpa [prefixWord, tailWord_2289269, baseEnd_2289269] using wordTrace_append hprefix tailTrace_2289269
  have hstable : (prefixWord ++ tailWord_2289269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289269).length < 2 ^ (prefixWord ++ tailWord_2289269).sum := by decide
  have hdescent : baseEnd_2289269 < baseStart_2289269 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289387 : List Nat := [1, 1, 1, 1, 2, 4, 2, 4, 6]
def baseStart_2289387 : Nat := 118140960795 + 2289387 * 2 ^ 59
def prefixEnd_2289387 : Nat := 4983230072969 + 3 ^ 40 * 2289387 * 2
def baseEnd_2289387 : Nat := 261234652256653221451957

theorem tailTrace_2289387 : CollatzResearch.WordTrace tailWord_2289387 prefixEnd_2289387 261234652256653221451957 := by
  unfold tailWord_2289387
  simp only [CollatzResearch.WordTrace]
  refine ⟨83500803756949370015914415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55667202504632913343942943 83500803756949370015914415)
  ·
    refine ⟨125251205635424055023871623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83500803756949370015914415 125251205635424055023871623)
    ·
      refine ⟨187876808453136082535807435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125251205635424055023871623 187876808453136082535807435)
      ·
        refine ⟨281815212679704123803711153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187876808453136082535807435 281815212679704123803711153)
        ·
          refine ⟨211361409509778092852783365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281815212679704123803711153 211361409509778092852783365)
          ·
            refine ⟨39630264283083392409896881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 211361409509778092852783365 39630264283083392409896881)
            ·
              refine ⟨29722698212312544307422661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39630264283083392409896881 29722698212312544307422661)
              ·
                refine ⟨5573005914808602057641749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29722698212312544307422661 5573005914808602057641749)
                ·
                  refine ⟨261234652256653221451957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5573005914808602057641749 261234652256653221451957)
                  ·
                    rfl

theorem cell22_2289387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 6].length) (baseStart_2289387 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2289387 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2289387 prefixEnd_2289387 := by exact prefixLift 2289387
  have htrace : WordTrace (prefixWord ++ tailWord_2289387) baseStart_2289387 baseEnd_2289387 := by
    simpa [prefixWord, tailWord_2289387, baseEnd_2289387] using wordTrace_append hprefix tailTrace_2289387
  have hstable : (prefixWord ++ tailWord_2289387).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289387).length < 2 ^ (prefixWord ++ tailWord_2289387).sum := by decide
  have hdescent : baseEnd_2289387 < baseStart_2289387 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289417 : List Nat := [1, 2, 1, 1, 3, 2, 1, 2, 3, 6]
def baseStart_2289417 : Nat := 118140960795 + 2289417 * 2 ^ 59
def prefixEnd_2289417 : Nat := 4983230072969 + 3 ^ 40 * 2289417 * 2
def baseEnd_2289417 : Nat := 783714226383049586105779

theorem tailTrace_2289417 : CollatzResearch.WordTrace tailWord_2289417 prefixEnd_2289417 783714226383049586105779 := by
  unfold tailWord_2289417
  simp only [CollatzResearch.WordTrace]
  refine ⟨83501897946840685139506505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55667931964560456759671003 83501897946840685139506505)
  ·
    refine ⟨62626423460130513854629879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83501897946840685139506505 62626423460130513854629879)
    ·
      refine ⟨93939635190195770781944819, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62626423460130513854629879 93939635190195770781944819)
      ·
        refine ⟨140909452785293656172917229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93939635190195770781944819 140909452785293656172917229)
        ·
          refine ⟨52841044794485121064843961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 140909452785293656172917229 52841044794485121064843961)
          ·
            refine ⟨39630783595863840798632971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52841044794485121064843961 39630783595863840798632971)
            ·
              refine ⟨59446175393795761197949457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 39630783595863840798632971 59446175393795761197949457)
              ·
                refine ⟨44584631545346820898462093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 59446175393795761197949457 44584631545346820898462093)
                ·
                  refine ⟨16719236829505057836923285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 44584631545346820898462093 16719236829505057836923285)
                  ·
                    refine ⟨783714226383049586105779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16719236829505057836923285 783714226383049586105779)
                    ·
                      rfl

theorem cell22_2289417_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 1, 2, 3, 6].length) (baseStart_2289417 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2289417 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2289417 prefixEnd_2289417 := by exact prefixLift 2289417
  have htrace : WordTrace (prefixWord ++ tailWord_2289417) baseStart_2289417 baseEnd_2289417 := by
    simpa [prefixWord, tailWord_2289417, baseEnd_2289417] using wordTrace_append hprefix tailTrace_2289417
  have hstable : (prefixWord ++ tailWord_2289417).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289417).length < 2 ^ (prefixWord ++ tailWord_2289417).sum := by decide
  have hdescent : baseEnd_2289417 < baseStart_2289417 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289417) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289419 : List Nat := [1, 1, 1, 1, 5, 1, 2, 3, 4, 3]
def baseStart_2289419 : Nat := 118140960795 + 2289419 * 2 ^ 59
def prefixEnd_2289419 : Nat := 4983230072969 + 3 ^ 40 * 2289419 * 2
def baseEnd_2289419 : Nat := 783714911023922247555773

theorem tailTrace_2289419 : CollatzResearch.WordTrace tailWord_2289419 prefixEnd_2289419 783714911023922247555773 := by
  unfold tailWord_2289419
  simp only [CollatzResearch.WordTrace]
  refine ⟨83501970892833439481079311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55667980595222292987386207 83501970892833439481079311)
  ·
    refine ⟨125252956339250159221618967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83501970892833439481079311 125252956339250159221618967)
    ·
      refine ⟨187879434508875238832428451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125252956339250159221618967 187879434508875238832428451)
      ·
        refine ⟨281819151763312858248642677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187879434508875238832428451 281819151763312858248642677)
        ·
          refine ⟨26420545477810580460810251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 281819151763312858248642677 26420545477810580460810251)
          ·
            refine ⟨39630818216715870691215377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 26420545477810580460810251 39630818216715870691215377)
            ·
              refine ⟨29723113662536903018411533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 39630818216715870691215377 29723113662536903018411533)
              ·
                refine ⟨11146167623451338631904325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29723113662536903018411533 11146167623451338631904325)
                ·
                  refine ⟨2089906429397125993482061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11146167623451338631904325 2089906429397125993482061)
                  ·
                    refine ⟨783714911023922247555773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2089906429397125993482061 783714911023922247555773)
                    ·
                      rfl

theorem cell22_2289419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 2, 3, 4, 3].length) (baseStart_2289419 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2289419 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2289419 prefixEnd_2289419 := by exact prefixLift 2289419
  have htrace : WordTrace (prefixWord ++ tailWord_2289419) baseStart_2289419 baseEnd_2289419 := by
    simpa [prefixWord, tailWord_2289419, baseEnd_2289419] using wordTrace_append hprefix tailTrace_2289419
  have hstable : (prefixWord ++ tailWord_2289419).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289419).length < 2 ^ (prefixWord ++ tailWord_2289419).sum := by decide
  have hdescent : baseEnd_2289419 < baseStart_2289419 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289436 : List Nat := [2, 2, 3, 1, 1, 2, 1, 5, 2, 3]
def baseStart_2289436 : Nat := 118140960795 + 2289436 * 2 ^ 59
def prefixEnd_2289436 : Nat := 4983230072969 + 3 ^ 40 * 2289436 * 2
def baseEnd_2289436 : Nat := 783720730471339869880721

theorem tailTrace_2289436 : CollatzResearch.WordTrace tailWord_2289436 prefixEnd_2289436 783720730471339869880721 := by
  unfold tailWord_2289436
  simp only [CollatzResearch.WordTrace]
  refine ⟨41751295466885925692224081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55668393955847900922965441 41751295466885925692224081)
  ·
    refine ⟨31313471600164444269168061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41751295466885925692224081 31313471600164444269168061)
    ·
      refine ⟨11742551850061666600938023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31313471600164444269168061 11742551850061666600938023)
      ·
        refine ⟨17613827775092499901407035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11742551850061666600938023 17613827775092499901407035)
        ·
          refine ⟨26420741662638749852110553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17613827775092499901407035 26420741662638749852110553)
          ·
            refine ⟨19815556246979062389082915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26420741662638749852110553 19815556246979062389082915)
            ·
              refine ⟨29723334370468593583624373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19815556246979062389082915 29723334370468593583624373)
              ·
                refine ⟨2786562597231430648464785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 29723334370468593583624373 2786562597231430648464785)
                ·
                  refine ⟨2089921947923572986348589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2786562597231430648464785 2089921947923572986348589)
                  ·
                    refine ⟨783720730471339869880721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2089921947923572986348589 783720730471339869880721)
                    ·
                      rfl

theorem cell22_2289436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 1, 5, 2, 3].length) (baseStart_2289436 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2289436 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2289436 prefixEnd_2289436 := by exact prefixLift 2289436
  have htrace : WordTrace (prefixWord ++ tailWord_2289436) baseStart_2289436 baseEnd_2289436 := by
    simpa [prefixWord, tailWord_2289436, baseEnd_2289436] using wordTrace_append hprefix tailTrace_2289436
  have hstable : (prefixWord ++ tailWord_2289436).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289436).length < 2 ^ (prefixWord ++ tailWord_2289436).sum := by decide
  have hdescent : baseEnd_2289436 < baseStart_2289436 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289470 : List Nat := [4, 2, 1, 2, 2, 3, 1, 2, 2, 3]
def baseStart_2289470 : Nat := 118140960795 + 2289470 * 2 ^ 59
def prefixEnd_2289470 : Nat := 4983230072969 + 3 ^ 40 * 2289470 * 2
def baseEnd_2289470 : Nat := 783732369366175114530617

theorem tailTrace_2289470 : CollatzResearch.WordTrace tailWord_2289470 prefixEnd_2289470 783732369366175114530617 := by
  unfold tailWord_2289470
  simp only [CollatzResearch.WordTrace]
  refine ⟨10437978876956084398898233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 55669220677099116794123909 10437978876956084398898233)
  ·
    refine ⟨7828484157717063299173675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10437978876956084398898233 7828484157717063299173675)
    ·
      refine ⟨11742726236575594948760513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7828484157717063299173675 11742726236575594948760513)
      ·
        refine ⟨8807044677431696211570385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11742726236575594948760513 8807044677431696211570385)
        ·
          refine ⟨6605283508073772158677789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8807044677431696211570385 6605283508073772158677789)
          ·
            refine ⟨2476981315527664559504171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6605283508073772158677789 2476981315527664559504171)
            ·
              refine ⟨3715471973291496839256257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2476981315527664559504171 3715471973291496839256257)
              ·
                refine ⟨2786603979968622629442193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3715471973291496839256257 2786603979968622629442193)
                ·
                  refine ⟨2089952984976466972081645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2786603979968622629442193 2089952984976466972081645)
                  ·
                    refine ⟨783732369366175114530617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2089952984976466972081645 783732369366175114530617)
                    ·
                      rfl

theorem cell22_2289470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 3, 1, 2, 2, 3].length) (baseStart_2289470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2289470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2289470 prefixEnd_2289470 := by exact prefixLift 2289470
  have htrace : WordTrace (prefixWord ++ tailWord_2289470) baseStart_2289470 baseEnd_2289470 := by
    simpa [prefixWord, tailWord_2289470, baseEnd_2289470] using wordTrace_append hprefix tailTrace_2289470
  have hstable : (prefixWord ++ tailWord_2289470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289470).length < 2 ^ (prefixWord ++ tailWord_2289470).sum := by decide
  have hdescent : baseEnd_2289470 < baseStart_2289470 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289481 : List Nat := [1, 2, 1, 1, 2, 4, 4, 1, 3, 3]
def baseStart_2289481 : Nat := 118140960795 + 2289481 * 2 ^ 59
def prefixEnd_2289481 : Nat := 4983230072969 + 3 ^ 40 * 2289481 * 2
def baseEnd_2289481 : Nat := 783736134890974752505583

theorem tailTrace_2289481 : CollatzResearch.WordTrace tailWord_2289481 prefixEnd_2289481 783736134890974752505583 := by
  unfold tailWord_2289481
  simp only [CollatzResearch.WordTrace]
  refine ⟨83504232218608824069836297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55669488145739216046557531 83504232218608824069836297)
  ·
    refine ⟨62628174163956618052377223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83504232218608824069836297 62628174163956618052377223)
    ·
      refine ⟨93942261245934927078565835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62628174163956618052377223 93942261245934927078565835)
      ·
        refine ⟨140913391868902390617848753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93942261245934927078565835 140913391868902390617848753)
        ·
          refine ⟨105685043901676792963386565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140913391868902390617848753 105685043901676792963386565)
          ·
            refine ⟨19815945731564398680634981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 105685043901676792963386565 19815945731564398680634981)
            ·
              refine ⟨3715489824668324752619059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19815945731564398680634981 3715489824668324752619059)
              ·
                refine ⟨5573234737002487128928589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3715489824668324752619059 5573234737002487128928589)
                ·
                  refine ⟨2089963026375932673348221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5573234737002487128928589 2089963026375932673348221)
                  ·
                    refine ⟨783736134890974752505583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2089963026375932673348221 783736134890974752505583)
                    ·
                      rfl

theorem cell22_2289481_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 4, 4, 1, 3, 3].length) (baseStart_2289481 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2289481 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2289481 prefixEnd_2289481 := by exact prefixLift 2289481
  have htrace : WordTrace (prefixWord ++ tailWord_2289481) baseStart_2289481 baseEnd_2289481 := by
    simpa [prefixWord, tailWord_2289481, baseEnd_2289481] using wordTrace_append hprefix tailTrace_2289481
  have hstable : (prefixWord ++ tailWord_2289481).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289481).length < 2 ^ (prefixWord ++ tailWord_2289481).sum := by decide
  have hdescent : baseEnd_2289481 < baseStart_2289481 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289481) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289500 : List Nat := [2, 2, 4, 2, 3, 1, 2, 6]
def baseStart_2289500 : Nat := 118140960795 + 2289500 * 2 ^ 59
def prefixEnd_2289500 : Nat := 4983230072969 + 3 ^ 40 * 2289500 * 2
def baseEnd_2289500 : Nat := 87082515442140559586725

theorem tailTrace_2289500 : CollatzResearch.WordTrace tailWord_2289500 prefixEnd_2289500 87082515442140559586725 := by
  unfold tailWord_2289500
  simp only [CollatzResearch.WordTrace]
  refine ⟨41752462602769995157388977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55669950137026660209851969 41752462602769995157388977)
  ·
    refine ⟨31314346952077496368041733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41752462602769995157388977 31314346952077496368041733)
    ·
      refine ⟨5871440053514530569007825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 31314346952077496368041733 5871440053514530569007825)
      ·
        refine ⟨4403580040135897926755869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5871440053514530569007825 4403580040135897926755869)
        ·
          refine ⟨1651342515050961722533451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4403580040135897926755869 1651342515050961722533451)
          ·
            refine ⟨2477013772576442583800177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1651342515050961722533451 2477013772576442583800177)
            ·
              refine ⟨1857760329432331937850133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2477013772576442583800177 1857760329432331937850133)
              ·
                refine ⟨87082515442140559586725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1857760329432331937850133 87082515442140559586725)
                ·
                  rfl

theorem cell22_2289500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 3, 1, 2, 6].length) (baseStart_2289500 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2289500 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2289500 prefixEnd_2289500 := by exact prefixLift 2289500
  have htrace : WordTrace (prefixWord ++ tailWord_2289500) baseStart_2289500 baseEnd_2289500 := by
    simpa [prefixWord, tailWord_2289500, baseEnd_2289500] using wordTrace_append hprefix tailTrace_2289500
  have hstable : (prefixWord ++ tailWord_2289500).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289500).length < 2 ^ (prefixWord ++ tailWord_2289500).sum := by decide
  have hdescent : baseEnd_2289500 < baseStart_2289500 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289575 : List Nat := [1, 1, 6, 1, 2, 2, 3, 1, 1, 4]
def baseStart_2289575 : Nat := 118140960795 + 2289575 * 2 ^ 59
def prefixEnd_2289575 : Nat := 4983230072969 + 3 ^ 40 * 2289575 * 2
def baseEnd_2289575 : Nat := 783768313011989840655295

theorem tailTrace_2289575 : CollatzResearch.WordTrace tailWord_2289575 prefixEnd_2289575 783768313011989840655295 := by
  unfold tailWord_2289575
  simp only [CollatzResearch.WordTrace]
  refine ⟨83507660680268278123758179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55671773786845518749172119 83507660680268278123758179)
  ·
    refine ⟨125261491020402417185637269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83507660680268278123758179 125261491020402417185637269)
    ·
      refine ⟨5871632391581363305576747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 125261491020402417185637269 5871632391581363305576747)
      ·
        refine ⟨8807448587372044958365121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5871632391581363305576747 8807448587372044958365121)
        ·
          refine ⟨6605586440529033718773841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8807448587372044958365121 6605586440529033718773841)
          ·
            refine ⟨4954189830396775289080381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6605586440529033718773841 4954189830396775289080381)
            ·
              refine ⟨1857821186398790733405143, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4954189830396775289080381 1857821186398790733405143)
              ·
                refine ⟨2786731779598186100107715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1857821186398790733405143 2786731779598186100107715)
                ·
                  refine ⟨4180097669397279150161573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2786731779598186100107715 4180097669397279150161573)
                  ·
                    refine ⟨783768313011989840655295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4180097669397279150161573 783768313011989840655295)
                    ·
                      rfl

theorem cell22_2289575_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 3, 1, 1, 4].length) (baseStart_2289575 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2289575 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2289575 prefixEnd_2289575 := by exact prefixLift 2289575
  have htrace : WordTrace (prefixWord ++ tailWord_2289575) baseStart_2289575 baseEnd_2289575 := by
    simpa [prefixWord, tailWord_2289575, baseEnd_2289575] using wordTrace_append hprefix tailTrace_2289575
  have hstable : (prefixWord ++ tailWord_2289575).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289575).length < 2 ^ (prefixWord ++ tailWord_2289575).sum := by decide
  have hdescent : baseEnd_2289575 < baseStart_2289575 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289575) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289616 : List Nat := [2, 1, 1, 1, 1, 2, 5, 1, 5, 3]
def baseStart_2289616 : Nat := 118140960795 + 2289616 * 2 ^ 59
def prefixEnd_2289616 : Nat := 4983230072969 + 3 ^ 40 * 2289616 * 2
def baseEnd_2289616 : Nat := 783782348149879400380169

theorem tailTrace_2289616 : CollatzResearch.WordTrace tailWord_2289616 prefixEnd_2289616 783782348149879400380169 := by
  unfold tailWord_2289616
  simp only [CollatzResearch.WordTrace]
  refine ⟨41754578036559871063000351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55672770715413161417333801 41754578036559871063000351)
  ·
    refine ⟨62631867054839806594500527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41754578036559871063000351 62631867054839806594500527)
    ·
      refine ⟨93947800582259709891750791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62631867054839806594500527 93947800582259709891750791)
      ·
        refine ⟨140921700873389564837626187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93947800582259709891750791 140921700873389564837626187)
        ·
          refine ⟨211382551310084347256439281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140921700873389564837626187 211382551310084347256439281)
          ·
            refine ⟨158536913482563260442329461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211382551310084347256439281 158536913482563260442329461)
            ·
              refine ⟨14862835638990305666468387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 158536913482563260442329461 14862835638990305666468387)
              ·
                refine ⟨22294253458485458499702581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14862835638990305666468387 22294253458485458499702581)
                ·
                  refine ⟨2090086261733011734347117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 22294253458485458499702581 2090086261733011734347117)
                  ·
                    refine ⟨783782348149879400380169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2090086261733011734347117 783782348149879400380169)
                    ·
                      rfl

theorem cell22_2289616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 5, 1, 5, 3].length) (baseStart_2289616 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2289616 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2289616 prefixEnd_2289616 := by exact prefixLift 2289616
  have htrace : WordTrace (prefixWord ++ tailWord_2289616) baseStart_2289616 baseEnd_2289616 := by
    simpa [prefixWord, tailWord_2289616, baseEnd_2289616] using wordTrace_append hprefix tailTrace_2289616
  have hstable : (prefixWord ++ tailWord_2289616).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289616).length < 2 ^ (prefixWord ++ tailWord_2289616).sum := by decide
  have hdescent : baseEnd_2289616 < baseStart_2289616 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289661 : List Nat := [1, 4, 1, 1, 1, 2, 4, 1, 2, 5]
def baseStart_2289661 : Nat := 118140960795 + 2289661 * 2 ^ 59
def prefixEnd_2289661 : Nat := 4983230072969 + 3 ^ 40 * 2289661 * 2
def baseEnd_2289661 : Nat := 783797752569514283005031

theorem tailTrace_2289661 : CollatzResearch.WordTrace tailWord_2289661 prefixEnd_2289661 783797752569514283005031 := by
  unfold tailWord_2289661
  simp only [CollatzResearch.WordTrace]
  refine ⟨83510797357956714811388837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55673864905304476540925891 83510797357956714811388837)
  ·
    refine ⟨15658274504616884027135407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83510797357956714811388837 15658274504616884027135407)
    ·
      refine ⟨23487411756925326040703111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15658274504616884027135407 23487411756925326040703111)
      ·
        refine ⟨35231117635387989061054667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23487411756925326040703111 35231117635387989061054667)
        ·
          refine ⟨52846676453081983591582001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35231117635387989061054667 52846676453081983591582001)
          ·
            refine ⟨39635007339811487693686501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52846676453081983591582001 39635007339811487693686501)
            ·
              refine ⟨7431563876214653942566219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 39635007339811487693686501 7431563876214653942566219)
              ·
                refine ⟨11147345814321980913849329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7431563876214653942566219 11147345814321980913849329)
                ·
                  refine ⟨8360509360741485685386997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 11147345814321980913849329 8360509360741485685386997)
                  ·
                    refine ⟨783797752569514283005031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8360509360741485685386997 783797752569514283005031)
                    ·
                      rfl

theorem cell22_2289661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 4, 1, 2, 5].length) (baseStart_2289661 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2289661 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2289661 prefixEnd_2289661 := by exact prefixLift 2289661
  have htrace : WordTrace (prefixWord ++ tailWord_2289661) baseStart_2289661 baseEnd_2289661 := by
    simpa [prefixWord, tailWord_2289661, baseEnd_2289661] using wordTrace_append hprefix tailTrace_2289661
  have hstable : (prefixWord ++ tailWord_2289661).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289661).length < 2 ^ (prefixWord ++ tailWord_2289661).sum := by decide
  have hdescent : baseEnd_2289661 < baseStart_2289661 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289723 : List Nat := [1, 1, 1, 1, 1, 2, 1, 9, 2, 3]
def baseStart_2289723 : Nat := 118140960795 + 2289723 * 2 ^ 59
def prefixEnd_2289723 : Nat := 4983230072969 + 3 ^ 40 * 2289723 * 2
def baseEnd_2289723 : Nat := 783818976436566787954841

theorem tailTrace_2289723 : CollatzResearch.WordTrace tailWord_2289723 prefixEnd_2289723 783818976436566787954841 := by
  unfold tailWord_2289723
  simp only [CollatzResearch.WordTrace]
  refine ⟨83513058683732099400145823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55675372455821399600097215 83513058683732099400145823)
  ·
    refine ⟨125269588025598149100218735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83513058683732099400145823 125269588025598149100218735)
    ·
      refine ⟨187904382038397223650328103, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125269588025598149100218735 187904382038397223650328103)
      ·
        refine ⟨281856573057595835475492155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187904382038397223650328103 281856573057595835475492155)
        ·
          refine ⟨422784859586393753213238233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 281856573057595835475492155 422784859586393753213238233)
          ·
            refine ⟨317088644689795314909928675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 422784859586393753213238233 317088644689795314909928675)
            ·
              refine ⟨475632967034692972364893013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 317088644689795314909928675 475632967034692972364893013)
              ·
                refine ⟨2786911916218904134950545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 475632967034692972364893013 2786911916218904134950545)
                ·
                  refine ⟨2090183937164178101212909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2786911916218904134950545 2090183937164178101212909)
                  ·
                    refine ⟨783818976436566787954841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2090183937164178101212909 783818976436566787954841)
                    ·
                      rfl

theorem cell22_2289723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 9, 2, 3].length) (baseStart_2289723 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2289723 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2289723 prefixEnd_2289723 := by exact prefixLift 2289723
  have htrace : WordTrace (prefixWord ++ tailWord_2289723) baseStart_2289723 baseEnd_2289723 := by
    simpa [prefixWord, tailWord_2289723, baseEnd_2289723] using wordTrace_append hprefix tailTrace_2289723
  have hstable : (prefixWord ++ tailWord_2289723).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289723).length < 2 ^ (prefixWord ++ tailWord_2289723).sum := by decide
  have hdescent : baseEnd_2289723 < baseStart_2289723 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289757 : List Nat := [1, 4, 4, 1, 1, 1, 1, 4, 2, 3]
def baseStart_2289757 : Nat := 118140960795 + 2289757 * 2 ^ 59
def prefixEnd_2289757 : Nat := 4983230072969 + 3 ^ 40 * 2289757 * 2
def baseEnd_2289757 : Nat := 783830615331402032604737

theorem tailTrace_2289757 : CollatzResearch.WordTrace tailWord_2289757 prefixEnd_2289757 783830615331402032604737 := by
  unfold tailWord_2289757
  simp only [CollatzResearch.WordTrace]
  refine ⟨83514298765608923206883525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55676199177072615471255683 83514298765608923206883525)
  ·
    refine ⟨15658931018551673101290661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83514298765608923206883525 15658931018551673101290661)
    ·
      refine ⟨2936049565978438706491999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15658931018551673101290661 2936049565978438706491999)
      ·
        refine ⟨4404074348967658059737999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2936049565978438706491999 4404074348967658059737999)
        ·
          refine ⟨6606111523451487089606999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4404074348967658059737999 6606111523451487089606999)
          ·
            refine ⟨9909167285177230634410499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6606111523451487089606999 9909167285177230634410499)
            ·
              refine ⟨14863750927765845951615749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9909167285177230634410499 14863750927765845951615749)
              ·
                refine ⟨2786953298956096115927953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14863750927765845951615749 2786953298956096115927953)
                ·
                  refine ⟨2090214974217072086945965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2786953298956096115927953 2090214974217072086945965)
                  ·
                    refine ⟨783830615331402032604737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2090214974217072086945965 783830615331402032604737)
                    ·
                      rfl

theorem cell22_2289757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_2289757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2289757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2289757 prefixEnd_2289757 := by exact prefixLift 2289757
  have htrace : WordTrace (prefixWord ++ tailWord_2289757) baseStart_2289757 baseEnd_2289757 := by
    simpa [prefixWord, tailWord_2289757, baseEnd_2289757] using wordTrace_append hprefix tailTrace_2289757
  have hstable : (prefixWord ++ tailWord_2289757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289757).length < 2 ^ (prefixWord ++ tailWord_2289757).sum := by decide
  have hdescent : baseEnd_2289757 < baseStart_2289757 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289770 : List Nat := [3, 1, 3, 2, 3, 2, 1, 7]
def baseStart_2289770 : Nat := 118140960795 + 2289770 * 2 ^ 59
def prefixEnd_2289770 : Nat := 4983230072969 + 3 ^ 40 * 2289770 * 2
def baseEnd_2289770 : Nat := 87092785055230481336633

theorem tailTrace_2289770 : CollatzResearch.WordTrace tailWord_2289770 prefixEnd_2289770 87092785055230481336633 := by
  unfold tailWord_2289770
  simp only [CollatzResearch.WordTrace]
  refine ⟨20878693228640456606776691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55676515276374550951404509 20878693228640456606776691)
  ·
    refine ⟨31318039842960684910165037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20878693228640456606776691 31318039842960684910165037)
    ·
      refine ⟨11744264941110256841311889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 31318039842960684910165037 11744264941110256841311889)
      ·
        refine ⟨8808198705832692630983917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11744264941110256841311889 8808198705832692630983917)
        ·
          refine ⟨3303074514687259736618969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8808198705832692630983917 3303074514687259736618969)
          ·
            refine ⟨2477305886015444802464227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3303074514687259736618969 2477305886015444802464227)
            ·
              refine ⟨3715958829023167203696341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2477305886015444802464227 3715958829023167203696341)
              ·
                refine ⟨87092785055230481336633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3715958829023167203696341 87092785055230481336633)
                ·
                  rfl

theorem cell22_2289770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 3, 2, 1, 7].length) (baseStart_2289770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2289770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2289770 prefixEnd_2289770 := by exact prefixLift 2289770
  have htrace : WordTrace (prefixWord ++ tailWord_2289770) baseStart_2289770 baseEnd_2289770 := by
    simpa [prefixWord, tailWord_2289770, baseEnd_2289770] using wordTrace_append hprefix tailTrace_2289770
  have hstable : (prefixWord ++ tailWord_2289770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289770).length < 2 ^ (prefixWord ++ tailWord_2289770).sum := by decide
  have hdescent : baseEnd_2289770 < baseStart_2289770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289785 : List Nat := [1, 2, 1, 3, 4, 2, 1, 2, 3, 3]
def baseStart_2289785 : Nat := 118140960795 + 2289785 * 2 ^ 59
def prefixEnd_2289785 : Nat := 4983230072969 + 3 ^ 40 * 2289785 * 2
def baseEnd_2289785 : Nat := 783840200303619292904651

theorem tailTrace_2289785 : CollatzResearch.WordTrace tailWord_2289785 prefixEnd_2289785 783840200303619292904651 := by
  unfold tailWord_2289785
  simp only [CollatzResearch.WordTrace]
  refine ⟨83515320009507483988902809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55676880006338322659268539 83515320009507483988902809)
  ·
    refine ⟨62636490007130612991677107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83515320009507483988902809 62636490007130612991677107)
    ·
      refine ⟨93954735010695919487515661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62636490007130612991677107 93954735010695919487515661)
      ·
        refine ⟨35233025629010969807818373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93954735010695919487515661 35233025629010969807818373)
        ·
          refine ⟨6606192305439556838965945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35233025629010969807818373 6606192305439556838965945)
          ·
            refine ⟨4954644229079667629224459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6606192305439556838965945 4954644229079667629224459)
            ·
              refine ⟨7431966343619501443836689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4954644229079667629224459 7431966343619501443836689)
              ·
                refine ⟨5573974757714626082877517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7431966343619501443836689 5573974757714626082877517)
                ·
                  refine ⟨2090240534142984781079069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5573974757714626082877517 2090240534142984781079069)
                  ·
                    refine ⟨783840200303619292904651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2090240534142984781079069 783840200303619292904651)
                    ·
                      rfl

theorem cell22_2289785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 4, 2, 1, 2, 3, 3].length) (baseStart_2289785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2289785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2289785 prefixEnd_2289785 := by exact prefixLift 2289785
  have htrace : WordTrace (prefixWord ++ tailWord_2289785) baseStart_2289785 baseEnd_2289785 := by
    simpa [prefixWord, tailWord_2289785, baseEnd_2289785] using wordTrace_append hprefix tailTrace_2289785
  have hstable : (prefixWord ++ tailWord_2289785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289785).length < 2 ^ (prefixWord ++ tailWord_2289785).sum := by decide
  have hdescent : baseEnd_2289785 < baseStart_2289785 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289802 : List Nat := [3, 1, 2, 3, 1, 2, 1, 5, 1, 3]
def baseStart_2289802 : Nat := 118140960795 + 2289802 * 2 ^ 59
def prefixEnd_2289802 : Nat := 4983230072969 + 3 ^ 40 * 2289802 * 2
def baseEnd_2289802 : Nat := 783846019751036915229599

theorem tailTrace_2289802 : CollatzResearch.WordTrace tailWord_2289802 prefixEnd_2289802 783846019751036915229599 := by
  unfold tailWord_2289802
  simp only [CollatzResearch.WordTrace]
  refine ⟨20878985012611473973067915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55677293366963930594847773 20878985012611473973067915)
  ·
    refine ⟨31318477518917210959601873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20878985012611473973067915 31318477518917210959601873)
    ·
      refine ⟨23488858139187908219701405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31318477518917210959601873 23488858139187908219701405)
      ·
        refine ⟨8808321802195465582388027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 23488858139187908219701405 8808321802195465582388027)
        ·
          refine ⟨13212482703293198373582041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8808321802195465582388027 13212482703293198373582041)
          ·
            refine ⟨9909362027469898780186531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13212482703293198373582041 9909362027469898780186531)
            ·
              refine ⟨14864043041204848170279797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9909362027469898780186531 14864043041204848170279797)
              ·
                refine ⟨1393504035112954515963731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 14864043041204848170279797 1393504035112954515963731)
                ·
                  refine ⟨2090256052669431773945597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1393504035112954515963731 2090256052669431773945597)
                  ·
                    refine ⟨783846019751036915229599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2090256052669431773945597 783846019751036915229599)
                    ·
                      rfl

theorem cell22_2289802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 5, 1, 3].length) (baseStart_2289802 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2289802 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2289802 prefixEnd_2289802 := by exact prefixLift 2289802
  have htrace : WordTrace (prefixWord ++ tailWord_2289802) baseStart_2289802 baseEnd_2289802 := by
    simpa [prefixWord, tailWord_2289802, baseEnd_2289802] using wordTrace_append hprefix tailTrace_2289802
  have hstable : (prefixWord ++ tailWord_2289802).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289802).length < 2 ^ (prefixWord ++ tailWord_2289802).sum := by decide
  have hdescent : baseEnd_2289802 < baseStart_2289802 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289873 : List Nat := [1, 2, 2, 1, 2, 2, 3, 1, 4, 4]
def baseStart_2289873 : Nat := 118140960795 + 2289873 * 2 ^ 59
def prefixEnd_2289873 : Nat := 4983230072969 + 3 ^ 40 * 2289873 * 2
def baseEnd_2289873 : Nat := 783870324502016396704381

theorem tailTrace_2289873 : CollatzResearch.WordTrace tailWord_2289873 prefixEnd_2289873 783870324502016396704381 := by
  unfold tailWord_2289873
  simp only [CollatzResearch.WordTrace]
  refine ⟨83518529633188675018106273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55679019755459116678737515 83518529633188675018106273)
  ·
    refine ⟨62638897224891506263579705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83518529633188675018106273 62638897224891506263579705)
    ·
      refine ⟨46979172918668629697684779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62638897224891506263579705 46979172918668629697684779)
      ·
        refine ⟨70468759378002944546527169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 46979172918668629697684779 70468759378002944546527169)
        ·
          refine ⟨52851569533502208409895377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70468759378002944546527169 52851569533502208409895377)
          ·
            refine ⟨39638677150126656307421533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52851569533502208409895377 39638677150126656307421533)
            ·
              refine ⟨14864503931297496115283075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39638677150126656307421533 14864503931297496115283075)
              ·
                refine ⟨22296755896946244172924613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14864503931297496115283075 22296755896946244172924613)
                ·
                  refine ⟨4180641730677420782423365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22296755896946244172924613 4180641730677420782423365)
                  ·
                    refine ⟨783870324502016396704381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4180641730677420782423365 783870324502016396704381)
                    ·
                      rfl

theorem cell22_2289873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 3, 1, 4, 4].length) (baseStart_2289873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2289873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2289873 prefixEnd_2289873 := by exact prefixLift 2289873
  have htrace : WordTrace (prefixWord ++ tailWord_2289873) baseStart_2289873 baseEnd_2289873 := by
    simpa [prefixWord, tailWord_2289873, baseEnd_2289873] using wordTrace_append hprefix tailTrace_2289873
  have hstable : (prefixWord ++ tailWord_2289873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289873).length < 2 ^ (prefixWord ++ tailWord_2289873).sum := by decide
  have hdescent : baseEnd_2289873 < baseStart_2289873 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289877 : List Nat := [1, 3, 2, 4, 2, 2, 1, 1, 6]
def baseStart_2289877 : Nat := 118140960795 + 2289877 * 2 ^ 59
def prefixEnd_2289877 : Nat := 4983230072969 + 3 ^ 40 * 2289877 * 2
def baseEnd_2289877 : Nat := 261290564594587239868123

theorem tailTrace_2289877 : CollatzResearch.WordTrace tailWord_2289877 prefixEnd_2289877 261290564594587239868123 := by
  unfold tailWord_2289877
  simp only [CollatzResearch.WordTrace]
  refine ⟨83518675525174183701251885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55679117016782789134167923 83518675525174183701251885)
  ·
    refine ⟨31319503321940318887969457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83518675525174183701251885 31319503321940318887969457)
    ·
      refine ⟨23489627491455239165977093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31319503321940318887969457 23489627491455239165977093)
      ·
        refine ⟨4404305154647857343620705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23489627491455239165977093 4404305154647857343620705)
        ·
          refine ⟨3303228865985893007715529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4404305154647857343620705 3303228865985893007715529)
          ·
            refine ⟨2477421649489419755786647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3303228865985893007715529 2477421649489419755786647)
            ·
              refine ⟨3716132474234129633679971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2477421649489419755786647 3716132474234129633679971)
              ·
                refine ⟨5574198711351194450519957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3716132474234129633679971 5574198711351194450519957)
                ·
                  refine ⟨261290564594587239868123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5574198711351194450519957 261290564594587239868123)
                  ·
                    rfl

theorem cell22_2289877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 2, 1, 1, 6].length) (baseStart_2289877 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2289877 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2289877 prefixEnd_2289877 := by exact prefixLift 2289877
  have htrace : WordTrace (prefixWord ++ tailWord_2289877) baseStart_2289877 baseEnd_2289877 := by
    simpa [prefixWord, tailWord_2289877, baseEnd_2289877] using wordTrace_append hprefix tailTrace_2289877
  have hstable : (prefixWord ++ tailWord_2289877).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289877).length < 2 ^ (prefixWord ++ tailWord_2289877).sum := by decide
  have hdescent : baseEnd_2289877 < baseStart_2289877 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2289888 : List Nat := [2, 1, 1, 3, 1, 3, 4, 7]
def baseStart_2289888 : Nat := 118140960795 + 2289888 * 2 ^ 59
def prefixEnd_2289888 : Nat := 4983230072969 + 3 ^ 40 * 2289888 * 2
def baseEnd_2289888 : Nat := 87097273256506817508815

theorem tailTrace_2289888 : CollatzResearch.WordTrace tailWord_2289888 prefixEnd_2289888 87097273256506817508815 := by
  unfold tailWord_2289888
  simp only [CollatzResearch.WordTrace]
  refine ⟨41759538364067166289951159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55679384485422888386601545 41759538364067166289951159)
  ·
    refine ⟨62639307546100749434926739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41759538364067166289951159 62639307546100749434926739)
    ·
      refine ⟨93958961319151124152390109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62639307546100749434926739 93958961319151124152390109)
      ·
        refine ⟨35234610494681671557146291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 93958961319151124152390109 35234610494681671557146291)
        ·
          refine ⟨52851915742022507335719437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35234610494681671557146291 52851915742022507335719437)
          ·
            refine ⟨19819468403258440250894789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 52851915742022507335719437 19819468403258440250894789)
            ·
              refine ⟨3716150325610957547042773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19819468403258440250894789 3716150325610957547042773)
              ·
                refine ⟨87097273256506817508815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3716150325610957547042773 87097273256506817508815)
                ·
                  rfl

theorem cell22_2289888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 4, 7].length) (baseStart_2289888 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2289888 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2289888 prefixEnd_2289888 := by exact prefixLift 2289888
  have htrace : WordTrace (prefixWord ++ tailWord_2289888) baseStart_2289888 baseEnd_2289888 := by
    simpa [prefixWord, tailWord_2289888, baseEnd_2289888] using wordTrace_append hprefix tailTrace_2289888
  have hstable : (prefixWord ++ tailWord_2289888).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2289888).length < 2 ^ (prefixWord ++ tailWord_2289888).sum := by decide
  have hdescent : baseEnd_2289888 < baseStart_2289888 := by decide
  rcases family_descends (prefixWord ++ tailWord_2289888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290025 : List Nat := [1, 2, 1, 1, 1, 3, 4, 3, 2, 4]
def baseStart_2290025 : Nat := 118140960795 + 2290025 * 2 ^ 59
def prefixEnd_2290025 : Nat := 4983230072969 + 3 ^ 40 * 2290025 * 2
def baseEnd_2290025 : Nat := 783922357208338666903915

theorem tailTrace_2290025 : CollatzResearch.WordTrace tailWord_2290025 prefixEnd_2290025 783922357208338666903915 := by
  unfold tailWord_2290025
  simp only [CollatzResearch.WordTrace]
  refine ⟨83524073528638004977639529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55682715685758669985093019 83524073528638004977639529)
  ·
    refine ⟨62643055146478503733229647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83524073528638004977639529 62643055146478503733229647)
    ·
      refine ⟨93964582719717755599844471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62643055146478503733229647 93964582719717755599844471)
      ·
        refine ⟨140946874079576633399766707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93964582719717755599844471 140946874079576633399766707)
        ·
          refine ⟨211420311119364950099650061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140946874079576633399766707 211420311119364950099650061)
          ·
            refine ⟨79282616669761856287368773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211420311119364950099650061 79282616669761856287368773)
            ·
              refine ⟨14865490625580348053881645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79282616669761856287368773 14865490625580348053881645)
              ·
                refine ⟨5574558984592630520205617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14865490625580348053881645 5574558984592630520205617)
                ·
                  refine ⟨4180919238444472890154213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5574558984592630520205617 4180919238444472890154213)
                  ·
                    refine ⟨783922357208338666903915, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4180919238444472890154213 783922357208338666903915)
                    ·
                      rfl

theorem cell22_2290025_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 3, 2, 4].length) (baseStart_2290025 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2290025 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2290025 prefixEnd_2290025 := by exact prefixLift 2290025
  have htrace : WordTrace (prefixWord ++ tailWord_2290025) baseStart_2290025 baseEnd_2290025 := by
    simpa [prefixWord, tailWord_2290025, baseEnd_2290025] using wordTrace_append hprefix tailTrace_2290025
  have hstable : (prefixWord ++ tailWord_2290025).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290025).length < 2 ^ (prefixWord ++ tailWord_2290025).sum := by decide
  have hdescent : baseEnd_2290025 < baseStart_2290025 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290025) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290175 : List Nat := [1, 1, 2, 2, 1, 2, 4, 9]
def baseStart_2290175 : Nat := 118140960795 + 2290175 * 2 ^ 59
def prefixEnd_2290175 : Nat := 4983230072969 + 3 ^ 40 * 2290175 * 2
def baseEnd_2290175 : Nat := 87108189474865363961495

theorem tailTrace_2290175 : CollatzResearch.WordTrace tailWord_2290175 prefixEnd_2290175 87108189474865363961495 := by
  unfold tailWord_2290175
  simp only [CollatzResearch.WordTrace]
  refine ⟨83529544478094580595599979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55686362985396387063733319 83529544478094580595599979)
  ·
    refine ⟨125294316717141870893399969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83529544478094580595599979 125294316717141870893399969)
    ·
      refine ⟨93970737537856403170049977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125294316717141870893399969 93970737537856403170049977)
      ·
        refine ⟨70478053153392302377537483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 93970737537856403170049977 70478053153392302377537483)
        ·
          refine ⟨105717079730088453566306225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70478053153392302377537483 105717079730088453566306225)
          ·
            refine ⟨79287809797566340174729669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105717079730088453566306225 79287809797566340174729669)
            ·
              refine ⟨14866464337043688782761813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 79287809797566340174729669 14866464337043688782761813)
              ·
                refine ⟨87108189474865363961495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14866464337043688782761813 87108189474865363961495)
                ·
                  rfl

theorem cell22_2290175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 9].length) (baseStart_2290175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2290175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2290175 prefixEnd_2290175 := by exact prefixLift 2290175
  have htrace : WordTrace (prefixWord ++ tailWord_2290175) baseStart_2290175 baseEnd_2290175 := by
    simpa [prefixWord, tailWord_2290175, baseEnd_2290175] using wordTrace_append hprefix tailTrace_2290175
  have hstable : (prefixWord ++ tailWord_2290175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290175).length < 2 ^ (prefixWord ++ tailWord_2290175).sum := by decide
  have hdescent : baseEnd_2290175 < baseStart_2290175 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290177 : List Nat := [1, 2, 4, 1, 3, 1, 1, 2, 1, 6]
def baseStart_2290177 : Nat := 118140960795 + 2290177 * 2 ^ 59
def prefixEnd_2290177 : Nat := 4983230072969 + 3 ^ 40 * 2290177 * 2
def baseEnd_2290177 : Nat := 783974389914660937103449

theorem tailTrace_2290177 : CollatzResearch.WordTrace tailWord_2290177 prefixEnd_2290177 783974389914660937103449 := by
  unfold tailWord_2290177
  simp only [CollatzResearch.WordTrace]
  refine ⟨83529617424087334937172785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55686411616058223291448523 83529617424087334937172785)
  ·
    refine ⟨62647213068065501202879589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83529617424087334937172785 62647213068065501202879589)
    ·
      refine ⟨11746352450262281475539923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62647213068065501202879589 11746352450262281475539923)
      ·
        refine ⟨17619528675393422213309885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11746352450262281475539923 17619528675393422213309885)
        ·
          refine ⟨6607323253272533329991207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17619528675393422213309885 6607323253272533329991207)
          ·
            refine ⟨9910984879908799994986811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6607323253272533329991207 9910984879908799994986811)
            ·
              refine ⟨14866477319863199992480217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9910984879908799994986811 14866477319863199992480217)
              ·
                refine ⟨11149857989897399994360163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14866477319863199992480217 11149857989897399994360163)
                ·
                  refine ⟨16724786984846099991540245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11149857989897399994360163 16724786984846099991540245)
                  ·
                    refine ⟨783974389914660937103449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16724786984846099991540245 783974389914660937103449)
                    ·
                      rfl

theorem cell22_2290177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 1, 1, 2, 1, 6].length) (baseStart_2290177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2290177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2290177 prefixEnd_2290177 := by exact prefixLift 2290177
  have htrace : WordTrace (prefixWord ++ tailWord_2290177) baseStart_2290177 baseEnd_2290177 := by
    simpa [prefixWord, tailWord_2290177, baseEnd_2290177] using wordTrace_append hprefix tailTrace_2290177
  have hstable : (prefixWord ++ tailWord_2290177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290177).length < 2 ^ (prefixWord ++ tailWord_2290177).sum := by decide
  have hdescent : baseEnd_2290177 < baseStart_2290177 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290196 : List Nat := [2, 4, 3, 1, 1, 1, 1, 2, 4, 3]
def baseStart_2290196 : Nat := 118140960795 + 2290196 * 2 ^ 59
def prefixEnd_2290196 : Nat := 4983230072969 + 3 ^ 40 * 2290196 * 2
def baseEnd_2290196 : Nat := 783980894002951220878391

theorem tailTrace_2290196 : CollatzResearch.WordTrace tailWord_2290196 prefixEnd_2290196 783980894002951220878391 := by
  unfold tailWord_2290196
  simp only [CollatzResearch.WordTrace]
  refine ⟨41765155205509250591057221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55686873607345667454742961 41765155205509250591057221)
  ·
    refine ⟨7830966601032984485823229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 41765155205509250591057221 7830966601032984485823229)
    ·
      refine ⟨2936612475387369182183711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7830966601032984485823229 2936612475387369182183711)
      ·
        refine ⟨4404918713081053773275567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2936612475387369182183711 4404918713081053773275567)
        ·
          refine ⟨6607378069621580659913351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4404918713081053773275567 6607378069621580659913351)
          ·
            refine ⟨9911067104432370989870027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6607378069621580659913351 9911067104432370989870027)
            ·
              refine ⟨14866600656648556484805041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9911067104432370989870027 14866600656648556484805041)
              ·
                refine ⟨11149950492486417363603781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14866600656648556484805041 11149950492486417363603781)
                ·
                  refine ⟨2090615717341203255675709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11149950492486417363603781 2090615717341203255675709)
                  ·
                    refine ⟨783980894002951220878391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2090615717341203255675709 783980894002951220878391)
                    ·
                      rfl

theorem cell22_2290196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 2, 4, 3].length) (baseStart_2290196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2290196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2290196 prefixEnd_2290196 := by exact prefixLift 2290196
  have htrace : WordTrace (prefixWord ++ tailWord_2290196) baseStart_2290196 baseEnd_2290196 := by
    simpa [prefixWord, tailWord_2290196, baseEnd_2290196] using wordTrace_append hprefix tailTrace_2290196
  have hstable : (prefixWord ++ tailWord_2290196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290196).length < 2 ^ (prefixWord ++ tailWord_2290196).sum := by decide
  have hdescent : baseEnd_2290196 < baseStart_2290196 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290215 : List Nat := [1, 1, 7, 2, 1, 1, 3, 2, 4]
def baseStart_2290215 : Nat := 118140960795 + 2290215 * 2 ^ 59
def prefixEnd_2290215 : Nat := 4983230072969 + 3 ^ 40 * 2290215 * 2
def baseEnd_2290215 : Nat := 261329132697080501551111

theorem tailTrace_2290215 : CollatzResearch.WordTrace tailWord_2290215 prefixEnd_2290215 261329132697080501551111 := by
  unfold tailWord_2290215
  simp only [CollatzResearch.WordTrace]
  refine ⟨83531003397949667427056099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55687335598633111618037399 83531003397949667427056099)
  ·
    refine ⟨125296505096924501140584149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83531003397949667427056099 125296505096924501140584149)
    ·
      refine ⟨2936636838209167995482441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 125296505096924501140584149 2936636838209167995482441)
      ·
        refine ⟨2202477628656875996611831, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2936636838209167995482441 2202477628656875996611831)
        ·
          refine ⟨3303716442985313994917747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2202477628656875996611831 3303716442985313994917747)
          ·
            refine ⟨4955574664477970992376621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3303716442985313994917747 4955574664477970992376621)
            ·
              refine ⟨1858340499179239122141233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4955574664477970992376621 1858340499179239122141233)
              ·
                refine ⟨1393755374384429341605925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1858340499179239122141233 1393755374384429341605925)
                ·
                  refine ⟨261329132697080501551111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1393755374384429341605925 261329132697080501551111)
                  ·
                    rfl

theorem cell22_2290215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2, 4].length) (baseStart_2290215 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2290215 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2290215 prefixEnd_2290215 := by exact prefixLift 2290215
  have htrace : WordTrace (prefixWord ++ tailWord_2290215) baseStart_2290215 baseEnd_2290215 := by
    simpa [prefixWord, tailWord_2290215, baseEnd_2290215] using wordTrace_append hprefix tailTrace_2290215
  have hstable : (prefixWord ++ tailWord_2290215).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290215).length < 2 ^ (prefixWord ++ tailWord_2290215).sum := by decide
  have hdescent : baseEnd_2290215 < baseStart_2290215 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290224 : List Nat := [2, 1, 1, 1, 2, 3, 5, 1, 3, 3]
def baseStart_2290224 : Nat := 118140960795 + 2290224 * 2 ^ 59
def prefixEnd_2290224 : Nat := 4983230072969 + 3 ^ 40 * 2290224 * 2
def baseEnd_2290224 : Nat := 783990478975168481178305

theorem tailTrace_2290224 : CollatzResearch.WordTrace tailWord_2290224 prefixEnd_2290224 783990478975168481178305 := by
  unfold tailWord_2290224
  simp only [CollatzResearch.WordTrace]
  refine ⟨41765665827458530982066863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55687554436611374642755817 41765665827458530982066863)
  ·
    refine ⟨62648498741187796473100295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41765665827458530982066863 62648498741187796473100295)
    ·
      refine ⟨93972748111781694709650443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62648498741187796473100295 93972748111781694709650443)
      ·
        refine ⟨140959122167672542064475665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93972748111781694709650443 140959122167672542064475665)
        ·
          refine ⟨105719341625754406548356749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 140959122167672542064475665 105719341625754406548356749)
          ·
            refine ⟨39644753109657902455633781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 105719341625754406548356749 39644753109657902455633781)
            ·
              refine ⟨3716695604030428355215667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39644753109657902455633781 3716695604030428355215667)
              ·
                refine ⟨5575043406045642532823501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3716695604030428355215667 5575043406045642532823501)
                ·
                  refine ⟨2090641277267115949808813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5575043406045642532823501 2090641277267115949808813)
                  ·
                    refine ⟨783990478975168481178305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2090641277267115949808813 783990478975168481178305)
                    ·
                      rfl

theorem cell22_2290224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 5, 1, 3, 3].length) (baseStart_2290224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2290224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2290224 prefixEnd_2290224 := by exact prefixLift 2290224
  have htrace : WordTrace (prefixWord ++ tailWord_2290224) baseStart_2290224 baseEnd_2290224 := by
    simpa [prefixWord, tailWord_2290224, baseEnd_2290224] using wordTrace_append hprefix tailTrace_2290224
  have hstable : (prefixWord ++ tailWord_2290224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290224).length < 2 ^ (prefixWord ++ tailWord_2290224).sum := by decide
  have hdescent : baseEnd_2290224 < baseStart_2290224 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290230 : List Nat := [5, 1, 2, 1, 2, 3, 2, 1, 2, 3]
def baseStart_2290230 : Nat := 118140960795 + 2290230 * 2 ^ 59
def prefixEnd_2290230 : Nat := 4983230072969 + 3 ^ 40 * 2290230 * 2
def baseEnd_2290230 : Nat := 783992532897786465528287

theorem tailTrace_2290230 : CollatzResearch.WordTrace tailWord_2290230 prefixEnd_2290230 783992532897786465528287 := by
  unfold tailWord_2290230
  simp only [CollatzResearch.WordTrace]
  refine ⟨5220721905805957811803259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55687700328596883325901429 5220721905805957811803259)
  ·
    refine ⟨7831082858708936717704889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5220721905805957811803259 7831082858708936717704889)
    ·
      refine ⟨5873312144031702538278667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7831082858708936717704889 5873312144031702538278667)
      ·
        refine ⟨8809968216047553807418001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5873312144031702538278667 8809968216047553807418001)
        ·
          refine ⟨6607476162035665355563501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8809968216047553807418001 6607476162035665355563501)
          ·
            refine ⟨2477803560763374508336313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6607476162035665355563501 2477803560763374508336313)
            ·
              refine ⟨1858352670572530881252235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2477803560763374508336313 1858352670572530881252235)
              ·
                refine ⟨2787529005858796321878353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1858352670572530881252235 2787529005858796321878353)
                ·
                  refine ⟨2090646754394097241408765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2787529005858796321878353 2090646754394097241408765)
                  ·
                    refine ⟨783992532897786465528287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2090646754394097241408765 783992532897786465528287)
                    ·
                      rfl

theorem cell22_2290230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_2290230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2290230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2290230 prefixEnd_2290230 := by exact prefixLift 2290230
  have htrace : WordTrace (prefixWord ++ tailWord_2290230) baseStart_2290230 baseEnd_2290230 := by
    simpa [prefixWord, tailWord_2290230, baseEnd_2290230] using wordTrace_append hprefix tailTrace_2290230
  have hstable : (prefixWord ++ tailWord_2290230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290230).length < 2 ^ (prefixWord ++ tailWord_2290230).sum := by decide
  have hdescent : baseEnd_2290230 < baseStart_2290230 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290327 : List Nat := [1, 1, 3, 3, 2, 1, 11]
def baseStart_2290327 : Nat := 118140960795 + 2290327 * 2 ^ 59
def prefixEnd_2290327 : Nat := 4983230072969 + 3 ^ 40 * 2290327 * 2
def baseEnd_2290327 : Nat := 29037990295559649846407

theorem tailTrace_2290327 : CollatzResearch.WordTrace tailWord_2290327 prefixEnd_2290327 29037990295559649846407 := by
  unfold tailWord_2290327
  simp only [CollatzResearch.WordTrace]
  refine ⟨83535088373543910555133235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55690058915695940370088823 83535088373543910555133235)
  ·
    refine ⟨125302632560315865832699853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83535088373543910555133235 125302632560315865832699853)
    ·
      refine ⟨46988487210118449687262445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125302632560315865832699853 46988487210118449687262445)
      ·
        refine ⟨17620682703794418632723417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 46988487210118449687262445 17620682703794418632723417)
        ·
          refine ⟨13215512027845813974542563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17620682703794418632723417 13215512027845813974542563)
          ·
            refine ⟨19823268041768720961813845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13215512027845813974542563 19823268041768720961813845)
            ·
              refine ⟨29037990295559649846407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 19823268041768720961813845 29037990295559649846407)
              ·
                rfl

theorem cell22_2290327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 11].length) (baseStart_2290327 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2290327 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2290327 prefixEnd_2290327 := by exact prefixLift 2290327
  have htrace : WordTrace (prefixWord ++ tailWord_2290327) baseStart_2290327 baseEnd_2290327 := by
    simpa [prefixWord, tailWord_2290327, baseEnd_2290327] using wordTrace_append hprefix tailTrace_2290327
  have hstable : (prefixWord ++ tailWord_2290327).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290327).length < 2 ^ (prefixWord ++ tailWord_2290327).sum := by decide
  have hdescent : baseEnd_2290327 < baseStart_2290327 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290451 : List Nat := [1, 1, 1, 2, 1, 3, 5, 4, 4]
def baseStart_2290451 : Nat := 118140960795 + 2290451 * 2 ^ 59
def prefixEnd_2290451 : Nat := 4983230072969 + 3 ^ 40 * 2290451 * 2
def baseEnd_2290451 : Nat := 261356061904738518584203

theorem tailTrace_2290451 : CollatzResearch.WordTrace tailWord_2290451 prefixEnd_2290451 261356061904738518584203 := by
  unfold tailWord_2290451
  simp only [CollatzResearch.WordTrace]
  refine ⟨83539611025094679732647207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55693074016729786488431471 83539611025094679732647207)
  ·
    refine ⟨125309416537642019598970811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83539611025094679732647207 125309416537642019598970811)
    ·
      refine ⟨187964124806463029398456217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125309416537642019598970811 187964124806463029398456217)
      ·
        refine ⟨140973093604847272048842163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 187964124806463029398456217 140973093604847272048842163)
        ·
          refine ⟨211459640407270908073263245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140973093604847272048842163 211459640407270908073263245)
          ·
            refine ⟨79297365152726590527473717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 211459640407270908073263245 79297365152726590527473717)
            ·
              refine ⟨7434127983068117861950661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 79297365152726590527473717 7434127983068117861950661)
              ·
                refine ⟨1393898996825272099115749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 7434127983068117861950661 1393898996825272099115749)
                ·
                  refine ⟨261356061904738518584203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1393898996825272099115749 261356061904738518584203)
                  ·
                    rfl

theorem cell22_2290451_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 4, 4].length) (baseStart_2290451 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2290451 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2290451 prefixEnd_2290451 := by exact prefixLift 2290451
  have htrace : WordTrace (prefixWord ++ tailWord_2290451) baseStart_2290451 baseEnd_2290451 := by
    simpa [prefixWord, tailWord_2290451, baseEnd_2290451] using wordTrace_append hprefix tailTrace_2290451
  have hstable : (prefixWord ++ tailWord_2290451).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290451).length < 2 ^ (prefixWord ++ tailWord_2290451).sum := by decide
  have hdescent : baseEnd_2290451 < baseStart_2290451 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290451) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290466 : List Nat := [3, 3, 1, 1, 2, 2, 1, 3, 1, 5]
def baseStart_2290466 : Nat := 118140960795 + 2290466 * 2 ^ 59
def prefixEnd_2290466 : Nat := 4983230072969 + 3 ^ 40 * 2290466 * 2
def baseEnd_2290466 : Nat := 784073320520760516627563

theorem tailTrace_2290466 : CollatzResearch.WordTrace tailWord_2290466 prefixEnd_2290466 784073320520760516627563 := by
  unfold tailWord_2290466
  simp only [CollatzResearch.WordTrace]
  refine ⟨20885039530010084323610813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55693438746693558196295501 20885039530010084323610813)
  ·
    refine ⟨7831889823753781621354055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20885039530010084323610813 7831889823753781621354055)
    ·
      refine ⟨11747834735630672432031083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7831889823753781621354055 11747834735630672432031083)
      ·
        refine ⟨17621752103446008648046625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11747834735630672432031083 17621752103446008648046625)
        ·
          refine ⟨13216314077584506486034969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17621752103446008648046625 13216314077584506486034969)
          ·
            refine ⟨9912235558188379864526227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13216314077584506486034969 9912235558188379864526227)
            ·
              refine ⟨14868353337282569796789341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9912235558188379864526227 14868353337282569796789341)
              ·
                refine ⟨5575632501480963673796003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14868353337282569796789341 5575632501480963673796003)
                ·
                  refine ⟨8363448752221445510694005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5575632501480963673796003 8363448752221445510694005)
                  ·
                    refine ⟨784073320520760516627563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8363448752221445510694005 784073320520760516627563)
                    ·
                      rfl

theorem cell22_2290466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 3, 1, 5].length) (baseStart_2290466 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2290466 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2290466 prefixEnd_2290466 := by exact prefixLift 2290466
  have htrace : WordTrace (prefixWord ++ tailWord_2290466) baseStart_2290466 baseEnd_2290466 := by
    simpa [prefixWord, tailWord_2290466, baseEnd_2290466] using wordTrace_append hprefix tailTrace_2290466
  have hstable : (prefixWord ++ tailWord_2290466).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290466).length < 2 ^ (prefixWord ++ tailWord_2290466).sum := by decide
  have hdescent : baseEnd_2290466 < baseStart_2290466 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290530 : List Nat := [3, 3, 2, 1, 3, 2, 2, 6]
def baseStart_2290530 : Nat := 118140960795 + 2290530 * 2 ^ 59
def prefixEnd_2290530 : Nat := 4983230072969 + 3 ^ 40 * 2290530 * 2
def baseEnd_2290530 : Nat := 87121692114298409225263

theorem tailTrace_2290530 : CollatzResearch.WordTrace tailWord_2290530 prefixEnd_2290530 87121692114298409225263 := by
  unfold tailWord_2290530
  simp only [CollatzResearch.WordTrace]
  refine ⟨20885623097952119056193261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55694994927872317483182029 20885623097952119056193261)
  ·
    refine ⟨7832108661732044646072473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20885623097952119056193261 7832108661732044646072473)
    ·
      refine ⟨5874081496299033484554355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7832108661732044646072473 5874081496299033484554355)
      ·
        refine ⟨8811122244448550226831533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5874081496299033484554355 8811122244448550226831533)
        ·
          refine ⟨3304170841668206335061825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8811122244448550226831533 3304170841668206335061825)
          ·
            refine ⟨2478128131251154751296369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3304170841668206335061825 2478128131251154751296369)
            ·
              refine ⟨1858596098438366063472277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2478128131251154751296369 1858596098438366063472277)
              ·
                refine ⟨87121692114298409225263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1858596098438366063472277 87121692114298409225263)
                ·
                  rfl

theorem cell22_2290530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 3, 2, 2, 6].length) (baseStart_2290530 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2290530 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2290530 prefixEnd_2290530 := by exact prefixLift 2290530
  have htrace : WordTrace (prefixWord ++ tailWord_2290530) baseStart_2290530 baseEnd_2290530 := by
    simpa [prefixWord, tailWord_2290530, baseEnd_2290530] using wordTrace_append hprefix tailTrace_2290530
  have hstable : (prefixWord ++ tailWord_2290530).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290530).length < 2 ^ (prefixWord ++ tailWord_2290530).sum := by decide
  have hdescent : baseEnd_2290530 < baseStart_2290530 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290539 : List Nat := [1, 1, 1, 1, 2, 2, 4, 2, 1, 7]
def baseStart_2290539 : Nat := 118140960795 + 2290539 * 2 ^ 59
def prefixEnd_2290539 : Nat := 4983230072969 + 3 ^ 40 * 2290539 * 2
def baseEnd_2290539 : Nat := 784098309912612659552339

theorem tailTrace_2290539 : CollatzResearch.WordTrace tailWord_2290539 prefixEnd_2290539 784098309912612659552339 := by
  unfold tailWord_2290539
  simp only [CollatzResearch.WordTrace]
  refine ⟨83542820648775870761850671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55695213765850580507900447 83542820648775870761850671)
  ·
    refine ⟨125314230973163806142776007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83542820648775870761850671 125314230973163806142776007)
    ·
      refine ⟨187971346459745709214164011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 125314230973163806142776007 187971346459745709214164011)
      ·
        refine ⟨281957019689618563821246017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 187971346459745709214164011 281957019689618563821246017)
        ·
          refine ⟨211467764767213922865934513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 281957019689618563821246017 211467764767213922865934513)
          ·
            refine ⟨158600823575410442149450885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 211467764767213922865934513 158600823575410442149450885)
            ·
              refine ⟨29737654420389457903022041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 158600823575410442149450885 29737654420389457903022041)
              ·
                refine ⟨22303240815292093427266531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29737654420389457903022041 22303240815292093427266531)
                ·
                  refine ⟨33454861222938140140899797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 22303240815292093427266531 33454861222938140140899797)
                  ·
                    refine ⟨784098309912612659552339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33454861222938140140899797 784098309912612659552339)
                    ·
                      rfl

theorem cell22_2290539_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 4, 2, 1, 7].length) (baseStart_2290539 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2290539 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2290539 prefixEnd_2290539 := by exact prefixLift 2290539
  have htrace : WordTrace (prefixWord ++ tailWord_2290539) baseStart_2290539 baseEnd_2290539 := by
    simpa [prefixWord, tailWord_2290539, baseEnd_2290539] using wordTrace_append hprefix tailTrace_2290539
  have hstable : (prefixWord ++ tailWord_2290539).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290539).length < 2 ^ (prefixWord ++ tailWord_2290539).sum := by decide
  have hdescent : baseEnd_2290539 < baseStart_2290539 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290539) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290545 : List Nat := [1, 2, 2, 2, 1, 4, 3, 3, 1, 3]
def baseStart_2290545 : Nat := 118140960795 + 2290545 * 2 ^ 59
def prefixEnd_2290545 : Nat := 4983230072969 + 3 ^ 40 * 2290545 * 2
def baseEnd_2290545 : Nat := 784100363835230643902321

theorem tailTrace_2290545 : CollatzResearch.WordTrace tailWord_2290545 prefixEnd_2290545 784100363835230643902321 := by
  unfold tailWord_2290545
  simp only [CollatzResearch.WordTrace]
  refine ⟨83543039486754133786569089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55695359657836089191046059 83543039486754133786569089)
  ·
    refine ⟨62657279615065600339926817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83543039486754133786569089 62657279615065600339926817)
    ·
      refine ⟨46992959711299200254945113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62657279615065600339926817 46992959711299200254945113)
      ·
        refine ⟨35244719783474400191208835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46992959711299200254945113 35244719783474400191208835)
        ·
          refine ⟨52867079675211600286813253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35244719783474400191208835 52867079675211600286813253)
          ·
            refine ⟨9912577439102175053777485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 52867079675211600286813253 9912577439102175053777485)
            ·
              refine ⟨3717216539663315645166557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9912577439102175053777485 3717216539663315645166557)
              ·
                refine ⟨1393956202373743366937459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 3717216539663315645166557 1393956202373743366937459)
                ·
                  refine ⟨2090934303560615050406189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1393956202373743366937459 2090934303560615050406189)
                  ·
                    refine ⟨784100363835230643902321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2090934303560615050406189 784100363835230643902321)
                    ·
                      rfl

theorem cell22_2290545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 4, 3, 3, 1, 3].length) (baseStart_2290545 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2290545 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2290545 prefixEnd_2290545 := by exact prefixLift 2290545
  have htrace : WordTrace (prefixWord ++ tailWord_2290545) baseStart_2290545 baseEnd_2290545 := by
    simpa [prefixWord, tailWord_2290545, baseEnd_2290545] using wordTrace_append hprefix tailTrace_2290545
  have hstable : (prefixWord ++ tailWord_2290545).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290545).length < 2 ^ (prefixWord ++ tailWord_2290545).sum := by decide
  have hdescent : baseEnd_2290545 < baseStart_2290545 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290601 : List Nat := [1, 2, 1, 1, 1, 1, 7, 2, 1, 5]
def baseStart_2290601 : Nat := 118140960795 + 2290601 * 2 ^ 59
def prefixEnd_2290601 : Nat := 4983230072969 + 3 ^ 40 * 2290601 * 2
def baseEnd_2290601 : Nat := 784119533779665164502149

theorem tailTrace_2290601 : CollatzResearch.WordTrace tailWord_2290601 prefixEnd_2290601 784119533779665164502149 := by
  unfold tailWord_2290601
  simp only [CollatzResearch.WordTrace]
  refine ⟨83545081974551255350607657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55696721316367503567071771 83545081974551255350607657)
  ·
    refine ⟨62658811480913441512955743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83545081974551255350607657 62658811480913441512955743)
    ·
      refine ⟨93988217221370162269433615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 62658811480913441512955743 93988217221370162269433615)
      ·
        refine ⟨140982325832055243404150423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 93988217221370162269433615 140982325832055243404150423)
        ·
          refine ⟨211473488748082865106225635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 140982325832055243404150423 211473488748082865106225635)
          ·
            refine ⟨317210233122124297659338453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 211473488748082865106225635 317210233122124297659338453)
            ·
              refine ⟨7434614838799788226390745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 317210233122124297659338453 7434614838799788226390745)
              ·
                refine ⟨5575961129099841169793059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7434614838799788226390745 5575961129099841169793059)
                ·
                  refine ⟨8363941693649761754689589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5575961129099841169793059 8363941693649761754689589)
                  ·
                    refine ⟨784119533779665164502149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8363941693649761754689589 784119533779665164502149)
                    ·
                      rfl

theorem cell22_2290601_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 7, 2, 1, 5].length) (baseStart_2290601 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2290601 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2290601 prefixEnd_2290601 := by exact prefixLift 2290601
  have htrace : WordTrace (prefixWord ++ tailWord_2290601) baseStart_2290601 baseEnd_2290601 := by
    simpa [prefixWord, tailWord_2290601, baseEnd_2290601] using wordTrace_append hprefix tailTrace_2290601
  have hstable : (prefixWord ++ tailWord_2290601).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290601).length < 2 ^ (prefixWord ++ tailWord_2290601).sum := by decide
  have hdescent : baseEnd_2290601 < baseStart_2290601 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290601) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290631 : List Nat := [1, 1, 4, 1, 1, 2, 5, 7]
def baseStart_2290631 : Nat := 118140960795 + 2290631 * 2 ^ 59
def prefixEnd_2290631 : Nat := 4983230072969 + 3 ^ 40 * 2290631 * 2
def baseEnd_2290631 : Nat := 87125533710306120694673

theorem tailTrace_2290631 : CollatzResearch.WordTrace tailWord_2290631 prefixEnd_2290631 87125533710306120694673 := by
  unfold tailWord_2290631
  simp only [CollatzResearch.WordTrace]
  refine ⟨83546176164442570474199747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55697450776295046982799831 83546176164442570474199747)
  ·
    refine ⟨125319264246663855711299621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83546176164442570474199747 125319264246663855711299621)
    ·
      refine ⟨23497362046249472945868679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 125319264246663855711299621 23497362046249472945868679)
      ·
        refine ⟨35246043069374209418803019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23497362046249472945868679 35246043069374209418803019)
        ·
          refine ⟨52869064604061314128204529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35246043069374209418803019 52869064604061314128204529)
          ·
            refine ⟨39651798453045985596153397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52869064604061314128204529 39651798453045985596153397)
            ·
              refine ⟨3717356104973061149639381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 39651798453045985596153397 3717356104973061149639381)
              ·
                refine ⟨87125533710306120694673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3717356104973061149639381 87125533710306120694673)
                ·
                  rfl

theorem cell22_2290631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 5, 7].length) (baseStart_2290631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2290631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2290631 prefixEnd_2290631 := by exact prefixLift 2290631
  have htrace : WordTrace (prefixWord ++ tailWord_2290631) baseStart_2290631 baseEnd_2290631 := by
    simpa [prefixWord, tailWord_2290631, baseEnd_2290631] using wordTrace_append hprefix tailTrace_2290631
  have hstable : (prefixWord ++ tailWord_2290631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290631).length < 2 ^ (prefixWord ++ tailWord_2290631).sum := by decide
  have hdescent : baseEnd_2290631 < baseStart_2290631 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290648 : List Nat := [2, 1, 2, 2, 2, 4, 3, 6]
def baseStart_2290648 : Nat := 118140960795 + 2290648 * 2 ^ 59
def prefixEnd_2290648 : Nat := 4983230072969 + 3 ^ 40 * 2290648 * 2
def baseEnd_2290648 : Nat := 87126180315574745397445

theorem tailTrace_2290648 : CollatzResearch.WordTrace tailWord_2290648 prefixEnd_2290648 87126180315574745397445 := by
  unfold tailWord_2290648
  simp only [CollatzResearch.WordTrace]
  refine ⟨41773398102690491188784299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55697864136920654918379065 41773398102690491188784299)
  ·
    refine ⟨62660097154035736783176449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41773398102690491188784299 62660097154035736783176449)
    ·
      refine ⟨46995072865526802587382337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62660097154035736783176449 46995072865526802587382337)
      ·
        refine ⟨35246304649145101940536753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46995072865526802587382337 35246304649145101940536753)
        ·
          refine ⟨26434728486858826455402565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 35246304649145101940536753 26434728486858826455402565)
          ·
            refine ⟨4956511591286029960387981, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26434728486858826455402565 4956511591286029960387981)
            ·
              refine ⟨1858691846732261235145493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4956511591286029960387981 1858691846732261235145493)
              ·
                refine ⟨87126180315574745397445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 1858691846732261235145493 87126180315574745397445)
                ·
                  rfl

theorem cell22_2290648_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 4, 3, 6].length) (baseStart_2290648 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2290648 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2290648 prefixEnd_2290648 := by exact prefixLift 2290648
  have htrace : WordTrace (prefixWord ++ tailWord_2290648) baseStart_2290648 baseEnd_2290648 := by
    simpa [prefixWord, tailWord_2290648, baseEnd_2290648] using wordTrace_append hprefix tailTrace_2290648
  have hstable : (prefixWord ++ tailWord_2290648).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290648).length < 2 ^ (prefixWord ++ tailWord_2290648).sum := by decide
  have hdescent : baseEnd_2290648 < baseStart_2290648 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290648) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290650 : List Nat := [3, 1, 1, 2, 4, 3, 1, 1, 2, 4]
def baseStart_2290650 : Nat := 118140960795 + 2290650 * 2 ^ 59
def prefixEnd_2290650 : Nat := 4983230072969 + 3 ^ 40 * 2290650 * 2
def baseEnd_2290650 : Nat := 784136307481045370026999

theorem tailTrace_2290650 : CollatzResearch.WordTrace tailWord_2290650 prefixEnd_2290650 784136307481045370026999 := by
  unfold tailWord_2290650
  simp only [CollatzResearch.WordTrace]
  refine ⟨20886717287843434179785351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55697912767582491146094269 20886717287843434179785351)
  ·
    refine ⟨31330075931765151269678027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20886717287843434179785351 31330075931765151269678027)
    ·
      refine ⟨46995113897647726904517041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31330075931765151269678027 46995113897647726904517041)
      ·
        refine ⟨35246335423235795178387781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 46995113897647726904517041 35246335423235795178387781)
        ·
          refine ⟨6608687891856711595947709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 35246335423235795178387781 6608687891856711595947709)
          ·
            refine ⟨2478257959446266848480391, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6608687891856711595947709 2478257959446266848480391)
            ·
              refine ⟨3717386939169400272720587, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2478257959446266848480391 3717386939169400272720587)
              ·
                refine ⟨5576080408754100409080881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3717386939169400272720587 5576080408754100409080881)
                ·
                  refine ⟨4182060306565575306810661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5576080408754100409080881 4182060306565575306810661)
                  ·
                    refine ⟨784136307481045370026999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4182060306565575306810661 784136307481045370026999)
                    ·
                      rfl

theorem cell22_2290650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 4].length) (baseStart_2290650 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2290650 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2290650 prefixEnd_2290650 := by exact prefixLift 2290650
  have htrace : WordTrace (prefixWord ++ tailWord_2290650) baseStart_2290650 baseEnd_2290650 := by
    simpa [prefixWord, tailWord_2290650, baseEnd_2290650] using wordTrace_append hprefix tailTrace_2290650
  have hstable : (prefixWord ++ tailWord_2290650).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290650).length < 2 ^ (prefixWord ++ tailWord_2290650).sum := by decide
  have hdescent : baseEnd_2290650 < baseStart_2290650 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290770 : List Nat := [3, 2, 2, 1, 3, 2, 1, 2, 1, 5]
def baseStart_2290770 : Nat := 118140960795 + 2290770 * 2 ^ 59
def prefixEnd_2290770 : Nat := 4983230072969 + 3 ^ 40 * 2290770 * 2
def baseEnd_2290770 : Nat := 784177385933405057026631

theorem tailTrace_2290770 : CollatzResearch.WordTrace tailWord_2290770 prefixEnd_2290770 784177385933405057026631 := by
  unfold tailWord_2290770
  simp only [CollatzResearch.WordTrace]
  refine ⟨20887811477734749303377441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55700830607292664809006509 20887811477734749303377441)
  ·
    refine ⟨15665858608301061977533081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20887811477734749303377441 15665858608301061977533081)
    ·
      refine ⟨11749393956225796483149811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15665858608301061977533081 11749393956225796483149811)
      ·
        refine ⟨17624090934338694724724717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11749393956225796483149811 17624090934338694724724717)
        ·
          refine ⟨6609034100377010521771769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17624090934338694724724717 6609034100377010521771769)
          ·
            refine ⟨4956775575282757891328827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6609034100377010521771769 4956775575282757891328827)
            ·
              refine ⟨7435163362924136836993241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4956775575282757891328827 7435163362924136836993241)
              ·
                refine ⟨5576372522193102627744931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7435163362924136836993241 5576372522193102627744931)
                ·
                  refine ⟨8364558783289653941617397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5576372522193102627744931 8364558783289653941617397)
                  ·
                    refine ⟨784177385933405057026631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8364558783289653941617397 784177385933405057026631)
                    ·
                      rfl

theorem cell22_2290770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 3, 2, 1, 2, 1, 5].length) (baseStart_2290770 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2290770 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2290770 prefixEnd_2290770 := by exact prefixLift 2290770
  have htrace : WordTrace (prefixWord ++ tailWord_2290770) baseStart_2290770 baseEnd_2290770 := by
    simpa [prefixWord, tailWord_2290770, baseEnd_2290770] using wordTrace_append hprefix tailTrace_2290770
  have hstable : (prefixWord ++ tailWord_2290770).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290770).length < 2 ^ (prefixWord ++ tailWord_2290770).sum := by decide
  have hdescent : baseEnd_2290770 < baseStart_2290770 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290813 : List Nat := [1, 4, 1, 1, 3, 1, 1, 2, 2, 6]
def baseStart_2290813 : Nat := 118140960795 + 2290813 * 2 ^ 59
def prefixEnd_2290813 : Nat := 4983230072969 + 3 ^ 40 * 2290813 * 2
def baseEnd_2290813 : Nat := 784192105712167278201499

theorem tailTrace_2290813 : CollatzResearch.WordTrace tailWord_2290813 prefixEnd_2290813 784192105712167278201499 := by
  unfold tailWord_2290813
  simp only [CollatzResearch.WordTrace]
  refine ⟨83552814249783215557325093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55701876166522143704883395 83552814249783215557325093)
  ·
    refine ⟨15666152671834352916998455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83552814249783215557325093 15666152671834352916998455)
    ·
      refine ⟨23499229007751529375497683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15666152671834352916998455 23499229007751529375497683)
      ·
        refine ⟨35248843511627294063246525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23499229007751529375497683 35248843511627294063246525)
        ·
          refine ⟨13218316316860235273717447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35248843511627294063246525 13218316316860235273717447)
          ·
            refine ⟨19827474475290352910576171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13218316316860235273717447 19827474475290352910576171)
            ·
              refine ⟨29741211712935529365864257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19827474475290352910576171 29741211712935529365864257)
              ·
                refine ⟨22305908784701647024398193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29741211712935529365864257 22305908784701647024398193)
                ·
                  refine ⟨16729431588526235268298645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 22305908784701647024398193 16729431588526235268298645)
                  ·
                    refine ⟨784192105712167278201499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16729431588526235268298645 784192105712167278201499)
                    ·
                      rfl

theorem cell22_2290813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 2, 2, 6].length) (baseStart_2290813 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2290813 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2290813 prefixEnd_2290813 := by exact prefixLift 2290813
  have htrace : WordTrace (prefixWord ++ tailWord_2290813) baseStart_2290813 baseEnd_2290813 := by
    simpa [prefixWord, tailWord_2290813, baseEnd_2290813] using wordTrace_append hprefix tailTrace_2290813
  have hstable : (prefixWord ++ tailWord_2290813).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290813).length < 2 ^ (prefixWord ++ tailWord_2290813).sum := by decide
  have hdescent : baseEnd_2290813 < baseStart_2290813 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290920 : List Nat := [2, 1, 4, 1, 2, 1, 1, 2, 4, 4]
def baseStart_2290920 : Nat := 118140960795 + 2290920 * 2 ^ 59
def prefixEnd_2290920 : Nat := 4983230072969 + 3 ^ 40 * 2290920 * 2
def baseEnd_2290920 : Nat := 784228733998854665776171

theorem tailTrace_2290920 : CollatzResearch.WordTrace tailWord_2290920 prefixEnd_2290920 784228733998854665776171 := by
  unfold tailWord_2290920
  simp only [CollatzResearch.WordTrace]
  refine ⟨41778358430197786415735107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55704477906930381887646809 41778358430197786415735107)
  ·
    refine ⟨62667537645296679623602661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41778358430197786415735107 62667537645296679623602661)
    ·
      refine ⟨11750163308493127429425499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62667537645296679623602661 11750163308493127429425499)
      ·
        refine ⟨17625244962739691144138249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11750163308493127429425499 17625244962739691144138249)
        ·
          refine ⟨13218933722054768358103687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 17625244962739691144138249 13218933722054768358103687)
          ·
            refine ⟨19828400583082152537155531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13218933722054768358103687 19828400583082152537155531)
            ·
              refine ⟨29742600874623228805733297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19828400583082152537155531 29742600874623228805733297)
              ·
                refine ⟨22306950655967421604299973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 29742600874623228805733297 22306950655967421604299973)
                ·
                  refine ⟨4182553247993891550806245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 22306950655967421604299973 4182553247993891550806245)
                  ·
                    refine ⟨784228733998854665776171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4182553247993891550806245 784228733998854665776171)
                    ·
                      rfl

theorem cell22_2290920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 2, 4, 4].length) (baseStart_2290920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2290920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2290920 prefixEnd_2290920 := by exact prefixLift 2290920
  have htrace : WordTrace (prefixWord ++ tailWord_2290920) baseStart_2290920 baseEnd_2290920 := by
    simpa [prefixWord, tailWord_2290920, baseEnd_2290920] using wordTrace_append hprefix tailTrace_2290920
  have hstable : (prefixWord ++ tailWord_2290920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290920).length < 2 ^ (prefixWord ++ tailWord_2290920).sum := by decide
  have hdescent : baseEnd_2290920 < baseStart_2290920 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290967 : List Nat := [1, 1, 3, 4, 1, 1, 2, 3, 3, 3]
def baseStart_2290967 : Nat := 118140960795 + 2290967 * 2 ^ 59
def prefixEnd_2290967 : Nat := 4983230072969 + 3 ^ 40 * 2290967 * 2
def baseEnd_2290967 : Nat := 784244823059362209851027

theorem tailTrace_2290967 : CollatzResearch.WordTrace tailWord_2290967 prefixEnd_2290967 784244823059362209851027 := by
  unfold tailWord_2290967
  simp only [CollatzResearch.WordTrace]
  refine ⟨83558431091225299858431155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55705620727483533238954103 83558431091225299858431155)
  ·
    refine ⟨125337646636837949787646733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83558431091225299858431155 125337646636837949787646733)
    ·
      refine ⟨47001617488814231170367525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125337646636837949787646733 47001617488814231170367525)
      ·
        refine ⟨8812803279152668344443911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 47001617488814231170367525 8812803279152668344443911)
        ·
          refine ⟨13219204918729002516665867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8812803279152668344443911 13219204918729002516665867)
          ·
            refine ⟨19828807378093503774998801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13219204918729002516665867 19828807378093503774998801)
            ·
              refine ⟨14871605533570127831249101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19828807378093503774998801 14871605533570127831249101)
              ·
                refine ⟨5576852075088797936718413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14871605533570127831249101 5576852075088797936718413)
                ·
                  refine ⟨2091319528158299226269405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5576852075088797936718413 2091319528158299226269405)
                  ·
                    refine ⟨784244823059362209851027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2091319528158299226269405 784244823059362209851027)
                    ·
                      rfl

theorem cell22_2290967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 3, 3, 3].length) (baseStart_2290967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2290967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2290967 prefixEnd_2290967 := by exact prefixLift 2290967
  have htrace : WordTrace (prefixWord ++ tailWord_2290967) baseStart_2290967 baseEnd_2290967 := by
    simpa [prefixWord, tailWord_2290967, baseEnd_2290967] using wordTrace_append hprefix tailTrace_2290967
  have hstable : (prefixWord ++ tailWord_2290967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290967).length < 2 ^ (prefixWord ++ tailWord_2290967).sum := by decide
  have hdescent : baseEnd_2290967 < baseStart_2290967 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2290984 : List Nat := [2, 1, 5, 1, 2, 2, 1, 2, 3, 3]
def baseStart_2290984 : Nat := 118140960795 + 2290984 * 2 ^ 59
def prefixEnd_2290984 : Nat := 4983230072969 + 3 ^ 40 * 2290984 * 2
def baseEnd_2290984 : Nat := 784250642506779832175975

theorem tailTrace_2290984 : CollatzResearch.WordTrace tailWord_2290984 prefixEnd_2290984 784250642506779832175975 := by
  unfold tailWord_2290984
  simp only [CollatzResearch.WordTrace]
  refine ⟨41779525566081855880900003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55706034088109141174533337 41779525566081855880900003)
  ·
    refine ⟨62669288349122783821350005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 41779525566081855880900003 62669288349122783821350005)
    ·
      refine ⟨5875245782730260983251563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 62669288349122783821350005 5875245782730260983251563)
      ·
        refine ⟨8812868674095391474877345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5875245782730260983251563 8812868674095391474877345)
        ·
          refine ⟨6609651505571543606158009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8812868674095391474877345 6609651505571543606158009)
          ·
            refine ⟨4957238629178657704618507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6609651505571543606158009 4957238629178657704618507)
            ·
              refine ⟨7435857943767986556927761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4957238629178657704618507 7435857943767986556927761)
              ·
                refine ⟨5576893457825989917695821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7435857943767986556927761 5576893457825989917695821)
                ·
                  refine ⟨2091335046684746219135933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 5576893457825989917695821 2091335046684746219135933)
                  ·
                    refine ⟨784250642506779832175975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2091335046684746219135933 784250642506779832175975)
                    ·
                      rfl

theorem cell22_2290984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 1, 2, 3, 3].length) (baseStart_2290984 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2290984 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2290984 prefixEnd_2290984 := by exact prefixLift 2290984
  have htrace : WordTrace (prefixWord ++ tailWord_2290984) baseStart_2290984 baseEnd_2290984 := by
    simpa [prefixWord, tailWord_2290984, baseEnd_2290984] using wordTrace_append hprefix tailTrace_2290984
  have hstable : (prefixWord ++ tailWord_2290984).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2290984).length < 2 ^ (prefixWord ++ tailWord_2290984).sum := by decide
  have hdescent : baseEnd_2290984 < baseStart_2290984 := by decide
  rcases family_descends (prefixWord ++ tailWord_2290984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291042 : List Nat := [3, 3, 2, 1, 1, 1, 1, 4, 6]
def baseStart_2291042 : Nat := 118140960795 + 2291042 * 2 ^ 59
def prefixEnd_2291042 : Nat := 4983230072969 + 3 ^ 40 * 2291042 * 2
def baseEnd_2291042 : Nat := 261423499030695671408599

theorem tailTrace_2291042 : CollatzResearch.WordTrace tailWord_2291042 prefixEnd_2291042 261423499030695671408599 := by
  unfold tailWord_2291042
  simp only [CollatzResearch.WordTrace]
  refine ⟨20890291641488396916852845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55707444377302391778274253 20890291641488396916852845)
  ·
    refine ⟨7833859365558148843819817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20890291641488396916852845 7833859365558148843819817)
    ·
      refine ⟨5875394524168611632864863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7833859365558148843819817 5875394524168611632864863)
      ·
        refine ⟨8813091786252917449297295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5875394524168611632864863 8813091786252917449297295)
        ·
          refine ⟨13219637679379376173945943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8813091786252917449297295 13219637679379376173945943)
          ·
            refine ⟨19829456519069064260918915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 13219637679379376173945943 19829456519069064260918915)
            ·
              refine ⟨29744184778603596391378373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19829456519069064260918915 29744184778603596391378373)
              ·
                refine ⟨5577034645988174323383445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 29744184778603596391378373 5577034645988174323383445)
                ·
                  refine ⟨261423499030695671408599, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5577034645988174323383445 261423499030695671408599)
                  ·
                    rfl

theorem cell22_2291042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 1, 4, 6].length) (baseStart_2291042 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2291042 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2291042 prefixEnd_2291042 := by exact prefixLift 2291042
  have htrace : WordTrace (prefixWord ++ tailWord_2291042) baseStart_2291042 baseEnd_2291042 := by
    simpa [prefixWord, tailWord_2291042, baseEnd_2291042] using wordTrace_append hprefix tailTrace_2291042
  have hstable : (prefixWord ++ tailWord_2291042).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291042).length < 2 ^ (prefixWord ++ tailWord_2291042).sum := by decide
  have hdescent : baseEnd_2291042 < baseStart_2291042 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291044 : List Nat := [2, 3, 1, 1, 3, 3, 2, 2, 1, 4]
def baseStart_2291044 : Nat := 118140960795 + 2291044 * 2 ^ 59
def prefixEnd_2291044 : Nat := 4983230072969 + 3 ^ 40 * 2291044 * 2
def baseEnd_2291044 : Nat := 784271181732959675675791

theorem tailTrace_2291044 : CollatzResearch.WordTrace tailWord_2291044 prefixEnd_2291044 784271181732959675675791 := by
  unfold tailWord_2291044
  simp only [CollatzResearch.WordTrace]
  refine ⟨41780619755973171004492093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55707493007964228005989457 41780619755973171004492093)
  ·
    refine ⟨15667732408489939126684535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41780619755973171004492093 15667732408489939126684535)
    ·
      refine ⟨23501598612734908690026803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15667732408489939126684535 23501598612734908690026803)
      ·
        refine ⟨35252397919102363035040205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 23501598612734908690026803 35252397919102363035040205)
        ·
          refine ⟨13219649219663386138140077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 35252397919102363035040205 13219649219663386138140077)
          ·
            refine ⟨4957368457373769801802529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 13219649219663386138140077 4957368457373769801802529)
            ·
              refine ⟨3718026343030327351351897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4957368457373769801802529 3718026343030327351351897)
              ·
                refine ⟨2788519757272745513513923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3718026343030327351351897 2788519757272745513513923)
                ·
                  refine ⟨4182779635909118270270885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2788519757272745513513923 4182779635909118270270885)
                  ·
                    refine ⟨784271181732959675675791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4182779635909118270270885 784271181732959675675791)
                    ·
                      rfl

theorem cell22_2291044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 2, 2, 1, 4].length) (baseStart_2291044 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2291044 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2291044 prefixEnd_2291044 := by exact prefixLift 2291044
  have htrace : WordTrace (prefixWord ++ tailWord_2291044) baseStart_2291044 baseEnd_2291044 := by
    simpa [prefixWord, tailWord_2291044, baseEnd_2291044] using wordTrace_append hprefix tailTrace_2291044
  have hstable : (prefixWord ++ tailWord_2291044).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291044).length < 2 ^ (prefixWord ++ tailWord_2291044).sum := by decide
  have hdescent : baseEnd_2291044 < baseStart_2291044 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291055 : List Nat := [1, 1, 2, 1, 3, 1, 3, 3, 1, 6]
def baseStart_2291055 : Nat := 118140960795 + 2291055 * 2 ^ 59
def prefixEnd_2291055 : Nat := 4983230072969 + 3 ^ 40 * 2291055 * 2
def baseEnd_2291055 : Nat := 784274947257759313650757

theorem tailTrace_2291055 : CollatzResearch.WordTrace tailWord_2291055 prefixEnd_2291055 784274947257759313650757 := by
  unfold tailWord_2291055
  simp only [CollatzResearch.WordTrace]
  refine ⟨83561640714906490887634619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55707760476604327258423079 83561640714906490887634619)
  ·
    refine ⟨125342461072359736331451929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83561640714906490887634619 125342461072359736331451929)
    ·
      refine ⟨94006845804269802248588947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 125342461072359736331451929 94006845804269802248588947)
      ·
        refine ⟨141010268706404703372883421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 94006845804269802248588947 141010268706404703372883421)
        ·
          refine ⟨52878850764901763764831283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 141010268706404703372883421 52878850764901763764831283)
          ·
            refine ⟨79318276147352645647246925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52878850764901763764831283 79318276147352645647246925)
            ·
              refine ⟨29744353555257242117717597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79318276147352645647246925 29744353555257242117717597)
              ·
                refine ⟨11154132583221465794144099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 29744353555257242117717597 11154132583221465794144099)
                ·
                  refine ⟨16731198874832198691216149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 11154132583221465794144099 16731198874832198691216149)
                  ·
                    refine ⟨784274947257759313650757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16731198874832198691216149 784274947257759313650757)
                    ·
                      rfl

theorem cell22_2291055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 3, 3, 1, 6].length) (baseStart_2291055 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2291055 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2291055 prefixEnd_2291055 := by exact prefixLift 2291055
  have htrace : WordTrace (prefixWord ++ tailWord_2291055) baseStart_2291055 baseEnd_2291055 := by
    simpa [prefixWord, tailWord_2291055, baseEnd_2291055] using wordTrace_append hprefix tailTrace_2291055
  have hstable : (prefixWord ++ tailWord_2291055).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291055).length < 2 ^ (prefixWord ++ tailWord_2291055).sum := by decide
  have hdescent : baseEnd_2291055 < baseStart_2291055 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291057 : List Nat := [1, 2, 2, 2, 1, 2, 3, 2, 4, 3]
def baseStart_2291057 : Nat := 118140960795 + 2291057 * 2 ^ 59
def prefixEnd_2291057 : Nat := 4983230072969 + 3 ^ 40 * 2291057 * 2
def baseEnd_2291057 : Nat := 784275631898631975100751

theorem tailTrace_2291057 : CollatzResearch.WordTrace tailWord_2291057 prefixEnd_2291057 784275631898631975100751 := by
  unfold tailWord_2291057
  simp only [CollatzResearch.WordTrace]
  refine ⟨83561713660899245229207425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55707809107266163486138283 83561713660899245229207425)
  ·
    refine ⟨62671285245674433921905569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83561713660899245229207425 62671285245674433921905569)
    ·
      refine ⟨47003463934255825441429177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 62671285245674433921905569 47003463934255825441429177)
      ·
        refine ⟨35252597950691869081071883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 47003463934255825441429177 35252597950691869081071883)
        ·
          refine ⟨52878896926037803621607825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 35252597950691869081071883 52878896926037803621607825)
          ·
            refine ⟨39659172694528352716205869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 52878896926037803621607825 39659172694528352716205869)
            ·
              refine ⟨14872189760448132268577201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 39659172694528352716205869 14872189760448132268577201)
              ·
                refine ⟨11154142320336099201432901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14872189760448132268577201 11154142320336099201432901)
                ·
                  refine ⟨2091401685063018600268669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 11154142320336099201432901 2091401685063018600268669)
                  ·
                    refine ⟨784275631898631975100751, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2091401685063018600268669 784275631898631975100751)
                    ·
                      rfl

theorem cell22_2291057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 2, 4, 3].length) (baseStart_2291057 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2291057 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2291057 prefixEnd_2291057 := by exact prefixLift 2291057
  have htrace : WordTrace (prefixWord ++ tailWord_2291057) baseStart_2291057 baseEnd_2291057 := by
    simpa [prefixWord, tailWord_2291057, baseEnd_2291057] using wordTrace_append hprefix tailTrace_2291057
  have hstable : (prefixWord ++ tailWord_2291057).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291057).length < 2 ^ (prefixWord ++ tailWord_2291057).sum := by decide
  have hdescent : baseEnd_2291057 < baseStart_2291057 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291076 : List Nat := [2, 3, 2, 1, 1, 4, 3, 2, 4]
def baseStart_2291076 : Nat := 118140960795 + 2291076 * 2 ^ 59
def prefixEnd_2291076 : Nat := 4983230072969 + 3 ^ 40 * 2291076 * 2
def baseEnd_2291076 : Nat := 261427378662307419625231

theorem tailTrace_2291076 : CollatzResearch.WordTrace tailWord_2291076 prefixEnd_2291076 261427378662307419625231 := by
  unfold tailWord_2291076
  simp only [CollatzResearch.WordTrace]
  refine ⟨41781203323915205737074541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55708271098553607649432721 41781203323915205737074541)
  ·
    refine ⟨15667951246468202151402953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 41781203323915205737074541 15667951246468202151402953)
    ·
      refine ⟨11750963434851151613552215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15667951246468202151402953 11750963434851151613552215)
      ·
        refine ⟨17626445152276727420328323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11750963434851151613552215 17626445152276727420328323)
        ·
          refine ⟨26439667728415091130492485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17626445152276727420328323 26439667728415091130492485)
          ·
            refine ⟨4957437699077829586967341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 26439667728415091130492485 4957437699077829586967341)
            ·
              refine ⟨1859039137154186095112753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4957437699077829586967341 1859039137154186095112753)
              ·
                refine ⟨1394279352865639571334565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1859039137154186095112753 1394279352865639571334565)
                ·
                  refine ⟨261427378662307419625231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1394279352865639571334565 261427378662307419625231)
                  ·
                    rfl

theorem cell22_2291076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2, 4].length) (baseStart_2291076 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2291076 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2291076 prefixEnd_2291076 := by exact prefixLift 2291076
  have htrace : WordTrace (prefixWord ++ tailWord_2291076) baseStart_2291076 baseEnd_2291076 := by
    simpa [prefixWord, tailWord_2291076, baseEnd_2291076] using wordTrace_append hprefix tailTrace_2291076
  have hstable : (prefixWord ++ tailWord_2291076).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291076).length < 2 ^ (prefixWord ++ tailWord_2291076).sum := by decide
  have hdescent : baseEnd_2291076 < baseStart_2291076 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291194 : List Nat := [3, 1, 1, 1, 1, 2, 3, 6, 4]
def baseStart_2291194 : Nat := 118140960795 + 2291194 * 2 ^ 59
def prefixEnd_2291194 : Nat := 4983230072969 + 3 ^ 40 * 2291194 * 2
def baseEnd_2291194 : Nat := 261440843266136428141777

theorem tailTrace_2291194 : CollatzResearch.WordTrace tailWord_2291194 prefixEnd_2291194 261440843266136428141777 := by
  unfold tailWord_2291194
  simp only [CollatzResearch.WordTrace]
  refine ⟨20891677615350729406736159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55711140307601945084629757 20891677615350729406736159)
  ·
    refine ⟨31337516423026094110104239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20891677615350729406736159 31337516423026094110104239)
    ·
      refine ⟨47006274634539141165156359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31337516423026094110104239 47006274634539141165156359)
      ·
        refine ⟨70509411951808711747734539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47006274634539141165156359 70509411951808711747734539)
        ·
          refine ⟨105764117927713067621601809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 70509411951808711747734539 105764117927713067621601809)
          ·
            refine ⟨79323088445784800716201357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 105764117927713067621601809 79323088445784800716201357)
            ·
              refine ⟨29746158167169300268575509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 79323088445784800716201357 29746158167169300268575509)
              ·
                refine ⟨1394351164086060950089477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 29746158167169300268575509 1394351164086060950089477)
                ·
                  refine ⟨261440843266136428141777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1394351164086060950089477 261440843266136428141777)
                  ·
                    rfl

theorem cell22_2291194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 2, 3, 6, 4].length) (baseStart_2291194 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2291194 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2291194 prefixEnd_2291194 := by exact prefixLift 2291194
  have htrace : WordTrace (prefixWord ++ tailWord_2291194) baseStart_2291194 baseEnd_2291194 := by
    simpa [prefixWord, tailWord_2291194, baseEnd_2291194] using wordTrace_append hprefix tailTrace_2291194
  have hstable : (prefixWord ++ tailWord_2291194).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291194).length < 2 ^ (prefixWord ++ tailWord_2291194).sum := by decide
  have hdescent : baseEnd_2291194 < baseStart_2291194 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291260 : List Nat := [2, 2, 2, 2, 4, 2, 2, 1, 2, 3]
def baseStart_2291260 : Nat := 118140960795 + 2291260 * 2 ^ 59
def prefixEnd_2291260 : Nat := 4983230072969 + 3 ^ 40 * 2291260 * 2
def baseEnd_2291260 : Nat := 784345122947207112275129

theorem tailTrace_2291260 : CollatzResearch.WordTrace tailWord_2291260 prefixEnd_2291260 784345122947207112275129 := by
  unfold tailWord_2291260
  simp only [CollatzResearch.WordTrace]
  refine ⟨41784558839581905449423617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 55712745119442540599231489 41784558839581905449423617)
  ·
    refine ⟨31338419129686429087067713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 41784558839581905449423617 31338419129686429087067713)
    ·
      refine ⟨23503814347264821815300785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 31338419129686429087067713 23503814347264821815300785)
      ·
        refine ⟨17627860760448616361475589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23503814347264821815300785 17627860760448616361475589)
        ·
          refine ⟨3305223892584115567776673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 17627860760448616361475589 3305223892584115567776673)
          ·
            refine ⟨2478917919438086675832505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3305223892584115567776673 2478917919438086675832505)
            ·
              refine ⟨1859188439578565006874379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2478917919438086675832505 1859188439578565006874379)
              ·
                refine ⟨2788782659367847510311569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1859188439578565006874379 2788782659367847510311569)
                ·
                  refine ⟨2091586994525885632733677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2788782659367847510311569 2091586994525885632733677)
                  ·
                    refine ⟨784345122947207112275129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2091586994525885632733677 784345122947207112275129)
                    ·
                      rfl

theorem cell22_2291260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 4, 2, 2, 1, 2, 3].length) (baseStart_2291260 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2291260 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2291260 prefixEnd_2291260 := by exact prefixLift 2291260
  have htrace : WordTrace (prefixWord ++ tailWord_2291260) baseStart_2291260 baseEnd_2291260 := by
    simpa [prefixWord, tailWord_2291260, baseEnd_2291260] using wordTrace_append hprefix tailTrace_2291260
  have hstable : (prefixWord ++ tailWord_2291260).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291260).length < 2 ^ (prefixWord ++ tailWord_2291260).sum := by decide
  have hdescent : baseEnd_2291260 < baseStart_2291260 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291301 : List Nat := [1, 3, 1, 3, 3, 2, 2, 2, 5]
def baseStart_2291301 : Nat := 118140960795 + 2291301 * 2 ^ 59
def prefixEnd_2291301 : Nat := 4983230072969 + 3 ^ 40 * 2291301 * 2
def baseEnd_2291301 : Nat := 261453052695032224000001

theorem tailTrace_2291301 : CollatzResearch.WordTrace tailWord_2291301 prefixEnd_2291301 261453052695032224000001 := by
  unfold tailWord_2291301
  simp only [CollatzResearch.WordTrace]
  refine ⟨83570613072015274901089757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55713742048010183267393171 83570613072015274901089757)
  ·
    refine ⟨31338979902005728087908659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 83570613072015274901089757 31338979902005728087908659)
    ·
      refine ⟨47008469853008592131862989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 31338979902005728087908659 47008469853008592131862989)
      ·
        refine ⟨17628176194878222049448621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 47008469853008592131862989 17628176194878222049448621)
        ·
          refine ⟨6610566073079333268543233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 17628176194878222049448621 6610566073079333268543233)
          ·
            refine ⟨4957924554809499951407425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6610566073079333268543233 4957924554809499951407425)
            ·
              refine ⟨3718443416107124963555569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4957924554809499951407425 3718443416107124963555569)
              ·
                refine ⟨2788832562080343722666677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3718443416107124963555569 2788832562080343722666677)
                ·
                  refine ⟨261453052695032224000001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2788832562080343722666677 261453052695032224000001)
                  ·
                    rfl

theorem cell22_2291301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 5].length) (baseStart_2291301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2291301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2291301 prefixEnd_2291301 := by exact prefixLift 2291301
  have htrace : WordTrace (prefixWord ++ tailWord_2291301) baseStart_2291301 baseEnd_2291301 := by
    simpa [prefixWord, tailWord_2291301, baseEnd_2291301] using wordTrace_append hprefix tailTrace_2291301
  have hstable : (prefixWord ++ tailWord_2291301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291301).length < 2 ^ (prefixWord ++ tailWord_2291301).sum := by decide
  have hdescent : baseEnd_2291301 < baseStart_2291301 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291329 : List Nat := [1, 2, 4, 2, 1, 2, 1, 1, 8]
def baseStart_2291329 : Nat := 118140960795 + 2291329 * 2 ^ 59
def prefixEnd_2291329 : Nat := 4983230072969 + 3 ^ 40 * 2291329 * 2
def baseEnd_2291329 : Nat := 261456247685771310766639

theorem tailTrace_2291329 : CollatzResearch.WordTrace tailWord_2291329 prefixEnd_2291329 261456247685771310766639 := by
  unfold tailWord_2291329
  simp only [CollatzResearch.WordTrace]
  refine ⟨83571634315913835683109041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55714422877275890455406027 83571634315913835683109041)
  ·
    refine ⟨62678725736935376762331781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 83571634315913835683109041 62678725736935376762331781)
    ·
      refine ⟨11752261075675383142937209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 62678725736935376762331781 11752261075675383142937209)
      ·
        refine ⟨8814195806756537357202907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11752261075675383142937209 8814195806756537357202907)
        ·
          refine ⟨13221293710134806035804361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8814195806756537357202907 13221293710134806035804361)
          ·
            refine ⟨9915970282601104526853271, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 13221293710134806035804361 9915970282601104526853271)
            ·
              refine ⟨14873955423901656790279907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9915970282601104526853271 14873955423901656790279907)
              ·
                refine ⟨22310933135852485185419861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14873955423901656790279907 22310933135852485185419861)
                ·
                  refine ⟨261456247685771310766639, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 22310933135852485185419861 261456247685771310766639)
                  ·
                    rfl

theorem cell22_2291329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 1, 2, 1, 1, 8].length) (baseStart_2291329 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2291329 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2291329 prefixEnd_2291329 := by exact prefixLift 2291329
  have htrace : WordTrace (prefixWord ++ tailWord_2291329) baseStart_2291329 baseEnd_2291329 := by
    simpa [prefixWord, tailWord_2291329, baseEnd_2291329] using wordTrace_append hprefix tailTrace_2291329
  have hstable : (prefixWord ++ tailWord_2291329).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291329).length < 2 ^ (prefixWord ++ tailWord_2291329).sum := by decide
  have hdescent : baseEnd_2291329 < baseStart_2291329 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291389 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 2, 7]
def baseStart_2291389 : Nat := 118140960795 + 2291389 * 2 ^ 59
def prefixEnd_2291389 : Nat := 4983230072969 + 3 ^ 40 * 2291389 * 2
def baseEnd_2291389 : Nat := 784389282283493775799733

theorem tailTrace_2291389 : CollatzResearch.WordTrace tailWord_2291389 prefixEnd_2291389 784389282283493775799733 := by
  unfold tailWord_2291389
  simp only [CollatzResearch.WordTrace]
  refine ⟨83573822695696465930293221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55715881797130977286862147 83573822695696465930293221)
  ·
    refine ⟨15670091755443087361929979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83573822695696465930293221 15670091755443087361929979)
    ·
      refine ⟨23505137633164631042894969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15670091755443087361929979 23505137633164631042894969)
      ·
        refine ⟨17628853224873473282171227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 23505137633164631042894969 17628853224873473282171227)
        ·
          refine ⟨26443279837310209923256841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 17628853224873473282171227 26443279837310209923256841)
          ·
            refine ⟨19832459877982657442442631, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 26443279837310209923256841 19832459877982657442442631)
            ·
              refine ⟨29748689816973986163663947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19832459877982657442442631 29748689816973986163663947)
              ·
                refine ⟨44623034725460979245495921, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 29748689816973986163663947 44623034725460979245495921)
                ·
                  refine ⟨33467276044095734434121941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 44623034725460979245495921 33467276044095734434121941)
                  ·
                    refine ⟨784389282283493775799733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 33467276044095734434121941 784389282283493775799733)
                    ·
                      rfl

theorem cell22_2291389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 7].length) (baseStart_2291389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2291389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2291389 prefixEnd_2291389 := by exact prefixLift 2291389
  have htrace : WordTrace (prefixWord ++ tailWord_2291389) baseStart_2291389 baseEnd_2291389 := by
    simpa [prefixWord, tailWord_2291389, baseEnd_2291389] using wordTrace_append hprefix tailTrace_2291389
  have hstable : (prefixWord ++ tailWord_2291389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291389).length < 2 ^ (prefixWord ++ tailWord_2291389).sum := by decide
  have hdescent : baseEnd_2291389 < baseStart_2291389 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291414 : List Nat := [5, 2, 1, 3, 1, 1, 3, 2, 4]
def baseStart_2291414 : Nat := 118140960795 + 2291414 * 2 ^ 59
def prefixEnd_2291414 : Nat := 4983230072969 + 3 ^ 40 * 2291414 * 2
def baseEnd_2291414 : Nat := 261465946764800681308219

theorem tailTrace_2291414 : CollatzResearch.WordTrace tailWord_2291414 prefixEnd_2291414 261465946764800681308219 := by
  unfold tailWord_2291414
  simp only [CollatzResearch.WordTrace]
  refine ⟨5223420907537868449997081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 55716489680403930133302197 5223420907537868449997081)
  ·
    refine ⟨3917565680653401337497811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5223420907537868449997081 3917565680653401337497811)
    ·
      refine ⟨5876348520980102006246717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3917565680653401337497811 5876348520980102006246717)
      ·
        refine ⟨2203630695367538252342519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 5876348520980102006246717 2203630695367538252342519)
        ·
          refine ⟨3305446043051307378513779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2203630695367538252342519 3305446043051307378513779)
          ·
            refine ⟨4958169064576961067770669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3305446043051307378513779 4958169064576961067770669)
            ·
              refine ⟨1859313399216360400414001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 4958169064576961067770669 1859313399216360400414001)
              ·
                refine ⟨1394485049412270300310501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1859313399216360400414001 1394485049412270300310501)
                ·
                  refine ⟨261465946764800681308219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1394485049412270300310501 261465946764800681308219)
                  ·
                    rfl

theorem cell22_2291414_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_2291414 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2291414 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2291414 prefixEnd_2291414 := by exact prefixLift 2291414
  have htrace : WordTrace (prefixWord ++ tailWord_2291414) baseStart_2291414 baseEnd_2291414 := by
    simpa [prefixWord, tailWord_2291414, baseEnd_2291414] using wordTrace_append hprefix tailTrace_2291414
  have hstable : (prefixWord ++ tailWord_2291414).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291414).length < 2 ^ (prefixWord ++ tailWord_2291414).sum := by decide
  have hdescent : baseEnd_2291414 < baseStart_2291414 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291414) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291474 : List Nat := [3, 2, 4, 1, 1, 1, 4, 2, 1, 3]
def baseStart_2291474 : Nat := 118140960795 + 2291474 * 2 ^ 59
def prefixEnd_2291474 : Nat := 4983230072969 + 3 ^ 40 * 2291474 * 2
def baseEnd_2291474 : Nat := 784418379520581887424473

theorem tailTrace_2291474 : CollatzResearch.WordTrace tailWord_2291474 prefixEnd_2291474 784418379520581887424473 := by
  unfold tailWord_2291474
  simp only [CollatzResearch.WordTrace]
  refine ⟨20894230725097131361784369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 55717948600259016964758317 20894230725097131361784369)
  ·
    refine ⟨15670673043822848521338277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20894230725097131361784369 15670673043822848521338277)
    ·
      refine ⟨2938251195716784097750927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15670673043822848521338277 2938251195716784097750927)
      ·
        refine ⟨4407376793575176146626391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2938251195716784097750927 4407376793575176146626391)
        ·
          refine ⟨6611065190362764219939587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4407376793575176146626391 6611065190362764219939587)
          ·
            refine ⟨9916597785544146329909381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6611065190362764219939587 9916597785544146329909381)
            ·
              refine ⟨1859362084789527436858009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 9916597785544146329909381 1859362084789527436858009)
              ·
                refine ⟨1394521563592145577643507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1859362084789527436858009 1394521563592145577643507)
                ·
                  refine ⟨2091782345388218366465261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1394521563592145577643507 2091782345388218366465261)
                  ·
                    refine ⟨784418379520581887424473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2091782345388218366465261 784418379520581887424473)
                    ·
                      rfl

theorem cell22_2291474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_2291474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2291474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2291474 prefixEnd_2291474 := by exact prefixLift 2291474
  have htrace : WordTrace (prefixWord ++ tailWord_2291474) baseStart_2291474 baseEnd_2291474 := by
    simpa [prefixWord, tailWord_2291474, baseEnd_2291474] using wordTrace_append hprefix tailTrace_2291474
  have hstable : (prefixWord ++ tailWord_2291474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291474).length < 2 ^ (prefixWord ++ tailWord_2291474).sum := by decide
  have hdescent : baseEnd_2291474 < baseStart_2291474 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291511 : List Nat := [1, 1, 3, 1, 2, 1, 2, 5, 2, 4]
def baseStart_2291511 : Nat := 118140960795 + 2291511 * 2 ^ 59
def prefixEnd_2291511 : Nat := 4983230072969 + 3 ^ 40 * 2291511 * 2
def baseEnd_2291511 : Nat := 784431045376726124249359

theorem tailTrace_2291511 : CollatzResearch.WordTrace tailWord_2291511 prefixEnd_2291511 784431045376726124249359 := by
  unfold tailWord_2291511
  simp only [CollatzResearch.WordTrace]
  refine ⟨83578272401254480766234387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55718848267502987177489591 83578272401254480766234387)
  ·
    refine ⟨125367408601881721149351581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 83578272401254480766234387 125367408601881721149351581)
    ·
      refine ⟨47012778225705645431006843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 125367408601881721149351581 47012778225705645431006843)
      ·
        refine ⟨70519167338558468146510265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 47012778225705645431006843 70519167338558468146510265)
        ·
          refine ⟨52889375503918851109882699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 70519167338558468146510265 52889375503918851109882699)
          ·
            refine ⟨79334063255878276664824049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 52889375503918851109882699 79334063255878276664824049)
            ·
              refine ⟨59500547441908707498618037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 79334063255878276664824049 59500547441908707498618037)
              ·
                refine ⟨5578176322678941327995441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 59500547441908707498618037 5578176322678941327995441)
                ·
                  refine ⟨4183632242009205995996581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5578176322678941327995441 4183632242009205995996581)
                  ·
                    refine ⟨784431045376726124249359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4183632242009205995996581 784431045376726124249359)
                    ·
                      rfl

theorem cell22_2291511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_2291511 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2291511 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2291511 prefixEnd_2291511 := by exact prefixLift 2291511
  have htrace : WordTrace (prefixWord ++ tailWord_2291511) baseStart_2291511 baseEnd_2291511 := by
    simpa [prefixWord, tailWord_2291511, baseEnd_2291511] using wordTrace_append hprefix tailTrace_2291511
  have hstable : (prefixWord ++ tailWord_2291511).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291511).length < 2 ^ (prefixWord ++ tailWord_2291511).sum := by decide
  have hdescent : baseEnd_2291511 < baseStart_2291511 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_2291517 : List Nat := [1, 4, 1, 4, 1, 3, 2, 1, 1, 4]
def baseStart_2291517 : Nat := 118140960795 + 2291517 * 2 ^ 59
def prefixEnd_2291517 : Nat := 4983230072969 + 3 ^ 40 * 2291517 * 2
def baseEnd_2291517 : Nat := 784433099299344108599341

theorem tailTrace_2291517 : CollatzResearch.WordTrace tailWord_2291517 prefixEnd_2291517 784433099299344108599341 := by
  unfold tailWord_2291517
  simp only [CollatzResearch.WordTrace]
  refine ⟨83578491239232743790952805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 55718994159488495860635203 83578491239232743790952805)
  ·
    refine ⟨15670967107356139460803651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 83578491239232743790952805 15670967107356139460803651)
    ·
      refine ⟨23506450661034209191205477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15670967107356139460803651 23506450661034209191205477)
      ·
        refine ⟨4407459498943914223351027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 23506450661034209191205477 4407459498943914223351027)
        ·
          refine ⟨6611189248415871335026541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4407459498943914223351027 6611189248415871335026541)
          ·
            refine ⟨2479195968155951750634953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 6611189248415871335026541 2479195968155951750634953)
            ·
              refine ⟨1859396976116963812976215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2479195968155951750634953 1859396976116963812976215)
              ·
                refine ⟨2789095464175445719464323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1859396976116963812976215 2789095464175445719464323)
                ·
                  refine ⟨4183643196263168579196485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2789095464175445719464323 4183643196263168579196485)
                  ·
                    refine ⟨784433099299344108599341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4183643196263168579196485 784433099299344108599341)
                    ·
                      rfl

theorem cell22_2291517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 3, 2, 1, 1, 4].length) (baseStart_2291517 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_2291517 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_2291517 prefixEnd_2291517 := by exact prefixLift 2291517
  have htrace : WordTrace (prefixWord ++ tailWord_2291517) baseStart_2291517 baseEnd_2291517 := by
    simpa [prefixWord, tailWord_2291517, baseEnd_2291517] using wordTrace_append hprefix tailTrace_2291517
  have hstable : (prefixWord ++ tailWord_2291517).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_2291517).length < 2 ^ (prefixWord ++ tailWord_2291517).sum := by decide
  have hdescent : baseEnd_2291517 < baseStart_2291517 := by decide
  rcases family_descends (prefixWord ++ tailWord_2291517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
